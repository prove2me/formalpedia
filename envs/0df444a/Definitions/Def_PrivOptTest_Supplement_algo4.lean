-- Prove2me | Definitions.Def_PrivOptTest_Supplement_algo4
-- name    : PrivOptTest_Supplement_algo4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:34:56.114203+00:00
-- url     : https://prove2.me/theorems/3841563f-ed03-4728-abf4-757053eb2c51
-- title:
--   Algorithm 4 $\mathcal A_{\mathrm{max-hs}}$ (random-sign ray sketches) as a two-party protocol
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^d\setminus\{0\}$ be finite. For $x\ne0$ let $R(x)=\{\lambda x:\lambda>0\}$ be the ray through $x$ and $\mathcal R=\{R(x):x\in\mathcal X\}$ the public set of rays meeting $\mathcal X$. Fix $k\in\mathbb N$ and $\varepsilon>0$, and put $\tau=\sqrt n/2$.
--
--   1. Public coins: independent uniform signs $\sigma_{j,R}\in\{\pm1\}$ for $j\in[k]$, $R\in\mathcal R$.
--   2. Alice computes $a_R=|\{i\in[n]:X_i\in R\}|$ and releases $Z_{A,j}=\sum_{R\in\mathcal R}\sigma_{j,R}a_R+\mathrm{Lap}(2k/\varepsilon)$ for $j\in[k]$, with independent noise from her private coins.
--   3. Bob does the same with his counts $b_R$ and releases $Z_{B,j}$.
--   4. The output is Match if $\max_{j\in[k]}|Z_{A,j}-Z_{B,j}|>\tau$ and Far otherwise.
--
--   This is the non-interactive tester of Theorem 4.9, with resolution $t=n$.
--
--   **Formalization Note** A ray is recorded by the points of $\mathcal X$ on it; for $\mathcal X\subseteq\mathbb R^d\setminus\{0\}$ these classes partition $\mathcal X$. Laplace laws are the base mission's $\mathrm{Lap}(b)$ with density $(2b)^{-1}e^{-|z|/b}$.
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Algorithm 4, p.33; rays, p.32

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivOptTest_Protocol

open MeasureTheory

namespace PrivOptTest

namespace Supplement

variable {d : ℕ}

open Classical in
/-- The points of `X` on the ray `R(x) = {λx : λ > 0}` through `x` (p.32). For `x ≠ 0` and `y ≠ 0`,
`SameRay ℝ x y` holds exactly when `y = λx` for some `λ > 0`. -/
noncomputable def rayClass (X : Finset (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    Finset (EuclideanSpace ℝ (Fin d)) :=
  X.filter fun y => SameRay ℝ x y

/-- The public set `ℛ = {R(x) : x ∈ X}` of rays meeting the domain (p.32), each ray recorded by the
points of `X` it contains. -/
noncomputable def rays (X : Finset (EuclideanSpace ℝ (Fin d))) :
    Finset (Finset (EuclideanSpace ℝ (Fin d))) :=
  X.image (rayClass X)

open Classical in
/-- The count `a_R = |{i ∈ [n] : X_i ∈ R}|` of a party's records on the ray `R` (line 3 of Algorithm 4). -/
noncomputable def rayCount {X : Finset (EuclideanSpace ℝ (Fin d))} {n : ℕ} (S : Fin n → ↥X)
    (R : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  (Finset.univ.filter fun i => (S i : EuclideanSpace ℝ (Fin d)) ∈ R).card

/-- The public coins of Algorithm 4: independent uniform signs `σ_{j,R} ∈ {±1}` for `j ∈ [k]` and
`R ∈ ℛ` (line 2), with `true` for `+1`. -/
abbrev Algo4Signs (X : Finset (EuclideanSpace ℝ (Fin d))) (k : ℕ) : Type :=
  Fin k → ↥(rays X) → Bool

/-- A party's release (lines 3–4): `Z_j = Σ_{R ∈ ℛ} σ_{j,R} a_R + ν_j` for `j ∈ [k]`, where `ν` are the
party's Laplace noises. -/
noncomputable def sketch {X : Finset (EuclideanSpace ℝ (Fin d))} {n k : ℕ} (S : Fin n → ↥X)
    (σ : Algo4Signs X k) (ν : Fin k → ℝ) : Fin k → ℝ :=
  fun j => (∑ R : ↥(rays X), (if σ j R then (1 : ℝ) else -1) * (rayCount S R.1 : ℝ)) + ν j

open Classical in
/-- The decision of lines 5–8: Match if `max_{j ∈ [k]} |Z_{A,j} − Z_{B,j}| > τ` with `τ = √n/2`, Far
otherwise. -/
noncomputable def algo4Decide (n k : ℕ) (zA zB : Fin k → ℝ) : Outcome :=
  if ∃ j, Real.sqrt n / 2 < |zA j - zB j| then Outcome.matched else Outcome.far

/-- **Algorithm 4, `A_max−hs` (Testing at Resolution `t = n` for Half Spaces), p.33**, with the constant
`k` of line 1 as a parameter. The public coins are the signs `σ_{j,R}`. Alice releases her sketch with
i.i.d. `Lap(2k/ε)` noise from her private coins (message 0), Bob releases his (message 1, which does
not look at Alice's), and the run stops before round 2 with the decision of lines 5–8.

**Formalization Note.** The rays are recorded by the domain points on them (`rays`); for a domain
`X ⊆ ℝ^d \ {0}`, as in Theorem 4.9, these classes partition `X`. Laplace laws are the base mission's
`PrivLearn.Generic.laplace`. -/
noncomputable def algo4 (X : Finset (EuclideanSpace ℝ (Fin d))) (n k : ℕ) (ε : ℝ) :
    Protocol (Fin n → ↥X) Outcome where
  ΩA := Fin k → ℝ
  ΩB := Fin k → ℝ
  ΩP := Algo4Signs X k
  Msg := Fin k → ℝ
  μA := Measure.pi fun _ => PrivLearn.Generic.laplace (2 * k / ε)
  μB := Measure.pi fun _ => PrivLearn.Generic.laplace (2 * k / ε)
  μP := ProbabilityTheory.uniformOn Set.univ
  nextA _ S ν σ _ := sketch S σ ν
  nextB _ S ν σ _ := sketch S σ ν
  stop r _ h := if hr : 2 ≤ r then Sum.inl (algo4Decide n k (h ⟨0, by omega⟩) (h ⟨1, by omega⟩))
    else Sum.inr ()

end Supplement

end PrivOptTest


