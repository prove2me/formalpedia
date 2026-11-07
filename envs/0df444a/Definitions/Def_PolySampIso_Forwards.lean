-- Prove2me | Definitions.Def_PolySampIso_Forwards
-- name    : PolySampIso_Forwards
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:08.152194+00:00
-- url     : https://prove2.me/theorems/594d7479-90bf-4cd7-9b0d-e8080dcbdde0
-- title:
--   Lemma 2's dual measure and Algorithm 2 (Forwards): the exponential forwards step
-- statement:
--   For $i\in[m]$ let $\rho_i$ be the pushforward of $e^{-tb_i}\mathbb 1_{t>0}\,dt$ under $t\mapsto ta_i$ (the density $e^{-\varphi_i}$ on the ray $\{ta_i:t>0\}$), and let $\rho=\rho_1*\cdots*\rho_m$ be the measure of $e^{-\varphi}$ (Lemma 2).
--
--   For $r\in\mathbb R^m_{>0}$, $\mathrm{Exp}(r)=\bigotimes_i\mathrm{Exp}(r_i)$ has density $\prod_i r_ie^{-r_iz_i}$ on $\mathbb R^m_{>0}$. **Algorithm 2** (Forwards$(x,\tau)$) draws $z^{(1)},\dots,z^{(\tau)}$ i.i.d. $\mathrm{Exp}(s(x))$, sets $\gamma=\sum_{l}z^{(l)}$ and returns $y=A^\top\gamma$. The law of $\gamma$ is the dual conditional $\pi^{\Gamma|X=x}_{t,\tau}$ of §5 (it does not depend on $t$), and the law of $y$ is the forwards law.
--
--   **Formalization Note** The product density is taken on $\mathbb R^m$ with the indicator of $z\ge0$ (Mathlib's `exponentialPDF`); the paper's $\mathbb R_{>0}$ differs by a null set.
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 2, Algorithm 2 and the definition of Exp(r), p.11 (PDF p.13); §5.1, p.41 (PDF p.43)

import Mathlib
import Definitions.Def_PolySampIso_LogBarrier

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PolySampIso

/-!
# The dual measure of the log barrier (Lemma 2) and the forwards step (Algorithm 2)

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), p.11 (PDF p.13). Lemma 2: "For each i ∈ [m], define
Ri := {y ∈ Rn | y = tai, t > 0}. Let exp(−φi) be the density on span(ai), supported on Ri, induced by
the pushforward of exp(−tbi)It>0dt by t ↦ tai. Define exp(−φ) := exp(−φ1) ∗ · · · ∗ exp(−φm)."
"Define for a vector r ∈ Rm>0 the product measure Exp(r) := ⊗i∈[m] Exp(ri) over Rm>0."
Algorithm 2 (Forwards(x, τ)): "z(i) ∼ i.i.d. Exp(s(x)) for all i ∈ [τ]; γ ← Σi∈[τ] z(i);
y ← A⊤γ; Return: y". §5.1, p.41 (PDF p.43): the Γ-conditional `π^{Γ|X=x}_{t,τ}` is the law of `γ`.

**Formalization Note.**
* `facetMeasure A b i` is the pushforward of `exp(−t bᵢ)𝕀_{t>0} dt` under `t ↦ t aᵢ`
  (`aᵢ` the `i`-th row of `A`), the measure of `exp(−φᵢ)`; `dualMeasure A b = ρ₁ ∗ ⋯ ∗ ρ_m` (as
  `ρ₁ ∗ (ρ₂ ∗ ⋯ (ρ_m ∗ δ₀))`) is the measure of `exp(−φ)`.
* `Exp(r)` is the Lebesgue density `∏ᵢ rᵢ e^{−rᵢzᵢ}𝕀_{zᵢ ≥ 0}` on `ℝ^m` (Mathlib's
  `exponentialPDF`; the paper's `R>0` differs by a null set, footnote 6).
* `forwardsGammaLaw A b τ x` is the law of `γ = Σ_{l<τ} z^{(l)}` with `z^{(l)}` i.i.d. `Exp(s(x))`
  (the density of the i.i.d. family is the product density); `forwardsLaw` is the law of `A⊤γ`.
  Both are used for `x ∈ X`, where `s(x) > 0`.
-/

/-- The `i`-th row `aᵢ` of `A` as a point of `ℝⁿ`. -/
noncomputable def rowVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (A i)

/-- `A⊤γ ∈ ℝⁿ`. -/
noncomputable def transposeApply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (γ : Fin m → ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j => ∑ i, A i j * γ i

/-- The measure of `exp(−φᵢ)`: the pushforward of `exp(−t bᵢ)𝕀_{t>0} dt` by `t ↦ t aᵢ`. -/
noncomputable def facetMeasure {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (i : Fin m) : Measure (EuclideanSpace ℝ (Fin n)) :=
  ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity fun t =>
      ENNReal.ofReal (Real.exp (-t * b i))).map fun t => t • rowVec A i

/-- The measure of `exp(−φ) = exp(−φ₁) ∗ ⋯ ∗ exp(−φ_m)` (Lemma 2). -/
noncomputable def dualMeasure {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (List.ofFn (facetMeasure A b)).foldr (· ∗ ·) (Measure.dirac 0)

/-- The product measure `Exp(r) = ⊗ᵢ Exp(rᵢ)` on `ℝ^m`. -/
noncomputable def expProd {m : ℕ} (r : Fin m → ℝ) : Measure (Fin m → ℝ) :=
  (volume : Measure (Fin m → ℝ)).withDensity fun z => ∏ i, exponentialPDF (r i) (z i)

/-- The law of `γ = Σ_{l<τ} z^{(l)}`, `z^{(l)}` i.i.d. `Exp(s(x))` (Algorithm 2, `π^{Γ|X=x}_{t,τ}`). -/
noncomputable def forwardsGammaLaw {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (τ : ℕ) (x : EuclideanSpace ℝ (Fin n)) : Measure (Fin m → ℝ) :=
  ((volume : Measure (Fin τ → Fin m → ℝ)).withDensity fun z =>
      ∏ l, ∏ i, exponentialPDF (slack A b x i) (z l i)).map fun z => ∑ l, z l

/-- The law of the output `y = A⊤γ` of Algorithm 2 (Forwards(x, τ)). -/
noncomputable def forwardsLaw {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (τ : ℕ) (x : EuclideanSpace ℝ (Fin n)) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (forwardsGammaLaw A b τ x).map (transposeApply A)

end PolySampIso


