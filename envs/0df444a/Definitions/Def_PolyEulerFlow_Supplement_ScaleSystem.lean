-- Prove2me | Definitions.Def_PolyEulerFlow_Supplement_ScaleSystem
-- name    : PolyEulerFlow_Supplement_ScaleSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:04:27.095592+00:00
-- url     : https://prove2.me/theorems/6a158b9f-4f8b-4cc0-9d37-d91af814e99b
-- title:
--   Scale-controlled polynomial systems and their stable and eventual robust decisions (Definitions 3–6)
-- statement:
--   A **scale-controlled polynomial system** (Definition 3) in dimension $m$ over inputs $x\in\mathbb N^d$ consists of rational polynomial maps
--   $$F:\mathbb R^d\times\mathbb R\times\mathbb R^m\to\mathbb R^m,\qquad c:\mathbb R^d\times\mathbb R\to\mathbb R^m .$$
--   At input $x$, scale $h=2^{-s}$ ($s\in\mathbb N$), step $0<\eta\le1$ and drift disturbances $(\xi_k)$, its orbit is
--   $$z_0=c(x,h),\qquad z_{k+1}=z_k+\eta F(x,h,z_k)+\eta\xi_k ;$$
--   the exact orbit has $\xi=0$. The parameters $(x,h)$ are frozen and exact; the physical time of index $k$ is $k\eta$. Write $1_L(x)\in\{0,1\}$ for the indicator of $L\subseteq\mathbb N^d$.
--
--   1. **Stable decision** (Definition 4). The system decides $L$ at step $\eta$ with threshold $S$, horizon $Q$, output coordinate $o$ and box $[lo,hi]$ if for every $x$ and every integer $s\ge S(\ell(x))$ the exact orbit lies in $[lo,hi]$ and $|z_k(o)-1_L(x)|\le 1/4$ for all $k\ge\lceil Q(s)/\eta\rceil$.
--   2. **Eventual robust decision** (Definition 6) with precision exponent $r$: for every $x$, every $s\ge S(\ell(x))$ and every disturbance sequence with $\|\xi_k\|_\infty\le h^r$, the orbit lies in the box and there is an index $k_0$, which may depend on the orbit, with $|z_k(o)-1_L(x)|\le1/4$ for all $k\ge k_0$.
--   3. **Robust decision with horizon $2^{cs}$**: as in 2, with the output correct at every index $k\ge\lceil 2^{cs}/\eta\rceil$.
--
--   Unit-step means $\eta=1$, mesh-uniform means every $0<\eta\le1$ with the same data. These are the decision semantics of Theorems 8, 9 and 11.
--
--   **Formalization Note** In $F$ the variables are the input coordinates, the scale and the active coordinates; in $c$ the input coordinates and the scale; coefficients are rational. Thresholds and horizons are polynomials with natural coefficients evaluated at $\ell(x)$, resp. $s$. The box is a coordinatewise interval with real corners. The orbit is the published `eulerOrbit` with the constant mesh $\eta$; norms on $\mathbb R^m$ are sup norms.
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow: Polynomial Dynamics for P and PSPACE (manuscript, STOC 2027 submission, sha256 c4e01b2beb237b48b48e97294deb3c15dae11d39c5f136914567c5ca2ae1b119), Definitions 3–6, pp.5–6 (PDF 7–8); Theorem 9, p.7 (PDF 9) for the horizon 2^{cs}

import Mathlib
import Definitions.Def_PolyEulerFlow_Supplement_encodeNatVec
import Definitions.Def_PolyEulerFlow_eulerOrbit

namespace PolyEulerFlow.Supplement

open PolyEulerFlow

/-- The indicator `1_L(x)` of a language `L ⊆ ℕ^d`, as a real number. -/
noncomputable def langIndicator {d : ℕ} (L : Set (Fin d → ℕ)) (x : Fin d → ℕ) : ℝ :=
  open Classical in if x ∈ L then 1 else 0

/-- A scale-controlled polynomial system, Definition 3, p.5 (PDF 7): rational polynomial maps `F : ℝ^d × ℝ × ℝ^m → ℝ^m` and
`c : ℝ^d × ℝ → ℝ^m`. Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…).
**Formalization Note.** In `F` the variable `inl i` is the input coordinate `x_i`, `inr none` is the scale `h` and `inr (some j)` is the
active coordinate `z_j`; in `c` the variable `inl i` is `x_i` and `inr ()` is `h`. The coefficients are rational. -/
structure ScaleSystem (d m : ℕ) where
  F : Fin m → MvPolynomial (Fin d ⊕ Option (Fin m)) ℚ
  c : Fin m → MvPolynomial (Fin d ⊕ Unit) ℚ

namespace ScaleSystem

variable {d m : ℕ} (S : ScaleSystem d m)

/-- The field `z ↦ F(x, h, z)` at frozen input `x` and scale `h`. -/
noncomputable def field (x : Fin d → ℕ) (h : ℝ) (z : Fin m → ℝ) : Fin m → ℝ :=
  fun i => MvPolynomial.aeval (Sum.elim (fun j => (x j : ℝ)) (fun v : Option (Fin m) => v.elim h z)) (S.F i)

/-- The initialization `c(x, h)`. -/
noncomputable def init (x : Fin d → ℕ) (h : ℝ) : Fin m → ℝ :=
  fun i => MvPolynomial.aeval (Sum.elim (fun j => (x j : ℝ)) (fun _ : Unit => h)) (S.c i)

/-- The active orbit at input `x`, scale `h = 2^{-s}` and constant step `η`, with drift disturbances `ξ` (Definitions 3 and 5):
`z₀ = c(x, h)`, `z_{k+1} = z_k + ηF(x, h, z_k) + ηξ_k`. The exact orbit of Definition 3 is `ξ = 0`. -/
noncomputable def orbit (x : Fin d → ℕ) (s : ℕ) (η : ℝ) (ξ : ℕ → Fin m → ℝ) : ℕ → Fin m → ℝ :=
  eulerOrbit (S.field x (scale s)) (S.init x (scale s)) (fun _ => η) ξ

/-- Stable decision at the step `η`, Definition 4, p.6 (PDF 8): for every input `x` and every integer `s ≥ S(ℓ(x))`, the exact orbit
lies in the box `[lo, hi]` and `|o_k − 1_L(x)| ≤ 1/4` for every `k ≥ ⌈Q(s)/η⌉`. Unit-step is `η = 1`; mesh-uniform is every
`η ∈ (0, 1]` with the same system, threshold, horizon, output coordinate and box. -/
def StablyDecidesAt (L : Set (Fin d → ℕ)) (Sthr Q : Polynomial ℕ) (o : Fin m) (lo hi : Fin m → ℝ) (η : ℝ) : Prop :=
  ∀ x : Fin d → ℕ, ∀ s : ℕ, Sthr.eval (vecLength x) ≤ s →
    (∀ k, S.orbit x s η (fun _ => 0) k ∈ Set.Icc lo hi) ∧
      ∀ k : ℕ, ⌈((Q.eval s : ℕ) : ℝ) / η⌉₊ ≤ k → |S.orbit x s η (fun _ => 0) k o - langIndicator L x| ≤ 1 / 4

/-- Eventual robust decision at the step `η`, Definition 6, p.6 (PDF 8): for every input `x`, every `s ≥ S(ℓ(x))` and every orbit from
the exact initialization with drift disturbances `‖ξ_k‖∞ ≤ h^r`, the whole orbit lies in the box and its output is eventually within `1/4`
of `1_L(x)`; the stabilization index may depend on the orbit. -/
def EventuallyRobustAt (L : Set (Fin d → ℕ)) (Sthr : Polynomial ℕ) (r : ℝ) (o : Fin m) (lo hi : Fin m → ℝ) (η : ℝ) : Prop :=
  ∀ x : Fin d → ℕ, ∀ s : ℕ, Sthr.eval (vecLength x) ≤ s →
    ∀ ξ : ℕ → Fin m → ℝ, IsPermittedDisturbance (scale s ^ r) ξ →
      (∀ k, S.orbit x s η ξ k ∈ Set.Icc lo hi) ∧
        ∃ k0 : ℕ, ∀ k, k0 ≤ k → |S.orbit x s η ξ k o - langIndicator L x| ≤ 1 / 4

/-- Robust decision with the common physical stabilization horizon `2^{cs}` (Theorem 9, p.7): as `EventuallyRobustAt`, with the output
correct at every index `k ≥ ⌈2^{cs}/η⌉`. -/
def RobustHorizonAt (L : Set (Fin d → ℕ)) (Sthr : Polynomial ℕ) (r c : ℝ) (o : Fin m) (lo hi : Fin m → ℝ) (η : ℝ) : Prop :=
  ∀ x : Fin d → ℕ, ∀ s : ℕ, Sthr.eval (vecLength x) ≤ s →
    ∀ ξ : ℕ → Fin m → ℝ, IsPermittedDisturbance (scale s ^ r) ξ →
      (∀ k, S.orbit x s η ξ k ∈ Set.Icc lo hi) ∧
        ∀ k : ℕ, ⌈(2 : ℝ) ^ (c * s) / η⌉₊ ≤ k → |S.orbit x s η ξ k o - langIndicator L x| ≤ 1 / 4

end ScaleSystem

end PolyEulerFlow.Supplement


