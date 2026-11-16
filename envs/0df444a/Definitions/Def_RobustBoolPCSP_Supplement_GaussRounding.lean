-- Prove2me | Definitions.Def_RobustBoolPCSP_Supplement_GaussRounding
-- name    : RobustBoolPCSP_Supplement_GaussRounding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:23:26.016609+00:00
-- url     : https://prove2.me/theorems/17101042-1df5-4321-9612-d665deab9c0b
-- title:
--   The local Gaussian score law (17)
-- statement:
--   Fix a probability distribution $\lambda=(\lambda_x)_{x\in A^r}$ (not necessarily supported on $P$) and put $\delta=\lambda(A^r\setminus P)$. Let $Z_x$, $x\in A^r$, be independent centered Gaussians of variance $\lambda_x$ ($Z_x=0$ when $\lambda_x=0$). For $0<t\le1$ the **scores** are
--
--   $$p_{i,a}=\sum_{x:x_i=a}\lambda_x,\qquad S_{i,a}=p_{i,a}+t\sum_{x:x_i=a}Z_x.$$
--
--   Rounding each coordinate $i$ by a selector applied to the row $(S_{i,a})_{a\in A}$ is the local step of the paper's algorithms (Theorems 5.3 and 5.18).
--
--   **Formalization Note** The joint law of $(Z_x)_x$ is the product of Mathlib's `gaussianReal 0 λ_x`; variance zero gives the Dirac mass at $0$.
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §5.1, p.29, eq. (17)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RobustBoolPCSP.Supplement

/-- The joint law of the independent centered Gaussians `Z_x ∼ N(0, λ_x)`, `x ∈ A^r`, of the local
rounding model (17).
Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03, sha256
fd1be0d0…), §5.1, p.29: "Let λ = (λ_x)_{x∈A^r} be a probability distribution, not necessarily
supported on P, and set δ = λ(A^r \ P). Let Z_x be independent centered Gaussians of variance λ_x,
with Z_x = 0 whenever λ_x = 0."

**Formalization Note.** The product (`Measure.pi`) of Mathlib's `gaussianReal 0 (λ x)`; for
`λ x = 0` this factor is the Dirac mass at `0`, matching "Z_x = 0 whenever λ_x = 0". The weights
`λ : A^r → ℝ≥0` are a probability vector where this law is used. -/
noncomputable def gaussLaw {A : Type} [Fintype A] [DecidableEq A] {r : ℕ}
    (lam : (Fin r → A) → ℝ≥0) : Measure ((Fin r → A) → ℝ) :=
  Measure.pi (fun x => gaussianReal 0 (lam x))

/-- The marginal `p_{i,a} = Σ_{x : x_i = a} λ_x` (17). -/
noncomputable def marg {A : Type} [Fintype A] [DecidableEq A] {r : ℕ}
    (lam : (Fin r → A) → ℝ≥0) (i : Fin r) (a : A) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : Fin r → A => x i = a), (lam x : ℝ)

/-- The perturbed score `S_{i,a} = p_{i,a} + t Σ_{x : x_i = a} Z_x` (17), as a function of the
Gaussian vector `z = (Z_x)_x`. -/
noncomputable def score {A : Type} [Fintype A] [DecidableEq A] {r : ℕ}
    (lam : (Fin r → A) → ℝ≥0) (t : ℝ) (z : (Fin r → A) → ℝ) (i : Fin r) (a : A) : ℝ :=
  marg lam i a + t * ∑ x ∈ Finset.univ.filter (fun x : Fin r → A => x i = a), z x

/-- The local strong error `δ = λ(A^r \ P)` (p.29). -/
noncomputable def defect {A : Type} [Fintype A] [DecidableEq A] {r : ℕ}
    (P : Set (Fin r → A)) (lam : (Fin r → A) → ℝ≥0) : ℝ :=
  ∑ x, Pᶜ.indicator (fun y => (lam y : ℝ)) x

end RobustBoolPCSP.Supplement


