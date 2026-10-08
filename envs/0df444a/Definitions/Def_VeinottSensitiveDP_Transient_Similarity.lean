-- Prove2me | Definitions.Def_VeinottSensitiveDP_Transient_Similarity
-- name    : VeinottSensitiveDP_Transient_Similarity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:08.059195+00:00
-- url     : https://prove2.me/theorems/3fa13850-4b1e-4dcf-a479-da97d2c8942b
-- title:
--   Spectral radius |σ(B)| and positive similarity of dynamic programs
-- statement:
--   **Spectral radius.** For a real $S\times S$ matrix $B$, $\sigma(B)$ is its spectrum (the set of its complex eigenvalues) and $|\sigma(B)|=\max\{|\lambda|:\lambda\in\sigma(B)\}$ its spectral radius.
--
--   **Positive similarity.** A dynamic program $(\tilde r(\cdot),\tilde P(\cdot))$ is **positively similar** to $(r(\cdot),P(\cdot))$ if both are defined on the same set $F$ of decision rules and there is an $S\times S$ diagonal matrix $B$ with positive diagonal elements such that
--
--   $$\tilde r(f)=B\,r(f)\quad\text{and}\quad \tilde P(f)=B\,P(f)\,B^{-1}\qquad\text{for all } f\in F.$$
--
--   Positive similarity is an equivalence relation; transience of a policy, and which policies maximize the total reward, are the same in positively similar programs, while the norms of the transition matrices are not. Hoffman's Lemma 3 uses it to bring the norms down to the spectral radii.
--
--   **Formalization Note.** The spectral radius is Mathlib's `spectralRadius ℂ` of the matrix viewed in the complex matrix algebra, a value in $[0,\infty]$; using complex eigenvalues matters because a nonnegative matrix can have non-real eigenvalues of maximal modulus. Positive similarity is a relation `PositivelySimilar D' D` between two programs on the same states and action sets, stated literally with `Matrix.diagonal b` for $b$ with positive entries; the matrix inverse is then the genuine inverse.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1636 (spectral radius) and p. 1638 (positive similarity)

import Mathlib
import Definitions.Def_VeinottSensitiveDP_Transient_Model

namespace VeinottSensitiveDP.Transient

open Matrix

variable {St : Type} {A : St → Type}

/-- The spectral radius `|σ(B)|` of a real `S × S` matrix (p. 1636): the largest modulus of a
**complex** eigenvalue of `B`.

**Formalization Note.** `B` is viewed as a complex matrix and Mathlib's `spectralRadius ℂ` is
taken in the complex matrix algebra; the value lies in `ℝ≥0∞` (it is finite for a matrix). -/
noncomputable def specRad [Fintype St] [DecidableEq St] (B : Matrix St St ℝ) : ENNReal :=
  spectralRadius ℂ (B.map (algebraMap ℝ ℂ))

namespace Program

/-- **Positive similarity** (p. 1638): the dynamic program `(r̃(·), P̃(·))` (here `D'`) is
positively similar to `(r(·), P(·))` (here `D`) if both are defined on `F` and there is an
`S × S` diagonal matrix `B` with positive diagonal elements such that `r̃(f) = B r(f)` and
`P̃(f) = B P(f) B⁻¹` for all `f ∈ F`. -/
def PositivelySimilar [Fintype St] [DecidableEq St] (D' D : Program St A) : Prop :=
  ∃ b : St → ℝ, (∀ s, 0 < b s) ∧ ∀ f : DecisionRule St A,
    D'.rvec f = Matrix.diagonal b *ᵥ D.rvec f ∧
    D'.Pmat f = Matrix.diagonal b * D.Pmat f * (Matrix.diagonal b)⁻¹

end Program

end VeinottSensitiveDP.Transient


