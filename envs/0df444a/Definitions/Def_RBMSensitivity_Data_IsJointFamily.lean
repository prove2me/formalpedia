-- Prove2me | Definitions.Def_RBMSensitivity_Data_IsJointFamily
-- name    : RBMSensitivity_Data_IsJointFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:35:56.998395+00:00
-- url     : https://prove2.me/theorems/f253629c-1422-4b4e-8f55-09b47bdbc2ba
-- title:
--   The family of joint processes $\Xi^{\alpha,\xi}=(Z^{\alpha,x},\mathcal J^{\alpha,\xi})$
-- statement:
--   Given $\xi=(x,y)\in\mathbb X$, there is a pathwise unique joint process $\Xi^{\alpha,\xi}=(Z^{\alpha,x},\mathcal J^{\alpha,\xi})$ associated with $\alpha$ with initial condition $\xi$: $Z^{\alpha,x}$ is the RBM from $x$ and $\mathcal J^{\alpha,\xi}$ is the derivative process along it starting at $y$. This predicate says that a family of processes consists of such pairs, all driven by the same Brownian motion.
--
--   The joint process is the Markov process whose stationary distribution gives the sensitivity formula.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §3.1, p.9

import Mathlib
import Definitions.Def_RBMSensitivity_Data_IsRBMFamily
import Definitions.Def_RBMSensitivity_Data_IsDerivativeProcess
import Definitions.Def_RBMSensitivity_SimpleCone_X
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The family of joint processes `Ξ^{α,ξ} = (Z^{α,x}, 𝒥^{α,ξ})`, `ξ = (x, y) ∈ X`:
arXiv:1907.00472v2, §3.1, p.9. `Z α x` is the RBM from `x` and `𝒥 α ξ` the derivative process along it
starting at `y`.

**Formalization Note.** Theorems 2.8 and 2.13 show such a family exists and is unique up to
indistinguishability. `𝒥 α ξ` for `ξ ∉ X` is not constrained, and never used. -/
structure Data.IsJointFamily {J : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} (D : Data J)
    (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (W : ℝ≥0 → Ω → E J)
    (Z : ℝ → E J → ℝ≥0 → Ω → E J) (𝒥 : ℝ → E J × E J → ℝ≥0 → Ω → E J) : Prop where
  rbm : D.IsRBMFamily 𝓕 P W Z
  derivative : ∀ α ∈ D.U, ∀ ξ ∈ D.X,
    D.IsDerivativeProcess 𝓕 P W α (Z α ξ.1) (𝒥 α ξ) ∧ ∀ᵐ ω ∂P, 𝒥 α ξ 0 ω = ξ.2

end RBMSensitivity


