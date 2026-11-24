-- Prove2me | Definitions.Def_RegMT_Classif_Supplement_Perturbation
-- name    : RegMT_Classif_Supplement_Perturbation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:25:01.06393+00:00
-- url     : https://prove2.me/theorems/fcd203ad-bc45-44e0-90c1-c82c2643ddc7
-- title:
--   Robust perturbations, Assumptions 3.7 and 3.18, absolute error
-- statement:
--   For regression and classification define the supremum of the empirical loss over perturbations with average norm budget at most $\rho$, exactly as in (15) and (28). The regression norm is the arbitrary joint norm; classification never perturbs labels. Assumption 3.7 requires, for every $w$, some sample with an existing loss derivative of magnitude $\operatorname{lip}(L)$ at the residual. Assumption 3.18 uses the signed margin instead.
--   $$\forall w\ \exists i,t:\quad L'(r_w(\hat\xi_i))=t,\quad |t|=\operatorname{lip}(L).$$
--   The classification condition has $\hat y_i\langle w,\hat x_i\rangle$ in place of the residual. Neither condition assumes an equality of optimization values. The same layer defines the infimum expected absolute residual over the full norm ball and its empirical average, for Theorem 5.1, p.22. All expectations are extended nonnegative integrals.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p.10, Assumption 3.7; p.11 (15); p.14, Assumption 3.18 and (28); p.22, Theorem 5.1

import Mathlib
import Definitions.Def_RegMT_Classif_Supplement_Transport
import Definitions.Def_RegMT_Regress_Model

open scoped ENNReal

noncomputable section

namespace RegMT.Classif.Supplement
open DRLogReg.Reformulation WassersteinDRO.Duality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def robustReg {N : ℕ} (z : Fin N → E) (L : ℝ → ℝ) (r : E →L[ℝ] ℝ) (ρ : ℝ) : ℝ≥0∞ :=
  ⨆ d : Fin N → E, ⨆ (_ : (N : ℝ)⁻¹ * ∑ i, ‖d i‖ ≤ ρ),
    ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i, L (r (z i + d i)))

def robustClass {N : ℕ} (x : Fin N → V) (y : Fin N → Bool) (L : ℝ → ℝ)
    (w : V →L[ℝ] ℝ) (ρ : ℝ) : ℝ≥0∞ :=
  ⨆ d : Fin N → V, ⨆ (_ : (N : ℝ)⁻¹ * ∑ i, ‖d i‖ ≤ ρ),
    ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i, L (sgn (y i) * w (x i + d i)))

/-- Assumption 3.7 in full: every weight has a sample attaining the modulus in derivative magnitude. -/
def MinimalDispersion {n N : ℕ} (e : E ≃L[ℝ] (Fin n → ℝ) × ℝ)
    (z : Fin N → E) (L : ℝ → ℝ) : Prop :=
  ∀ w : Fin n → ℝ, ∃ i : Fin N, ∃ t : ℝ,
    HasDerivAt L t (RegMT.Regress.pairing e w (z i)) ∧
    ENNReal.ofReal |t| = lipschitzModulus L

/-- Assumption 3.18 in full, not an equality of objective values. -/
def Nonseparability {N : ℕ} (x : Fin N → V) (y : Fin N → Bool) (L : ℝ → ℝ) : Prop :=
  ∀ w : V →L[ℝ] ℝ, ∃ i : Fin N, ∃ t : ℝ,
    HasDerivAt L t (sgn (y i) * w (x i)) ∧ ENNReal.ofReal |t| = lipschitzModulus L

variable [MeasurableSpace E]

def bestAbs {N : ℕ} (z : Fin N → E) (ρ : ℝ) (r : E →L[ℝ] ℝ) : ℝ≥0∞ :=
  ⨅ Q ∈ ambiguitySet ρ 1 Set.univ (empiricalDistribution z), expected Q (fun u => |r u|)

def empiricalAbs {N : ℕ} (z : Fin N → E) (r : E →L[ℝ] ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, |r (z i)|

end RegMT.Classif.Supplement


