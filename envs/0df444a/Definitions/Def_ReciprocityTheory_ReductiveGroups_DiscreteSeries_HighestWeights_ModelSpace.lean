-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelSpace
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelSpace
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T14:33:23.087806+00:00
-- url     : https://prove2.me/theorems/7ebb52da-3204-489e-8ede-7bfa3d1e7585
-- title:
--   Model Space
-- statement:
--   Definitions and structural lemmas for Model Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelSpace.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def rtr (ε : Fin n → Bool) (k : KG ε) : (KG ε → ℂ) →ₗ[ℂ] (KG ε → ℂ) where
  toFun f := fun x => f (x * k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) : Submodule ℂ (KG ε → ℂ) :=
  Submodule.span ℂ (Set.range fun k : KG ε => rtr ε k (f0K ε m))
def evalK (ε : Fin n → Bool) : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] (KG ε → ℂ) :=
  MvPolynomial.aeval fun p : Fin n × Fin n => fun k : KG ε => toMK k p.1 p.2
def polyK (ε : Fin n → Bool) (D : ℕ) : Submodule ℂ (KG ε → ℂ) :=
  (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ D).map (evalK ε).toLinearMap
def rsub (ε : Fin n → Bool) (k : KG ε) : Fin n × Fin n → MvPolynomial (Fin n × Fin n) ℂ :=
  fun p => ∑ l, MvPolynomial.X (p.1, l) * MvPolynomial.C (toMK k l p.2)
def f0P (ε : Fin n → Bool) (m : Fin n → ℤ) : MvPolynomial (Fin n × Fin n) ℂ :=
  ∏ a, ((Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).submatrix
    (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))
    (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))).det ^ (mexp ε m a).toNat
end ReciprocityTheory.ChartRestriction.DS.HW


