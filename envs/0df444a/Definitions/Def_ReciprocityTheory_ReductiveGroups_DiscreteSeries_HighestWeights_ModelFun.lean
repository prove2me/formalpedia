-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelFun
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:14:42.490169+00:00
-- url     : https://prove2.me/theorems/91e2617b-e1a5-411d-85cc-4e953536a018
-- title:
--   Model Fun
-- statement:
--   Definitions and structural lemmas for Model Fun, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelFun.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer
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
def blkMinor (ε : Fin n → Bool) (a : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (x.submatrix (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))
    (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))).det
open Classical in

def mexp (ε : Fin n → Bool) (m : Fin n → ℤ) (a : Fin n) : ℤ :=
  if h : (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).Nonempty then
    m a - m ((Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).min' h)
  else m a
def NonnegDom (ε : Fin n → Bool) (m : Fin n → ℤ) : Prop :=
  (∀ a b, a < b → ε a = ε b → m b ≤ m a) ∧ ∀ a, 0 ≤ m a
def f0 (ε : Fin n → Bool) (m : Fin n → ℤ) (x : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∏ a, blkMinor ε a x ^ (mexp ε m a).toNat
def f0K (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) : ℂ := f0 ε m (toMK k)
end ReciprocityTheory.ChartRestriction.DS.HW


