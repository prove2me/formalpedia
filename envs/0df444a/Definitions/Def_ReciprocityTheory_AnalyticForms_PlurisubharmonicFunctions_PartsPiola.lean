-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:56.315993+00:00
-- url     : https://prove2.me/theorems/59aaa288-e57c-4153-8d17-b9f17ec0c7a4
-- title:
--   Parts Piola
-- statement:
--   Definitions and structural lemmas for Parts Piola, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsPiola.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
section DzCalc
variable {D : ℕ} {j : Fin D} {f g : (Fin D → ℂ) → ℂ} {z : Fin D → ℂ}
end DzCalc
def insL {n : ℕ} (j : Fin (n + 1)) : (Fin n → ℂ) →L[ℝ] (Fin (n + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => Fin.insertNth (α := fun _ => ℂ) j 0 y
      map_add' := fun x y => by
        ext i; refine Fin.succAboveCases j ?_ (fun l => ?_) i <;> simp
      map_smul' := fun c x => by
        ext i; refine Fin.succAboveCases j ?_ (fun l => ?_) i <;> simp }
end
end ReciprocityTheory.AnForm.A


