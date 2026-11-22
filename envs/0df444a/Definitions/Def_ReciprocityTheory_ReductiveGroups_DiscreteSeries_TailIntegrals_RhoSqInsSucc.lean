-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:16:04.878805+00:00
-- url     : https://prove2.me/theorems/c1552fdb-62e2-4491-ab29-ba9672fa2975
-- title:
--   Rho Sq Ins Succ
-- statement:
--   Definitions and structural lemmas for Rho Sq Ins Succ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RhoSqInsSucc.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux
abbrev Yp (p m : ℕ) := (Fin (p + 1) → ℂ) × (Fin p → ℂ) × (Fin m → ℂ) × ℝ
def ins {p m : ℕ} (y : Yp p m) (z : ℂ) : Xp (p + 1) m := (y.1, Fin.cons z y.2.1, y.2.2)
def bS {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : ℂ :=
  ∑ j : Fin p, if l.val ≤ j.val then x.2.1 j * star (x.1 j) else 0
def splitE (p m : ℕ) : Xp (p + 1) m ≃ᵐ Yp p m × ℂ :=
  ((MeasurableEquiv.refl (Fin (p + 1) → ℂ)).prodCongr
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).prodCongr
        (MeasurableEquiv.refl ((Fin m → ℂ) × ℝ)))).trans
    (((MeasurableEquiv.refl (Fin (p + 1) → ℂ)).prodCongr MeasurableEquiv.prodAssoc).trans
      (MeasurableEquiv.prodAssoc.symm.trans
        ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl _)).trans
          (MeasurableEquiv.prodAssoc.trans MeasurableEquiv.prodComm))))
end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi


