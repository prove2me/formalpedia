-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:03.763642+00:00
-- url     : https://prove2.me/theorems/063b71cb-9b53-4fda-890c-f7f27dbf39f7
-- title:
--   Constant Coeff Ev
-- statement:
--   Definitions and structural lemmas for Constant Coeff Ev, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ConstantCoeffEv.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqCOfPderivZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d m n : ℕ}
def CZ (a : Fin m → Pt k n d) : Prop := ∀ j i, constantCoeff (a j i) = 0
theorem CZ.hasSubst {a : Fin m → Pt k n d} (ha : CZ a) : HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2
def evHom {a : Fin m → Pt k n d} (ha : CZ a) : PS k m d →+* PS k n d :=
  (substAlgHom ha.hasSubst).toRingHom
theorem constantCoeff_ev {a : Fin m → Pt k n d} (ha : CZ a) {f : PS k m d} (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 :=
  constantCoeff_subst_eq_zero ha.hasSubst (fun p => ha p.1 p.2) hf
theorem CZ.ev {a : Fin m → Pt k n d} (ha : CZ a) {l : ℕ} {b : Fin l → Pt k m d} (hb : CZ b) :
    CZ (fun j i => ev a (b j i)) := fun j i => constantCoeff_ev ha (hb j i)
end GlobalTheory.FormalLog


