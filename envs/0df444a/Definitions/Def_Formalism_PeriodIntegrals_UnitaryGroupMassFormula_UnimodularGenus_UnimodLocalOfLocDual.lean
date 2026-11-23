-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_UnimodLocalOfLocDual
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_UnimodLocalOfLocDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:44.493164+00:00
-- url     : https://prove2.me/theorems/f8e12397-62e0-459c-8415-67620d8fcda9
-- title:
--   Unimod Local Of Loc Dual
-- statement:
--   Definitions and structural lemmas for Unimod Local Of Loc Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularGenus/UnimodLocalOfLocDual.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_StdLatEqSpan
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace PI.UG.W
example (E : Type) [Field E] [NumberField E] [StarRing E] : PI.UG.IsCMUnram E ↔ Formalism.HermitianLatticesTheory.IsCMUnram E := Iff.rfl
example (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (p : Ideal (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) :
    IsUnimodularAt (hStd E n) p N ↔ Formalism.HermitianLatticesTheory.IsUnimodularAt (hStd E n) p N := Iff.rfl
example (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (p : Ideal (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) :
    (∃ g ∈ isom (hStd E n), gmap g (loc (K := E) p (stdLat E n)) = loc (K := E) p N) ↔
    (∃ g ∈ Formalism.HermitianLatticesTheory.isom (hStd E n), Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := E) p (stdLat E n)) = Formalism.HermitianLatticesTheory.loc (K := E) p N) :=
  Iff.rfl
end PI.UG.W


