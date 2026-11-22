-- Prove2me | Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV
-- name    : Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:45.06751+00:00
-- url     : https://prove2.me/theorems/8aaa5751-e375-4440-b127-11da17a4ffd6
-- title:
--   Group V
-- statement:
--   Definitions and structural lemmas for Group V, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
namespace Formalism.FG.FormalGroupCoefficients
open MvPowerSeries Formalism.G Formalism.LT
section General
variable {R : Type u} [CommRing R]
end General
section Law
variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {f : ι → MvPowerSeries ι R} {F : ι → MvPowerSeries (Fin 2 × ι) R}
def swp : Fin 2 × ι → MvPowerSeries (Fin 2 × ι) R := fun x => X (Fin.rev x.1, x.2)
def zY : Fin 2 × ι → MvPowerSeries (Fin 2 × ι) R := fun x => if x.1 = 0 then X x else 0
def zX : Fin 2 × ι → MvPowerSeries (Fin 2 × ι) R := fun x => if x.1 = 1 then X x else 0
def c01 : Fin 2 × ι → MvPowerSeries (Fin 3 × ι) R := fun y => v3 (Fin.castSucc y.1) y.2
def c12 : Fin 2 × ι → MvPowerSeries (Fin 3 × ι) R := fun y => v3 y.1.succ y.2
def aL (F : ι → MvPowerSeries (Fin 2 × ι) R) : Fin 2 × ι → MvPowerSeries (Fin 3 × ι) R :=
  fun x => if x.1 = 0 then subst c01 (F x.2) else v3 2 x.2
def aR (F : ι → MvPowerSeries (Fin 2 × ι) R) : Fin 2 × ι → MvPowerSeries (Fin 3 × ι) R :=
  fun x => if x.1 = 0 then v3 0 x.2 else subst c12 (F x.2)
end Law
section FunEq
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
end FunEq
end Formalism.FG.FormalGroupCoefficients
namespace Formalism.FG
open MvPowerSeries Formalism.G Formalism.LT Formalism.FG.FormalGroupCoefficients
end Formalism.FG


