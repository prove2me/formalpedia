-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffTripleSubstitution
-- name    : Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffTripleSubstitution
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T09:20:41.115797+00:00
-- url     : https://prove2.me/theorems/8759bca6-c5af-53b7-85e7-e3a40f36a20c
-- title:
--   Constant Coeff Triple Substitution
-- statement:
--   Definitions and structural lemmas for Constant Coeff Triple Substitution, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffTripleSubstitution.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValU
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
namespace VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}
def P2 (a b : Fin dd → MvPowerSeries τ C) : Fin 2 × Fin dd → MvPowerSeries τ C :=
  fun q => if q.1 = 0 then a q.2 else b q.2
def P3 (a b c : Fin dd → MvPowerSeries τ C) : Fin 3 × Fin dd → MvPowerSeries τ C :=
  fun q => if q.1 = 0 then a q.2 else if q.1 = 1 then b q.2 else c q.2
variable (Y : FBChart C V O dd)
def hAt (a b : Fin dd → MvPowerSeries τ C) : MvPowerSeries τ C := MvPowerSeries.subst (P2 a b) Y.h
def actAt (x : O) (a : Fin dd → MvPowerSeries τ C) : Fin dd → MvPowerSeries τ C :=
  fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (Y.B.A.act x i)
def addAt (a b : Fin dd → MvPowerSeries τ C) : Fin dd → MvPowerSeries τ C :=
  fun i => MvPowerSeries.subst (P2 a b) (Y.B.G.F i)
variable {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
  (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)
include ha hb
end VP
end Formalism.L2.FormalSeriesBounds


