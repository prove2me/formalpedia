-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValBr
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieValBr
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T10:25:15.577706+00:00
-- url     : https://prove2.me/theorems/b4c28558-070d-534a-8d70-c94185a1e36e
-- title:
--   Row Tie Val Br
-- statement:
--   Definitions and structural lemmas for Row Tie Val Br, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValBr.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValueEquationOfProjectors
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieProj
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_GoodPt_act
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
def EndoLogSt (Y : FBChart C V O dd) : Prop :=
  ∀ ε : Pt C 1 dd, (∀ i, MvPowerSeries.constantCoeff (ε i) = 0) →
    comp1 ε (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 ε (pt C (n := 2) dd 0)) (comp1 ε (pt C (n := 2) dd 1)) →
    ∀ (τ : Type) [Finite τ] (a : Fin dd → MvPowerSeries τ C), (∀ i, MvPowerSeries.constantCoeff (a i) = 0) →
    ∀ i, MvPowerSeries.subst (fun q : Fin 1 × Fin dd => VP.exAt Y a q.2) (ε i) =
      VP.exAt Y (fun m => ∑ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (ε m) • a j) i
def KillSt (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) : Prop :=
  PairsSep Y p → ∀ (o : Orb) (g : Fin 2) (ε : Pt C 1 dd), (∀ i, MvPowerSeries.constantCoeff (ε i) = 0) →
    (∀ a, comp1 ε (Y.B.A.act a) = comp1 (Y.B.A.act a) ε) →
    (∀ v : Fin dd → C, ∃ b : I o g → C, linAct ε v = ∑ c, b c • (p o).u g c) →
    ∀ w : WVO I, (w.1, w.2.1) ≠ (o, g) → linAct ε ((p w.1).u w.2.1 w.2.2) = 0
end Formalism.L2.FormalSeriesBounds


