-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
-- name    : Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T11:06:53.494913+00:00
-- url     : https://prove2.me/theorems/5aea960b-2292-4202-bd1c-7eba624dcbc9
-- title:
--   Block Admissible Chart
-- statement:
--   Definitions and structural lemmas for Block Admissible Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockAdmissibleChart.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieVal
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
namespace Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
  (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)
abbrev rd (o : Orb) : RowData C V d (I o) (JJ (I o)) := (Y.raw (p o)).rowData (H o)
def imgFam : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C) :=
  {Po | ∃ P ∈ Ls.FF n, IsImgO (fun o => Y.raw (p o)) (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o))}
variable (F : ∀ o, Flag (rd Y p H o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)
def BlockMembershipChart : Prop := BlockMembership (fun o => rd Y p H o) n F (imgFam Y p Ls n) Z ga
def BlockAdmissibleChart : Prop := BlockAdmissible (fun o => rd Y p H o) F Z ga
end Formalism.L2.FormalSeriesBounds.RF


