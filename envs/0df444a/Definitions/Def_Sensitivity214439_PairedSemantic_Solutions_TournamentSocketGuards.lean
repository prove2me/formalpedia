-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_TournamentSocketGuards
-- name    : Sensitivity214439_PairedSemantic_Solutions_TournamentSocketGuards
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:56:35.827798+00:00
-- url     : https://prove2.me/theorems/179d7a2c-8a9a-4c70-8ee1-fcfacd3d2236
-- title:
--   Cyclic arcs, circulant labels, and paired tournament guards
-- statement:
--   The cyclic relation uses positive modular displacements at most half the modulus, and a circulant label reads the Boolean label mask at the displacement. Paired tournament guards use a singleton at the labeled socket for an external macro arc and both destination sockets for an internal arc within one macro.
--
--   The resulting guard family has no self-sockets: external arcs go to a distinct macro, and internal arcs go to a distinct internal row. This property is used by canonical witness lifting and by single-row event decompositions.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/TournamentSocketGuards.lean lines 27–65; SHA256 c02c9c0f6bef42f4c35b45fa1a33b6d2ea01d4fa2e2f8c3144119de141506e71; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentSocketGuards
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-!
Actual guard placement for the checkpoint's unary tournament and clustered
paired tournament. All macro destinations are checked in the labeled child
socket; all internal destinations are checked by the OR of both children.
-/

namespace SensitivityRankedConstruction

noncomputable section
open scoped Classical





def pairedTournamentGuards {M B : Type} [Fintype M] [Fintype B]
    (macroArc : M → M → Prop) (label : M → M → Bool)
    (internalArc : B → B → Prop) : GuardFamily (M × B) Bool :=
  fun v =>
    ((Finset.univ.filter fun w : M × B => w.1 ≠ v.1 ∧ macroArc v.1 w.1).image
      (fun w => {(w, label v.1 w.1)})) ∪
    ((Finset.univ.filter fun w : M × B =>
      w.1 = v.1 ∧ w.2 ≠ v.2 ∧ internalArc v.2 w.2).image
      (fun w => {(w, false), (w, true)}))

theorem pairedTournamentGuards_noSelf {M B : Type} [Fintype M] [Fintype B]
    (macroArc : M → M → Prop) (label : M → M → Bool)
    (internalArc : B → B → Prop) :
    NoSelfGuards (pairedTournamentGuards macroArc label internalArc) := by
  intro v check hcheck socket hsocket
  rcases Finset.mem_union.mp hcheck with hexternal | hinternal
  · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hexternal
    have hwv := (Finset.mem_filter.mp hw).2.1
    have hs : socket = (w, label v.1 w.1) := Finset.mem_singleton.mp hsocket
    intro heq
    rw [hs] at heq
    exact hwv (congrArg Prod.fst heq)
  · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hinternal
    have hwv := (Finset.mem_filter.mp hw).2.2.1
    have hs : socket.1 = w := by
      rcases Finset.mem_insert.mp hsocket with hs | hs
      · exact congrArg Prod.fst hs
      · exact congrArg Prod.fst (Finset.mem_singleton.mp hs)
    intro heq
    exact hwv (congrArg Prod.snd (hs.symm.trans heq))

def cyclicArc {b : ℕ} (x y : Fin b) : Prop :=
  0 < (y.val + b - x.val) % b ∧ (y.val + b - x.val) % b ≤ b / 2



def circulantLabel {m : ℕ} (mask : ℕ) (x y : Fin m) : Bool :=
  mask.testBit ((y.val + m - x.val) % m)






end
end SensitivityRankedConstruction


