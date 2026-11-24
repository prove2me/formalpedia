-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentSocketGuards
-- name    : Sensitivity214439_Phase0_Solutions_TournamentSocketGuards
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:06:30.192806+00:00
-- url     : https://prove2.me/theorems/f90fb17a-18d1-44a8-a056-99c44cfcd050
-- title:
--   Unary guards from circulant and Paley orientations
-- statement:
--   The unary guard family of an arc relation assigns one singleton check $\{(w,\ast)\}$ to each distinct outgoing neighbor $w$ of a source row $v$. Excluding $w=v$ makes the guard family non-self.
--
--   A mask defines a circulant arc by testing the bit of the displacement $(y-x)\bmod m$. The Paley relation modulo $2659$ is
--   $$
--   x\to y
--   \iff
--   \exists z\in\{1,\ldots,2658\},\quad z^2\equiv y-x\pmod{2659}.
--   $$
--   The bundle includes the no-self-guard proof for the unary constructor.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/TournamentSocketGuards.lean lines 14–71; SHA256 c02c9c0f6bef42f4c35b45fa1a33b6d2ea01d4fa2e2f8c3144119de141506e71; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
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

def unaryTournamentGuards {V : Type} [Fintype V]
    (arc : V → V → Prop) : GuardFamily V Unit :=
  fun v => (Finset.univ.filter fun w => w ≠ v ∧ arc v w).image
    (fun w => {(w, ())})

theorem unaryTournamentGuards_noSelf {V : Type} [Fintype V]
    (arc : V → V → Prop) : NoSelfGuards (unaryTournamentGuards arc) := by
  intro v check hcheck socket hsocket
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hcheck
  have hwv := (Finset.mem_filter.mp hw).2.1
  have hs : socket = (w, ()) := Finset.mem_singleton.mp hsocket
  simpa only [hs] using hwv







def circulantArc {m : ℕ} (mask : ℕ) (x y : Fin m) : Prop :=
  mask.testBit ((y.val + m - x.val) % m) = true



/-- Paley's orientation on the prime field represented by residues. The
unary guard constructor separately excludes a self-loop. -/
def paley2659Arc (x y : Fin 2659) : Prop :=
  ∃ z : Fin 2659, z.val ≠ 0 ∧
    (z.val * z.val) % 2659 = (y.val + 2659 - x.val) % 2659




end
end SensitivityRankedConstruction


