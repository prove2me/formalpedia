-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
-- name    : OAI_Probability_CriticalZ3_SeedTrials
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:04:21.404918+00:00
-- url     : https://prove2.me/theorems/982d3c21-7495-42a2-8075-f1f04e82f8b7
-- title:
--   Seed boxes attached to entry points
-- statement:
--   Seed cubes used in repeated trials to connect an entering cluster to the interior of a box $C$.
--
--   1. **Monotonicity.** If box $B$ is contained in box $C$, then the bits of $B$ are among the bits of $C$, and a lattice graph containing $C$ contains $B$.
--   2. **Relay centres.** For radius $r$ and an exterior vertex $y$, the relay centre is the entry point of $y$ clamped $r$ away from the faces of $C$. The seed box is the cube of radius $r$ around it, which lies inside $C$ when $C$ is wide enough.
--   3. **Success bits.** The success bits of $y$ are the seed box's bits, together with the entry bond in the bond model. Their number is
--   $$
--   \mathrm{seedCard}(r)+[\text{bond model}],
--   $$
--   where $\mathrm{seedCard}(r)$ is the number of bits of a cube of radius $r$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/SeedTrials.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/SeedTrials.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CriticalZ3 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers

namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical
namespace Box

theorem bits_mono (m : Model) {B C : Box} (h : ∀ x, B.Contains x → C.Contains x) :
    B.bits m ⊆ C.bits m := by
  intro e he
  cases m
  · exact (mem_bonds C e).mpr ⟨h _ ((mem_bonds B e).mp he).1,h _ ((mem_bonds B e).mp he).2⟩
  · exact (mem_vertices C e).mpr (h _ ((mem_vertices B e).mp he))

@[simp] theorem center_mem_cube (c : Vertex) (r : ℕ) : (cube c r).Contains c := by
  rw [contains_cube]; intro i; simp

noncomputable def relayCenter (C : Box) (r : ℕ) (y : Vertex) := C.seedCenter r (C.entry y)
noncomputable def seedBox (C : Box) (r : ℕ) (y : Vertex) := cube (C.relayCenter r y) r

noncomputable def successBits (C : Box) (r : ℕ) : (m : Model) → Vertex → Finset m.Bit
  | .bond,y => insert (C.entryBit .bond y) (C.seedBox r y).bonds
  | .site,y => (C.seedBox r y).vertices

noncomputable def seedCard (m : Model) (r : ℕ) : ℕ := ((cube 0 r).bits m).card
noncomputable def successCard (m : Model) (r : ℕ) : ℕ := seedCard m r + match m with
  | .bond => 1
  | .site => 0

theorem seedBox_contained (C : Box) (r : ℕ)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (y : Vertex) :
    ∀ x, (C.seedBox r y).Contains x → C.Contains x := C.seed_contained r hw (C.entry y)

end Box

namespace LatticeGraph
variable (G : LatticeGraph)

theorem ContainsBox.mono {B C : Box} (hC : G.ContainsBox C)
    (h : ∀ x, B.Contains x → C.Contains x) : G.ContainsBox B :=
  ⟨(Box.bits_mono .site h).trans hC.1,(Box.bits_mono .bond h).trans hC.2⟩

end LatticeGraph
end CriticalZ3

end OAI


