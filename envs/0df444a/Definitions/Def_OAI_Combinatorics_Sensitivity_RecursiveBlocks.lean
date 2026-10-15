-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
-- name    : OAI_Combinatorics_Sensitivity_RecursiveBlocks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:25:47.271743+00:00
-- url     : https://prove2.me/theorems/e2890a3d-ac78-4a5b-b72a-9b2654b626e1
-- title:
--   Lifting a coordinate block to every column of a row
-- statement:
--   In the recursive construction the coordinates of the next level are $([k] \times [r]) \times I$: $kr$ copies of a coordinate set $I$, indexed by a row $i \in [k]$ and a column $c \in [r]$, where $[n] = \{0, \dots, n-1\}$. For a row $i$ and a finite set $B \subseteq I$, the row lift of $B$ places a copy of $B$ in every column of row $i$:
--
--   $$
--   \mathrm{lift}_i(B) = \{ ((i,c), a) : c \in [r],\ a \in B \} \subseteq ([k] \times [r]) \times I .
--   $$
--
--   Thus a coordinate $((j,c), a)$ belongs to $\mathrm{lift}_i(B)$ exactly when $j = i$ and $a \in B$.
--
--   Row lifts propagate the sensitive blocks at the all-zero input from one level of the construction to the next: lifting a pairwise disjoint family of blocks along each of the $k$ rows gives a pairwise disjoint family that is $k$ times larger.
--
--   **Formalization Note** `rowLift i B` is the image of the product of `Finset.univ` (all columns) with `B` under the injective map $(c, a) \mapsto ((i,c), a)$, and `mem_rowLift` is its membership characterization.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/RecursiveBlocks.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/RecursiveBlocks.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SensitivitySeparation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions

namespace OAI

/-! Disjoint zero-input blocks lift to every column of a chosen row. -/

noncomputable section
open scoped Classical

namespace Paper320

def rowLift {k r : ℕ} {I : Type} (i : Fin k) (B : Finset I) :
    Finset ((Fin k × Fin r) × I) :=
  (Finset.univ.product B).map
    ⟨fun p : Fin r × I => ((i, p.1), p.2), by
      intro p q hpq
      exact Prod.ext (congrArg (fun z => z.1.2) hpq) (congrArg (fun z : (Fin k × Fin r) × I => z.2) hpq)⟩

@[simp] theorem mem_rowLift {k r : ℕ} {I : Type} (i : Fin k) (B : Finset I)
    (p : (Fin k × Fin r) × I) : p ∈ rowLift (r := r) i B ↔ p.1.1 = i ∧ p.2 ∈ B := by
  rcases p with ⟨⟨j, c⟩, a⟩
  unfold rowLift
  rw [Finset.mem_map]
  constructor
  · rintro ⟨⟨c', b⟩, hb, hp⟩
    change ((i, c'), b) = ((j, c), a) at hp
    cases hp
    exact ⟨rfl, (Finset.mem_product.mp hb).2⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨(c, a), Finset.mem_product.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩

end Paper320

end

end OAI


