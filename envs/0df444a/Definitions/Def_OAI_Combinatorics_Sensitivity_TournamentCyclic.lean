-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCyclic
-- name    : OAI_Combinatorics_Sensitivity_TournamentCyclic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:49:56.645384+00:00
-- url     : https://prove2.me/theorems/a8107a7c-1281-42f0-ba8f-2e4f4f0ea611
-- title:
--   The cyclic regular tournament on $2a+1$ vertices
-- statement:
--   Let $a \in \mathbb{N}$ and identify the vertex set $\{0, 1, \dots, 2a\}$ with the integers modulo $2a+1$. For vertices $i, j$ let $(j - i) \bmod (2a+1) \in \{0, \dots, 2a\}$ denote the residue of $j - i$.
--
--   1. **Cyclic tournament.** The cyclic tournament on $2a + 1$ vertices has an edge from $i$ to $j$ exactly when $j$ is one of the next $a$ vertices after $i$ around the cycle:
--   $$
--   i \to j \iff 1 \le (j - i) \bmod (2a+1) \le a .
--   $$
--   There are no loops, and for $i \ne j$ the residues of $j - i$ and $i - j$ are nonzero and add up to $2a+1$, so exactly one of them is at most $a$; hence exactly one of $i \to j$ and $j \to i$ holds, and this is a tournament.
--
--   2. **Out-degrees.** Every vertex $i$ has exactly $a$ out-neighbours, namely $i+1, \dots, i+a$ modulo $2a+1$.
--
--   3. **Regular cyclic tournament with parameter $M$.** For $M \in \mathbb{N}$, taking $a = M^2$ gives a tournament on $2M^2+1$ vertices in which every vertex has out-degree exactly $M^2$, i.e. a regular tournament with parameter $M$.
--
--   This is the concrete regular tournament used in the construction separating block sensitivity from sensitivity: each level of the construction has $k = 2M^2+1$ rows, and the common out-degree $M^2$ is the factor multiplying the 0-side profile in the recurrence for sensitivity on accepted inputs.
--
--   **Formalization Note** The definitions are `cyclicTournament a : Tournament (2*a+1)`, whose adjacency is `0 < (j-i).val ∧ (j-i).val ≤ a` with subtraction in `Fin (2*a+1)` (that is, modulo $2a+1$), the out-degree theorem `cyclicTournament_outdegree`, and `regularCyclicTournament M`, which packages `cyclicTournament (M^2)` with this out-degree as a `RegularTournament M`. The private lemma `ite_eq_right` restates `if_neg` for a local rewrite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/TournamentCyclic.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/TournamentCyclic.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
import Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_OAI_Combinatorics_Sensitivity_Or
import Definitions.Def_OAI_Combinatorics_Sensitivity_Reindex
import Definitions.Def_OAI_Combinatorics_Sensitivity_Construction
import Definitions.Def_OAI_Combinatorics_Sensitivity_FixedCoordinates
import Definitions.Def_OAI_Combinatorics_Sensitivity_LabelingEvents

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! The literal regular tournament on an odd cyclic set. -/

noncomputable section
open scoped Classical

namespace Paper320

def cyclicTournament (a : ℕ) : Tournament (2*a+1) where
  Adj i j := 0 < (j-i).val ∧ (j-i).val ≤ a
  loopless i := by simp
  edge_compl := by
    intro i j hij
    have hδ : j-i ≠ 0 := sub_ne_zero.mpr hij.symm
    have hp : 0 < (j-i).val := Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hδ)
    have hb := (j-i).isLt
    have hn : (i-j).val = 2*a+1-(j-i).val := by
      rw [← neg_sub j i, Fin.val_neg, ite_eq_right hδ]
    change (0 < (j-i).val ∧ (j-i).val ≤ a) ↔ ¬ (0 < (i-j).val ∧ (i-j).val ≤ a)
    rw [hn]
    omega

theorem cyclicTournament_outdegree (a : ℕ) (i : Fin (2*a+1)) :
    (Finset.univ.filter ((cyclicTournament a).Adj i)).card = a := by
  let z : Fin (2*a+1) := 0
  let b : Fin (2*a+1) := ⟨a, by omega⟩
  have he : (Finset.Ioc z b).card =
      (Finset.univ.filter ((cyclicTournament a).Adj i)).card :=
    Finset.card_equiv (Equiv.addLeft i) (by
      intro x
      simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_univ, true_and]
      change (0 < x.val ∧ x.val ≤ a) ↔
        (0 < ((i+x)-i).val ∧ ((i+x)-i).val ≤ a)
      rw [add_sub_cancel_left])
  rw [← he, Fin.card_Ioc]
  change a - 0 = a
  exact Nat.sub_zero a

def regularCyclicTournament (M : ℕ) : RegularTournament M where
  toTournament := cyclicTournament (M^2)
  outdegree := cyclicTournament_outdegree (M^2)

end Paper320

end

end OAI


