-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_FixedCoordinates
-- name    : OAI_Combinatorics_Sensitivity_FixedCoordinates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:46:28.537475+00:00
-- url     : https://prove2.me/theorems/fa2572e0-579d-46a0-b68d-817e8992a39b
-- title:
--   Functions with prescribed values on a set of coordinates correspond to functions on its complement
-- statement:
--   Let $\alpha$ and $\beta$ be finite sets, let $s \subseteq \alpha$, and let $v : \alpha \to \beta$ be a fixed function. The functions $g : \alpha \to \beta$ that agree with $v$ on $s$ are in bijection with the functions on the complement $\alpha \setminus s$:
--   $$
--   \{\, g : \alpha \to \beta \ :\ g(i) = v(i) \text{ for all } i \in s \,\} \;\longleftrightarrow\; \beta^{\,\alpha \setminus s} .
--   $$
--   The forward map restricts $g$ to $\alpha \setminus s$; the inverse map sends $h : \alpha \setminus s \to \beta$ to the function that equals $v(i)$ for $i \in s$ and $h(i)$ for $i \notin s$.
--
--   Consequently, exactly $|\beta|^{|\alpha| - |s|}$ functions $\alpha \to \beta$ take prescribed values on $s$. This exact count is used to count the edge labelings of a tournament that are target-constant on a given vertex set, since these are precisely the labelings with prescribed values on the internal edges of that set.
--
--   **Formalization Note** The definition is the equivalence `fixedCoordinatesEquiv s v` from the subtype `{f : α → β // ∀ i ∈ s, f i = v i}` to functions on the subtype `{i : α // i ∉ s}`; it uses `DecidableEq α` to form the piecewise inverse. The counting statement `card_fixedCoordinates` is proved separately. The two private lemmas `dite_eq_left` and `dite_eq_right` restate `dif_pos` and `dif_neg` for the local simplifications.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/FixedCoordinates.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/FixedCoordinates.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

/-! Exact finite counting when a specified set of coordinates is fixed. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]

def fixedCoordinatesEquiv (s : Finset α) (v : α → β) :
    {f : α → β // ∀ i ∈ s, f i = v i} ≃ ({i : α // i ∉ s} → β) where
  toFun f i := f.val i.val
  invFun f := ⟨fun i => if h : i ∈ s then v i else f ⟨i,h⟩, by
    intro i hi
    simp only [dite_eq_left hi]⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · simp only [dite_eq_left hi]
      exact (f.property i hi).symm
    · simp only [dite_eq_right hi]
  right_inv f := by
    funext i
    simp only [dite_eq_right i.property]

end Paper320

end

end OAI


