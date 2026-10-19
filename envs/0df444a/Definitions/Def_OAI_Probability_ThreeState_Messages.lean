-- Prove2me | Definitions.Def_OAI_Probability_ThreeState_Messages
-- name    : OAI_Probability_ThreeState_Messages
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:29:31.114094+00:00
-- url     : https://prove2.me/theorems/44cd1e72-d6d1-4fab-92ee-f3aceadc0b88
-- title:
--   Likelihood messages on three spins and the uninformative message
-- statement:
--   A message on the three spins $\{0,1,2\}$ is a vector $m=(m_0,m_1,m_2)\in\mathbb{R}^3$ with
--   $$
--   m_i\ge0\quad(i=0,1,2),\qquad m_0+m_1+m_2=3 .
--   $$
--   A message records the likelihood of each spin relative to the uniform distribution: $m_i/3$ is a probability vector on the spins. The file defines the following.
--
--   1. **Messages.** The set of messages is a closed and bounded subset of $\mathbb{R}^3$, and hence compact. Every coordinate satisfies $0\le m_i\le3$.
--   2. **The uninformative message** $\mathbf 1=(1,1,1)$. This corresponds to the uniform posterior.
--
--   The compactness is what later permits extracting convergent subsequences of laws of messages. The uninformative message is the fixed point of the message recursion.
--
--   **Formalization Note** `Message` is the subtype `{m : Spin → ℝ // (∀ i, 0 ≤ m i) ∧ ∑ i, m i = 3}`, with a coercion to functions. The file proves the coordinate bounds (`Message.nonneg`, `Message.sum`, `Message.le_three`) and compactness (`message_isCompact`), which gives a `CompactSpace` instance. `uninformative` is the constant function $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeState/Messages.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/Messages.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateSupercritical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic
import Definitions.Def_OAI_Probability_ThreeState_Expectations

namespace OAI

/-! Likelihood messages, compact couplings and subsequential posterior limits. -/

namespace ThreeState
open MeasureTheory

 
abbrev Message := {m : Spin → ℝ // (∀ i, 0 ≤ m i) ∧ ∑ i, m i = 3}

instance : CoeFun Message (fun _ => Spin → ℝ) := ⟨Subtype.val⟩

lemma Message.nonneg (m : Message) (i : Spin) : 0 ≤ m i := m.2.1 i
lemma Message.sum (m : Message) : ∑ i, m i = 3 := m.2.2
lemma Message.le_three (m : Message) (i : Spin) : m i ≤ 3 := by
  calc
    m i ≤ ∑ j, m j := Finset.single_le_sum (fun j _ => Message.nonneg m j) (Finset.mem_univ i)
    _ = 3 := Message.sum m

lemma message_isCompact : IsCompact {m : Spin → ℝ | (∀ i, 0 ≤ m i) ∧ ∑ i, m i = 3} := by
  have hc : IsClosed {m : Spin → ℝ | (∀ i, 0 ≤ m i) ∧ ∑ i, m i = 3} := by
    apply IsClosed.inter
    · have he : {m : Spin → ℝ | ∀ i, 0 ≤ m i} =
          ⋂ i : Spin, {m : Spin → ℝ | 0 ≤ m i} := by ext m; simp
      change IsClosed {m : Spin → ℝ | ∀ i, 0 ≤ m i}
      rw [he]
      exact isClosed_iInter (fun i : Spin => isClosed_le (continuous_const (y := (0:ℝ)))
          (continuous_apply i : Continuous (fun m : Spin → ℝ => m i)))
    · exact isClosed_eq (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const
  apply (isCompact_Icc (a := (fun _ : Spin => (0:ℝ))) (b := fun _ => (3:ℝ))).of_isClosed_subset hc
  intro m hm
  exact ⟨hm.1, fun i => Message.le_three ⟨m,hm⟩ i⟩

instance : CompactSpace Message := isCompact_iff_compactSpace.mp message_isCompact
noncomputable def uninformative : Message := ⟨fun _ => 1, by simp⟩

 
end ThreeState

namespace ThreeState
open MeasureTheory

 
end ThreeState

namespace ThreeState
open MeasureTheory Filter Topology

 

end ThreeState

end OAI


