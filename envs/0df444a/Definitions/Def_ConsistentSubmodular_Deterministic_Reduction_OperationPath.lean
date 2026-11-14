-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_OperationPath
-- name    : ConsistentSubmodular_Deterministic_Reduction_OperationPath
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:08:39.961366+00:00
-- url     : https://prove2.me/theorems/c2e9307b-ba86-480c-ad33-1db57109652d
-- title:
--   Set operation paths: insertions and deletions one at a time, constant path, concatenation
-- statement:
--   A set operation path records a finite list of physical insertions and deletions of elements.
--
--   - `ConsistentSubmodular.SetOperationPath` $n$: a structure with a length $\ell \in \mathbb{N}$ and nodes $A_i \subseteq \{0,\dots,n-1\}$ for every $i \in \mathbb{N}$ such that (a) the path is stationary after its endpoint, $A_i = A_\ell$ for all $i \ge \ell$; and (b) consecutive nodes differ by at most one element, $|A_{i+1} \triangle A_i| \le 1$ for every $i$. Stuttering steps ($A_{i+1}=A_i$) are permitted.
--   - `SetOperationPath.constant` $(A)$: the path of length $0$ with all nodes equal to $A$.
--   - `SetOperationPath.append` $(P, Q, h)$: for paths $P,Q$ with $P_\ell = Q_0$ (the hypothesis $h$), the concatenation of length $\ell_P + \ell_Q$ whose $i$-th node is $P_i$ for $i \le \ell_P$ and $Q_{i - \ell_P}$ for $i \ge \ell_P$.
--
--   The file also proves the basic facts: the recourse between nodes $a \le b$ is at most $b-a$ (by the triangle inequality); the concatenation has length $\ell_P+\ell_Q$, starts at $P_0$ and ends at $Q_{\ell_Q}$.
--
--   Operation paths model the physical realization of a change of the maintained set as a sequence of unit-recourse steps. They are the building blocks of the block schedules in the reduction from consistency to certificates (Section 3.2).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/OperationPath.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SchedulingBasics

noncomputable section

namespace ConsistentSubmodular

/-- A finite list of physical insertions and deletions, extended constantly
after its endpoint. Stuttering steps are permitted. -/
structure SetOperationPath (n : ℕ) where
  length : ℕ
  node : ℕ → Finset (Fin n)
  stationary : ∀ i, length ≤ i → node i = node length
  step : ∀ i, recourse (node (i + 1)) (node i) ≤ 1

namespace SetOperationPath

variable {n : ℕ} (P : SetOperationPath n)

theorem interval_recourse (a d : ℕ) : recourse (P.node (a + d)) (P.node a) ≤ d := by
  induction d with
  | zero => simp [recourse]
  | succ d ih =>
    have ht := recourse_triangle (P.node (a + (d + 1))) (P.node (a + d)) (P.node a)
    have hs := P.step (a + d)
    rw [Nat.add_assoc] at hs
    omega

theorem recourse_le_difference {a b : ℕ} (hab : a ≤ b) :
    recourse (P.node b) (P.node a) ≤ b - a := by
  simpa [Nat.add_sub_of_le hab] using P.interval_recourse a (b - a)

def constant (A : Finset (Fin n)) : SetOperationPath n where
  length := 0
  node := fun _ => A
  stationary := by intros; rfl
  step := by intro; simp [recourse]

def append (Q : SetOperationPath n) (hjoin : P.node P.length = Q.node 0) :
    SetOperationPath n := by
  let seq := fun i => if i ≤ P.length then P.node i else Q.node (i - P.length)
  have hbefore (i : ℕ) (hi : i ≤ P.length) : seq i = P.node i := by simp [seq, hi]
  have hafter (i : ℕ) (hi : P.length ≤ i) : seq i = Q.node (i - P.length) := by
    by_cases he : i = P.length
    · subst i
      simp [seq, hjoin]
    · simp [seq, show ¬i ≤ P.length by omega]
  refine {
    length := P.length + Q.length
    node := seq
    stationary := ?_
    step := ?_ }
  · intro i hi
    rw [hafter i (by omega), hafter (P.length + Q.length) (by omega)]
    simp only [Nat.add_sub_cancel_left]
    exact Q.stationary _ (by omega)
  · intro i
    by_cases hi : i < P.length
    · rw [hbefore (i + 1) (by omega), hbefore i (by omega)]
      exact P.step i
    · rw [hafter (i + 1) (by omega), hafter i (by omega)]
      rw [show i + 1 - P.length = (i - P.length) + 1 by omega]
      exact Q.step _

@[simp] theorem append_length (Q : SetOperationPath n) (hjoin) :
    (P.append Q hjoin).length = P.length + Q.length := rfl

@[simp] theorem append_initial (Q : SetOperationPath n) (hjoin) :
    (P.append Q hjoin).node 0 = P.node 0 := by simp [append]

@[simp] theorem append_terminal (Q : SetOperationPath n) (hjoin) :
    (P.append Q hjoin).node (P.length + Q.length) = Q.node Q.length := by
  by_cases hQ : Q.length = 0
  · simp [append, hQ, hjoin]
  · simp [append, show ¬P.length + Q.length ≤ P.length by omega]

end SetOperationPath

end ConsistentSubmodular

end


