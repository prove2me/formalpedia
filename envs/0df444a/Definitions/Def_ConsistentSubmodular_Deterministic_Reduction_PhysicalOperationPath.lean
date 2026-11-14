-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_PhysicalOperationPath
-- name    : ConsistentSubmodular_Deterministic_Reduction_PhysicalOperationPath
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:09:38.516945+00:00
-- url     : https://prove2.me/theorems/6ef360f9-9992-45c8-ae19-8da7ffaa6f71
-- title:
--   Single-element operation paths: one-step path, reversal, and adding a forced set
-- statement:
--   Throughout, a *set-operation path* (`SetOperationPath n`) is a finite sequence of subsets $A_0,A_1,\dots,A_L$ of the ground set $[n]$ (with $L$ the `length`), extended constantly after index $L$, in which consecutive sets differ by at most one insertion or deletion; stuttering steps are allowed. The recourse is $\mathrm{rec}(A,B)=|A\triangle B|$.
--
--   - `SetOperationPath.oneStep A B h`: for sets $A,B$ with $\mathrm{rec}(B,A)\le 1$, the path of length $1$ with nodes $A_0=A$ and $A_i=B$ for $i\ge 1$.
--   - `SetOperationPath.reverse P`: the reversed path with the same length $L$ and nodes $A'_i=A_{L-i}$ (natural-number subtraction, so $A'_i=A_0$ for $i\ge L$). It starts at the terminal node of $P$ and ends at the initial node of $P$.
--   - `SetOperationPath.withForced P D`: for a fixed set $D\subseteq[n]$, the path with the same length and nodes $A'_i=D\cup A_i$. Since $|(D\cup A)\triangle(D\cup B)|\le|A\triangle B|$, a fixed forced set adds no operations to a path.
--
--   The file also proves the basic facts that recourse is symmetric and that the endpoints of a reversed path are the swapped endpoints of the original.
--
--   These constructions are the elementary path surgery used when the rounded windows of the deterministic reduction are assembled into physical trajectories that change one element per step: reversal turns an entry path into an exit path, and the forced set is the reserve of heavy elements that stays in every sampled set.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/PhysicalOperationPath.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_OperationPath

noncomputable section

namespace ConsistentSubmodular

variable {n : ℕ}

theorem recourse_comm (A B : Finset (Fin n)) : recourse A B = recourse B A := by
  simp only [recourse, Finset.union_comm]

namespace SetOperationPath

def oneStep (A B : Finset (Fin n)) (h : recourse B A ≤ 1) : SetOperationPath n where
  length := 1
  node i := if i = 0 then A else B
  stationary i hi := by simp [show i ≠ 0 by omega]
  step i := by
    by_cases hi : i = 0
    · simpa [hi] using h
    · simp [hi, recourse]

def reverse (P : SetOperationPath n) : SetOperationPath n where
  length := P.length
  node i := P.node (P.length - i)
  stationary i hi := by simp [Nat.sub_eq_zero_of_le hi]
  step i := by
    rw [recourse_comm]
    by_cases hi : i < P.length
    · have h := P.step (P.length - (i + 1))
      rw [show P.length - (i + 1) + 1 = P.length - i by omega] at h
      exact h
    · simp [Nat.sub_eq_zero_of_le (show P.length ≤ i by omega),
        Nat.sub_eq_zero_of_le (show P.length ≤ i + 1 by omega), recourse]

@[simp] theorem reverse_initial (P : SetOperationPath n) :
    P.reverse.node 0 = P.node P.length := by simp [reverse]

@[simp] theorem reverse_terminal (P : SetOperationPath n) :
    P.reverse.node P.length = P.node 0 := by simp [reverse]

end SetOperationPath

namespace SetOperationPath

open scoped BigOperators

/-- A fixed forced set adds no operations to a sampled path. -/
def withForced (P : SetOperationPath n) (D : Finset (Fin n)) : SetOperationPath n where
  length := P.length
  node i := D ∪ P.node i
  stationary i hi := congrArg (fun A => D ∪ A) (P.stationary i hi)
  step i := by
    have h := recourse_union_le D D (P.node (i + 1)) (P.node i)
    simp only [recourse, Finset.sdiff_self, Finset.union_self, Finset.card_empty, zero_add] at h
    exact h.trans (P.step i)

end SetOperationPath

end ConsistentSubmodular

end


