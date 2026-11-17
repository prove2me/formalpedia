-- Prove2me | Definitions.Def_AvgCaseTI_Supplement_orthIsos
-- name    : AvgCaseTI_Supplement_orthIsos
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:30:40.606337+00:00
-- url     : https://prove2.me/theorems/1010c7ad-6dd9-4312-b594-a41ff5482149
-- title:
--   Orthogonal matrices and the set of orthogonal isomorphisms of 3-tensors
-- statement:
--   The **orthogonal group** is $\mathrm O(n,q)=\{Q\in\mathrm{GL}(n,q):Q^tQ=I_n\}$. For $Q_1,Q_2,Q_3$ and an $n\times n\times n$ array $A$, $(Q_1\otimes Q_2\otimes Q_3)\cdot A$ is the array
--   $$
--   b_{i,j,k}=\sum_{i',j',k'}(Q_1)_{ii'}(Q_2)_{jj'}(Q_3)_{kk'}\,a_{i',j',k'}.
--   $$
--   The **set of orthogonal isomorphisms** from $A$ to $B$ is
--   $$
--   \mathrm{Isos}(A,B)=\{(Q_1,Q_2,Q_3)\in\mathrm O(n,q)^3: B=(Q_1\otimes Q_2\otimes Q_3)\cdot A\},
--   $$
--   which is empty exactly when $A$ and $B$ are not orthogonally isomorphic. It is the object computed by the algorithm of Theorem 5.6.
--
--   **Formalization Note** $Q^tQ=I$ already forces $Q$ to be invertible.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), §5.1, p.28 (PDF p.30); §2.3, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_AvgCaseTI_Tensor3

set_option autoImplicit false

namespace AvgCaseTI.Supplement

open AvgCaseTI Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- **Orthogonal matrices**, `O(n, q) = {Q ∈ GL(n, q) : QᵗQ = I_n}` (§5.1, p.28, PDF p.30).
`QᵗQ = I` already forces `Q` to be invertible. -/
def IsOrth (Q : Matrix (Fin n) (Fin n) K) : Prop := Qᵀ * Q = 1

/-- The action `(Q1 ⊗ Q2 ⊗ Q3) · A` on 3-way arrays, with the §2.3 convention (p.15, PDF p.17):
`b_{i,j,k} = Σ_{i',j',k'} (Q1)_{i i'} (Q2)_{j j'} (Q3)_{k k'} a_{i',j',k'}`. -/
def act3 (Q1 Q2 Q3 : Matrix (Fin n) (Fin n) K) (A : Tensor3 K n) : Tensor3 K n :=
  fun i j k => ∑ i' : Fin n, ∑ j' : Fin n, ∑ k' : Fin n, Q1 i i' * Q2 j j' * Q3 k k' * A i' j' k'

/-- **The set of orthogonal isomorphisms from `A` to `B`.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), §5.1, p.28 (PDF p.30): "The goal is to determine whether there exist orthogonal matrices
Q1, Q2, Q3 ∈ O(n, q) such that B = (Q1 ⊗ Q2 ⊗ Q3) · A".

`orthIsos A B = {(Q1, Q2, Q3) ∈ O(n, q)³ : B = (Q1 ⊗ Q2 ⊗ Q3) · A}`; it is empty exactly when `A` and
`B` are not orthogonally isomorphic. -/
def orthIsos (A B : Tensor3 K n) :
    Set (Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K) :=
  {t | IsOrth t.1 ∧ IsOrth t.2.1 ∧ IsOrth t.2.2 ∧ B = act3 t.1 t.2.1 t.2.2 A}

end AvgCaseTI.Supplement


