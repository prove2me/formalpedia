-- Prove2me | Definitions.Def_ArbLindbladLearn_Supplement_IsKLocal
-- name    : ArbLindbladLearn_Supplement_IsKLocal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:15:34.104193+00:00
-- url     : https://prove2.me/theorems/6d8bfb7d-f1c9-4226-ab06-7b0f516a1e8c
-- title:
--   $k$-local Lindbladian
-- statement:
--   An $n$-qubit Lindbladian with Hamiltonian coefficients $\{h_a\}$ and dissipative coefficients $\{\gamma_{ab}\}$ is **$k$-local** if every nonzero canonical coordinate has (union) support of size at most $k$:
--   $$h_a\ne0\ \Rightarrow\ |\operatorname{supp}P_a|\le k\quad(a\ne0),\qquad \gamma_{ab}\ne0\ \Rightarrow\ |\operatorname{supp}P_a\cup\operatorname{supp}P_b|\le k\quad(a,b\ne0),$$
--   where $\operatorname{supp}P_a$ is the set of qubits on which the Pauli operator $P_a$ acts nontrivially.
--
--   This is the locality class of Theorems 5.7 and 5.8 and of Theorem 1.2.
--
--   **Formalization Note** The support is the public `support` of a Pauli label.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), §1.1, p.3 (Learning generic k-local Lindbladians)

import Mathlib
import Definitions.Def_ArbLindbladLearn_Coeffs

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn.Supplement

open LindbladTolerant.Testing
open ArbLindbladLearn

/-- `k`-locality of a Lindbladian (§1.1, p.3, "Learning generic k-local Lindbladians"; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…)):
"A Lindbladian is k-local if every nonzero canonical coordinate has union support of size at most
k": every nonzero Hamiltonian coefficient `h_a` (`a ≠ 0`) has `|supp P_a| ≤ k`, and every nonzero
dissipative coefficient `γ_ab` (`a, b ≠ 0`) has `|supp P_a ∪ supp P_b| ≤ k`.

**Formalization Note** `support` is the public set of qubits on which a Pauli label acts
nontrivially. The canonical coordinates are the published coefficients `Coeffs` (Definition 2.6). -/
def IsKLocal {n : ℕ} (k : ℕ) (c : Coeffs n) : Prop :=
  (∀ a : Pauli n, a ≠ 0 → c.h a ≠ 0 → (support a).card ≤ k) ∧
  (∀ a b : Pauli n, a ≠ 0 → b ≠ 0 → c.γ a b ≠ 0 → (support a ∪ support b).card ≤ k)

end ArbLindbladLearn.Supplement


