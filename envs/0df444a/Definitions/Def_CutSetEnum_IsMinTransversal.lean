-- Prove2me | Definitions.Def_CutSetEnum_IsMinTransversal
-- name    : CutSetEnum_IsMinTransversal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:57.265977+00:00
-- url     : https://prove2.me/theorems/bbb89902-77ed-4f1e-9b9c-2e3a6506647f
-- title:
--   Minimal transversal of $\mathcal C$ inside $U$
-- statement:
--   A set $S\subseteq V$ is a **transversal** of $\mathcal C$ if $S\cap Q\ne\emptyset$ for every $Q\in\mathcal C$. A **minimal transversal of $\mathcal C$ inside $U$** is a set $S\subseteq U$ that is a transversal of $\mathcal C$ and no proper subset of which is a transversal: an inclusion-wise minimal subset of $U$ meeting every member of $\mathcal C$.
--
--   This is the set $S$ chosen in the proof of Theorem 2.1, about which Proposition 2.1 and Lemma 2.1 are stated.
--
--   **Formalization Note** Every proper subset of $S$ lies in $U$ again, so minimality among subsets of $U$ is minimality among all proper subsets. If $\mathcal C$ is empty the only minimal transversal is $\emptyset$. The module also defines `IsTransversal`.
-- source:
--   Beideman, Chandrasekaran & Wang, Counting and enumerating optimum cut sets for hypergraph k-partitioning problems for fixed k, arXiv:2204.09178v2, Theorem 2.1, proof, p.10 (PDF 11)

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Definitions.Def_CutSetEnum_Coll

open HyperKCut.Structure

namespace CutSetEnum

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Transversal of the collection `C`.**
Beideman, Chandrasekaran & Wang, arXiv:2204.09178v2, Theorem 2.1, proof, p.10 (PDF 11):
"S ∩ Q ≠ ∅ for all Q ∈ C".

`IsTransversal H U S` says that `S` meets every member of `Coll H U`. -/
def IsTransversal (H : HyperKCut.Structure.Hypergraph V) (U S : Finset V) : Prop :=
  ∀ Q ∈ Coll H U, (S ∩ Q).Nonempty

/-- **Minimal transversal of `C` inside `U`.**
Beideman, Chandrasekaran & Wang, arXiv:2204.09178v2, Theorem 2.1, proof, p.10 (PDF 11): "Let S
be an inclusion-wise minimal subset of U such that S ∩ Q ≠ ∅ for all Q ∈ C, i.e., the set S is
completely contained in U and is a minimal transversal of the collection C."

`IsMinTransversal H U S` says that `S ⊆ U`, that `S` meets every member of `Coll H U`, and that
no proper subset of `S` does.

**Formalization Note.** Every proper subset of `S` is again a subset of `U`, so "inclusion-wise
minimal among subsets of `U`" and "no proper subset is a transversal" coincide. When `C` is empty
the only minimal transversal is `∅`. -/
def IsMinTransversal (H : HyperKCut.Structure.Hypergraph V) (U S : Finset V) : Prop :=
  S ⊆ U ∧ IsTransversal H U S ∧ ∀ S' : Finset V, S' ⊂ S → ¬ IsTransversal H U S'

end CutSetEnum


