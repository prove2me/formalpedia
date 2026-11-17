-- Prove2me | Definitions.Def_PolyContract_Supplement_IsLaminarDescription
-- name    : PolyContract_Supplement_IsLaminarDescription
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:58:33.868536+00:00
-- url     : https://prove2.me/theorems/d38c4655-9966-496a-9cb4-5f4703d32ffc
-- title:
--   Laminar description of a polymatroid and its height
-- statement:
--   A polymatroid $(E,f)$ is **laminar** if it has a description
--   $$P^{(+)}(f)=\{x\ge0: x(L)\le f(L)\text{ for }L\in\mathcal L\}$$
--   by a family $\mathcal L$ of nonempty constraint sets of which any two are disjoint or nested. The **height** $h$ of $\mathcal L$ is the number of sets in a longest chain of $\mathcal L$ (a subfamily totally ordered by inclusion).
--
--   The bound of Theorem B.19 on the number of breakpoints is stated in terms of $n$, $|\mathcal L|$ and $h$.
--
--   **Formalization Note** $\mathcal L$ is a finite set of finite subsets of the ground set, and the description is the equality of the two polyhedra; $f$ remains the instance's own rank function.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), §3, p.9 (PDF p.10); App. B.8, p.44 (PDF p.45)

import Mathlib
import Definitions.Def_PolyContract_IsRankFunction

set_option autoImplicit false

namespace PolyContract.Supplement

/-- `L` is a **laminar description** of the polymatroid `(E, f)` (Klimm, Lippke, Warode,
arXiv:2611.04934, version of November 3, 2026, sha256 18cfc0a5…, §3, p.9, and App. B.8, p.44):
"`P(+)(f) = {x ≥ 0 : x(L) ≤ f(L) for L ∈ L}` with nonempty constraint sets that are pairwise
disjoint or nested".

**Formalization Note** `L` is a finite family of subsets of the ground set `ι`; `f` stays the rank
function of the instance, and the description is the stated equality of polyhedra. -/
def IsLaminarDescription {ι : Type} (f : Finset ι → ℝ) (L : Finset (Finset ι)) : Prop :=
  (∀ A ∈ L, A.Nonempty) ∧ (∀ A ∈ L, ∀ B ∈ L, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A) ∧
    indepPoly f = {x | (∀ e, 0 ≤ x e) ∧ ∀ A ∈ L, setSum x A ≤ f A}

open Classical in
/-- The **height** `h` of a laminar family `L` (arXiv:2611.04934, §3, p.9): "the number of sets in a
longest chain in `L`", i.e. the largest cardinality of a subfamily totally ordered by inclusion. -/
noncomputable def laminarHeight {ι : Type} (L : Finset (Finset ι)) : ℕ :=
  (L.powerset.filter fun C : Finset (Finset ι) => IsChain (· ⊆ ·) (↑C : Set (Finset ι))).sup
    Finset.card

end PolyContract.Supplement


