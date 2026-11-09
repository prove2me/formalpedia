-- Prove2me | Definitions.Def_HypClass1_ellMax
-- name    : HypClass1_ellMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:30:20.0594+00:00
-- url     : https://prove2.me/theorems/f7acef2a-6361-476c-9e56-48e5a6aaff7e
-- title:
--   $\ell(\mathcal B)$, size of a largest minimal element
-- statement:
--   For a family $\mathcal B \subseteq 2^X$, $\ell(\mathcal B)$ is the size of a largest minimal element of $\mathcal B$ (a member none of whose proper subsets lies in $\mathcal B$).
--
--   **Formalization Note** $\ell$ of the empty family is $0$.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §8.4 p.43

import Mathlib

namespace HypClass1

/-- **`ℓ(B)`**, the size of a largest minimal element of `B`. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §8.4 p.43: "Finally, let ℓ(B) be the
size of a largest minimal element of B."

**Formalization Note.** A minimal element is a member `A ∈ B` no proper subset of which is in `B`;
`ℓ(B)` is the largest cardinality of such an `A` (`0` for the empty family). -/
def ellMax {α : Type*} [DecidableEq α] (B : Finset (Finset α)) : ℕ :=
  (B.filter (fun A => ∀ A' ∈ B, A' ⊆ A → A' = A)).sup Finset.card

end HypClass1


