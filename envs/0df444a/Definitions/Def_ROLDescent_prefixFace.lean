-- Prove2me | Definitions.Def_ROLDescent_prefixFace
-- name    : ROLDescent_prefixFace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:01.56626+00:00
-- url     : https://prove2.me/theorems/1cbb54f0-7f9c-4184-8229-c63da1aaada3
-- title:
--   The $k$-th node $\tau_k$ of a path
-- statement:
--   A path of $j$ steps from the root $\emptyset$ adds one vertex at a time; it is recorded by the sequence $p = (p_0, \dots, p_{j-1})$ of added vertices. Its $k$-th node is the set of the first $k$ added vertices,
--
--   $$\tau_k = \{p_0, \dots, p_{k-1}\}, \qquad \tau_0 = \emptyset .$$
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1, p.29 (PDF 29)

import Mathlib

namespace ROLDescent

/-- **The k-th node of a path**, `τ_k`. Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1, p.29 (PDF 29): "A
root-to-stop path p = (τ₀ = ∅, τ₁, …, τ_{d−1}) records an ordered sequence of legal additions".

**Formalization Note** A path of `j` steps is the sequence `p : Fin j → V` of the vertices it adds;
`prefixFace p k` is the set of the first `k` added vertices, i.e. τ_k (so `prefixFace p 0 = ∅`). -/
def prefixFace {V : Type*} [DecidableEq V] {j : ℕ} (p : Fin j → V) (k : ℕ) : Finset V :=
  (Finset.univ.filter (fun m : Fin j => (m : ℕ) < k)).image p

end ROLDescent


