-- Prove2me | Definitions.Def_ROLDescent_rootPaths
-- name    : ROLDescent_rootPaths
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:46.125646+00:00
-- url     : https://prove2.me/theorems/f2850475-05f4-4e2a-b4a8-cbafb3710806
-- title:
--   Root paths of $j$ steps; $\mathcal P_{\mathrm{stop}}$
-- statement:
--   A **root path** of $j$ steps in a simplicial complex $X$ is a sequence of $j$ distinct vertices $p_0, \dots, p_{j-1}$ such that every prefix set $\tau_k = \{p_0,\dots,p_{k-1}\}$, $0 \le k \le j$, is a face: an ordered sequence of legal additions $\emptyset = \tau_0 \to \tau_1 \to \dots \to \tau_j$. For a pure complex with facet size $d$, the root-to-stop paths $\mathcal P_{\mathrm{stop}}$ are the root paths of $d-1$ steps, with endpoint $t(p) = \tau_{d-1}$.
--
--   Different orders reaching the same face are different paths.
--
--   **Formalization Note** A step $\tau \to \tau i$ is determined by the added vertex $i \in N_\tau$, so a path is its vertex sequence `Fin j → V`.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1, p.29 (PDF 29)

import Mathlib
import Definitions.Def_ROLDescent_prefixFace

namespace ROLDescent

/-- **Root paths of j steps**; `rootPaths X (d − 1)` is `P_stop`. Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Section 5.1,
p.29 (PDF 29): "The ROL label graph has faces as nodes and legal inclusions as arrows: … a : τ →
τi (i ∈ N_τ). … A root-to-stop path p = (τ₀ = ∅, τ₁, …, τ_{d−1}) records an ordered sequence of
legal additions, with endpoint t(p) = τ_{d−1}. Different paths can reach the same node."

**Formalization Note** A step τ → τi is determined by the added vertex `i ∈ N_τ` (there are no
parallel steps), so a path of `j` steps is an injective vertex sequence `p : Fin j → V` all of whose
prefix sets `prefixFace p k` (k ≤ j) are faces. Two orders reaching the same face are different
paths, as the paper requires. -/
def rootPaths {V : Type*} [Fintype V] [DecidableEq V] (X : Finset (Finset V)) (j : ℕ) :
    Finset (Fin j → V) :=
  Finset.univ.filter (fun p => Function.Injective p ∧ ∀ k ≤ j, prefixFace p k ∈ X)

end ROLDescent


