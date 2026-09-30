-- Prove2me | Definitions.Def_WangKangXue_SpectralTuran_IsSpectralExtremal
-- name    : WangKangXue_SpectralTuran_IsSpectralExtremal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T14:18:55.129775+00:00
-- url     : https://prove2.me/theorems/fd08d90b-433c-4ae9-b7b7-b75f48a3ed64
-- title:
--   Spectral extremal graph: an F-free n-vertex graph of maximum spectral radius
-- statement:
--   Let $F$ be a graph. A graph $G$ is **$F$-free** if no subgraph of $G$ (not necessarily induced) is isomorphic to $F$. For an $n$-vertex graph $G$ on the vertex set $\{0,1,\dots,n-1\}$, we say that $G$ is a **spectral extremal graph for $F$**, written $G \in \mathrm{Ex}_{sp}(n,F)$, if
--
--   1. $G$ is $F$-free, and
--   2. $\lambda(G') \le \lambda(G)$ for every $F$-free graph $G'$ on the same $n$ vertices,
--
--   where $\lambda$ is the spectral radius (largest adjacency eigenvalue). In the words of the paper, $G$ "has the maximal spectral radius over all $n$-vertex $F$-free graphs".
--
--   **Formalization Note** "$F$-free" is Mathlib's `F.Free G`, i.e. there is no injective graph homomorphism (copy) of $F$ into $G$. Since isomorphic graphs have the same spectral radius, comparing with all $F$-free graphs on the fixed vertex type `Fin n` is the same as comparing with all $n$-vertex $F$-free graphs.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, p. 1 (F-free, Ex_sp(n, F)) and p. 2 (Theorem 1.2: "G has the maximal spectral radius over all n-vertex F-free graphs")

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad

namespace WangKangXue.SpectralTuran

/-- `G ∈ Ex_sp(n, F)`: the `n`-vertex graph `G` is `F`-free (it contains no subgraph isomorphic
to `F`, `F.Free G`) and has the maximum spectral radius `λ` among all `F`-free graphs on the
same `n` vertices. -/
def IsSpectralExtremal {W : Type*} (F : SimpleGraph W) {n : ℕ} (G : SimpleGraph (Fin n)) :
    Prop :=
  F.Free G ∧ ∀ G' : SimpleGraph (Fin n), F.Free G' → specRad G' ≤ specRad G

end WangKangXue.SpectralTuran


