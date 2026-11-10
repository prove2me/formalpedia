-- Prove2me | Definitions.Def_RandTreeUniv_IsExchangeableLaw
-- name    : RandTreeUniv_IsExchangeableLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:13.516304+00:00
-- url     : https://prove2.me/theorems/9d2330ef-9b39-4f2f-ac15-e985d8d81eec
-- title:
--   Exchangeable random graph on $[n]$
-- statement:
--   A random graph on the vertex set $[n]$ is described by a probability mass function $\mu$ on the finitely many graphs with vertex set $[n]$: $\mu(G)\ge0$ and $\sum_G\mu(G)=1$. The random graph is **exchangeable** if relabelling the vertices does not change its law: for every permutation $\sigma\in S_n$ and every graph $G$,
--
--   $$
--   \mu(\sigma(G))=\mu(G),
--   $$
--
--   where $\sigma(G)$ is the image of $G$ under $\sigma$. For an event $E$ (a property of graphs), $\mathbb P_\mu(E)=\sum_{G:\,E(G)}\mu(G)$.
--
--   The binomial random graph $G(n,p)$ is exchangeable. Lemma 3.2 assumes only exchangeability, which is what lets it be applied to the random graph conditioned on partial information.
--
--   **Formalization Note** Vertices are $\{0,\dots,n-1\}$; the module also defines $\mathbb P_\mu$ as `lawProb`.
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), Lemma 3.2 and footnote 4, p.14 (PDF 15)

import Mathlib

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- An exchangeable random graph on `[n]` (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), Lemma 3.2 and footnote 4, p.14 (PDF 15)):
"for any permutation `σ ∈ S_n` acting on `[n]`, the image of `G` under `σ` and `G` itself are
identically distributed". The law is a probability mass function `μ` on the finitely many graphs
on `Fin n` that is invariant under relabelling the vertices.

**Formalization Note** Vertices `[n]` are `Fin n` (0-based). `G.map σ` is the image of `G`
under the vertex permutation `σ`. -/
def IsExchangeableLaw {n : ℕ} (μ : SimpleGraph (Fin n) → ℝ) : Prop :=
  (∀ G, 0 ≤ μ G) ∧ (∑ G, μ G = 1) ∧
    ∀ (σ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)), μ (G.map σ.toEmbedding) = μ G

/-- The probability `P_μ(E)` of an event `E` (a property of graphs on `Fin n`) under a
probability mass function `μ` on graphs. -/
noncomputable def lawProb {n : ℕ} (μ : SimpleGraph (Fin n) → ℝ) (E : SimpleGraph (Fin n) → Prop) :
    ℝ :=
  ∑ G, if E G then μ G else 0

end RandTreeUniv


