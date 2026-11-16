-- Prove2me | Definitions.Def_DetSpectralSparsify_Dense_Supplement_RLevel
-- name    : DetSpectralSparsify_Dense_Supplement_RLevel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:10:45.127246+00:00
-- url     : https://prove2.me/theorems/074ed34a-e353-498c-9246-9362240ca498
-- title:
--   Algorithm 9 ($A_r$) as an execution relation, with block size $\lceil n^{1/(\alpha_{r-1}-1)}\rceil$
-- statement:
--   Algorithm 9 is the recursive self-improvement of §6. Fix the implementation data and conductance sequence $\phi_n$ of Algorithm 8 and an initial exponent $\alpha_0$, and let $\alpha_{r+1}=3-1/(\alpha_r-1)$ as in (40). For a level $r\ge0$, an $n$-vertex multigraph $G$ and an accuracy $\eta$, a run of $A_r(G,\eta)$ returns $H$ as follows.
--
--   1. Aggregate parallel edges and delete self-loops, giving $\bar G$.
--   2. If $n<\eta^{-1}$, return $\bar G$.
--   3. If $r=0$, return the output of a run of Algorithm 8 (dense mode) on $(\bar G,\eta)$.
--   4. Otherwise let $s=\lceil n^{1/(\alpha_{r-1}-1)}\rceil$ and cut the vertices $0,\dots,n-1$ into consecutive blocks $V_1,\dots,V_t$ of $s$ vertices (the last possibly smaller). For $a\le c$, $G_{ac}$ consists of the non-loop edges inside $V_a$ if $a=c$ and of the edges between $V_a$ and $V_c$ if $a<c$. For every pair with $E(G_{ac})\ne\emptyset$, delete the isolated vertices of $G_{ac}$, run $A_{r-1}$ on it with the same $\eta$, and map the result back to the vertices of $G$. Join all these results into $J$, aggregate parallel edges of $J$, and return the output of a run of Algorithm 8 (sparse mode) on $(\bar J,\eta)$.
--
--   The relation is the subject of Theorem 17, which bounds the spectral error, the size and the running time of $A_r$ uniformly in $r$.
--
--   **Formalization Note** Blocks are numbered from $0$; vertex $v$ lies in block $\lfloor v/s\rfloor$, so there are $\lceil n/s\rceil$ blocks. The nonempty block pairs are enumerated in a fixed order; the order does not affect the aggregated union. $\alpha_0$ is a real parameter here; Theorem 17 takes it rational and achievable.
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.28 (recurrence (40)), p.29 (Algorithm 9)

import Definitions.Def_DetSpectralSparsify_Dense_Supplement_WeightedSparsify

set_option autoImplicit false

namespace DetSpectralSparsify.Dense.Supplement

open DetSpectralSparsify.Dense

/-! # Algorithm 9 (`A_r`, p.29) -/

/-- Line 6 at level `r + 1`: the block size `s = ⌈n^{1/(α_r − 1)}⌉`, with `α_r` the exponent
recurrence (40) started at `α₀`. -/
noncomputable def blockSize (α₀ : ℝ) (r n : ℕ) : ℕ :=
  ⌈(n : ℝ) ^ (1 / (alphaSeq α₀ r - 1))⌉₊

/-- Line 7: the vertices `0, …, n-1` are cut into consecutive blocks `V_1, V_2, …` of `s`
vertices, the last possibly smaller; vertex `v` lies in block `⌊v/s⌋` (blocks numbered from `0`). -/
def blockOf (s : ℕ) {n : ℕ} (v : Fin n) : ℕ := v.val / s

/-- The number `t = ⌈n/s⌉` of blocks. -/
def numBlocks (n s : ℕ) : ℕ := (n + s - 1) / s

/-- Line 10: the edge set of `G_{ac}` (`a ≤ c`): the non-loop edges inside block `a` if `a = c`,
the edges between blocks `a` and `c` if `a < c`. -/
def pairEdges {n : ℕ} (G : Multigraph n) (s a c : ℕ) : Finset (Fin G.m) :=
  Finset.univ.filter fun e => ¬ G.IsLoop e ∧
    min (blockOf s (G.src e)) (blockOf s (G.dst e)) = a ∧
    max (blockOf s (G.src e)) (blockOf s (G.dst e)) = c

/-- Lines 9 and 11: the pairs `1 ≤ a ≤ c ≤ t` with `E(G_{ac}) ≠ ∅`. -/
def blockPairs {n : ℕ} (G : Multigraph n) (s : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (numBlocks n s) ×ˢ Finset.range (numBlocks n s)).filter fun p =>
    p.1 ≤ p.2 ∧ (pairEdges G s p.1 p.2).Nonempty

/-- The non-isolated vertices of `G_{ac}`. -/
def pairVertices {n : ℕ} (G : Multigraph n) (s a c : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ e ∈ pairEdges G s a c, G.src e = v ∨ G.dst e = v

/-- Line 12: `G_{ac}` with its isolated vertices deleted, on `Fin |V(G_{ac})|`; its vertex `x`
is the vertex `vertexEmb (pairVertices G s a c) x` of `G`. -/
noncomputable def pairGraph {n : ℕ} (G : Multigraph n) (s a c : ℕ) :
    Multigraph (pairVertices G s a c).card :=
  restrictTo (edgeSub G (pairEdges G s a c)) (pairVertices G s a c)

/-- The `p`-th nonempty block pair. -/
noncomputable def pairAt {n : ℕ} (G : Multigraph n) (s : ℕ) (p : Fin (blockPairs G s).card) :
    ℕ × ℕ :=
  ((blockPairs G s).equivFin.symm p).1

/-- An execution of Algorithm 9: `RLevel D ϕ α₀ r G η H` holds when `A_r(G, η)` can return `H`.
Line 1 aggregates parallel edges and deletes self-loops (`Ḡ`); if `n < η⁻¹` the result is `Ḡ`.
Otherwise, at `r = 0` it is a dense execution of Algorithm 8 on `Ḡ`; at level `r + 1` every
nonempty block-pair graph of `Ḡ` (block size `⌈n^{1/(α_r − 1)}⌉`), with isolated vertices deleted,
is sent to `A_r` with the same `η`, the outputs are mapped back to the vertices of `G` and joined
(`J`), parallel edges of `J` are aggregated, and the result is a sparse execution of Algorithm 8
on `J̄`. Here `D` is the fixed implementation data, `ϕ` the conductance sequence of the expander
decompositions and `α₀` the initial exponent. -/
def RLevel (D : ImplData) (ϕ : ℕ → ℝ) (α₀ : ℝ) :
    ℕ → ∀ {n : ℕ}, Multigraph n → ℝ → Multigraph n → Prop
  | 0, n, G, η, H =>
      ((n : ℝ) < η⁻¹ ∧ H = G.aggregate) ∨
      (η⁻¹ ≤ (n : ℝ) ∧ WeightedSparsify D ϕ G.aggregate η Mode.dense H)
  | r + 1, n, G, η, H =>
      ((n : ℝ) < η⁻¹ ∧ H = G.aggregate) ∨
      (η⁻¹ ≤ (n : ℝ) ∧
        ∃ Js : (p : Fin (blockPairs G.aggregate (blockSize α₀ r n)).card) →
            Multigraph (pairVertices G.aggregate (blockSize α₀ r n)
              (pairAt G.aggregate (blockSize α₀ r n) p).1
              (pairAt G.aggregate (blockSize α₀ r n) p).2).card,
          (∀ p, RLevel D ϕ α₀ r
            (pairGraph G.aggregate (blockSize α₀ r n)
              (pairAt G.aggregate (blockSize α₀ r n) p).1
              (pairAt G.aggregate (blockSize α₀ r n) p).2) η (Js p)) ∧
          WeightedSparsify D ϕ
            (Multigraph.union fun p => mapGraph (vertexEmb _) (Js p)).aggregate η Mode.sparse H)

end DetSpectralSparsify.Dense.Supplement


