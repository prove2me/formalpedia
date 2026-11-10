-- Prove2me | Definitions.Def_FatFlat_Hereditary_Patterns
-- name    : FatFlat_Hereditary_Patterns
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:42:13.280308+00:00
-- url     : https://prove2.me/theorems/212a3517-025a-421c-b4a2-8bccb22e693d
-- title:
--   Subdivided cliques $K(r,n)$, webs $W(r,n)$, bipartite patterns $K/W/M(r,n,m)$ and $\ell$-fans
-- statement:
--   - $\mathrm{webOf}(G,P)$: the graph obtained from $G$ by turning the (open) neighbourhood of every vertex of $P$ into a clique; all edges of $G$ are kept.
--   - $K(r,n)$, the **$r$-subdivided clique** of order $n$: every edge of $K_n$ is replaced by a path with exactly $r$ internal vertices (`SparseDisc.subdivide` $(\top:\text{Fin }n)$ with $k\equiv r-1$, which inserts $k+1=r$ vertices). The original vertices are **principal**. Defined by the paper for $r\ge3$; every statement using it assumes $r\ge3$.
--   - $W(r,n)$, the **$r$-web**: $K(r,n)$ with the neighbourhood of every principal vertex turned into a clique.
--   - $K(r,n,m)$, the **$r$-subdivided biclique**: every edge of $K_{n,m}$ subdivided exactly $r$ times; $W(r,n,m)$, the **$r$-biweb**: neighbourhoods of all principal vertices (both sides) made cliques; $M(r,n,m)$, the **$r$-mixweb**: only the neighbourhoods of the principal vertices on the size-$n$ side made cliques.
--   - An **$\ell$-fan** ($\ell\ge1$) with center $c$ and leaf set $X$ is a family of induced paths $P_x=c\,p^1_x\cdots p^\ell_x=x$ of length $\ell$ ($x\in X$), pairwise vertex-disjoint except for $c$, which is either **independent** (no edge between $P_x-c$ and $P_y-c$ for distinct $x,y$) or **linked** (the only such edges are $p^1_xp^1_y$, all present). In Lean a path is a map $\mathrm{Fin}(\ell+1)\to V$ that is injective, starts at $c$, ends at $x$, and whose image has an edge exactly between consecutive indices.
-- source:
--   Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, Fatness and Flatness, arXiv:2607.21474, Definition 3.4 p. 11 (PDF 13), Definition 6.3 p. 17 (PDF 19), Definition 6.5 pp. 18–19 (PDF 20–21). PDF SHA-256: 757d7502abd8762f687daa2125d7908bd129bcf2f5d6d5cc1756b514302adaf1.

import Mathlib
import Definitions.Def_SparseDisc_subdivide

set_option autoImplicit false

namespace FatFlat.Hereditary

/-- `webOf G P`: the graph obtained from `G` by turning the neighbourhood of every vertex of `P`
into a clique: two distinct vertices `x, y` become adjacent when some `p ∈ P` is adjacent to
both; all edges of `G` are kept. -/
def webOf {V : Type} (G : SimpleGraph V) (P : Set V) : SimpleGraph V :=
  G ⊔ SimpleGraph.fromRel (fun x y => ∃ p ∈ P, G.Adj p x ∧ G.Adj p y)

/-- `K(r, n)`, the **`r`-subdivided clique** of order `n` (Definition 3.4, p. 11): every edge of
`K_n` is subdivided exactly `r` times, i.e. replaced by a path with `r` internal vertices
(published `SparseDisc.subdivide` with `k ≡ r − 1`, which inserts `k + 1` vertices). The
**principal vertices** are `Sum.inl i`, `i : Fin n`. The paper defines it for `r ≥ 3`; every
statement using it assumes `3 ≤ r`. -/
noncomputable def subdividedClique (r n : ℕ) :=
  SparseDisc.subdivide (⊤ : SimpleGraph (Fin n)) (fun _ => r - 1)

/-- `W(r, n)`, the **`r`-web** of order `n` (Definition 3.4, p. 11): `K(r, n)` with the
neighbourhood of every principal vertex turned into a clique. -/
noncomputable def web (r n : ℕ) :=
  webOf (subdividedClique r n) (Set.range Sum.inl)

/-- `K(r, n, m)`, the **`r`-subdivided biclique** of order `(n, m)` (Definition 6.5, p. 18):
every edge of `K_{n,m}` (`completeBipartiteGraph (Fin n) (Fin m)`) subdivided exactly `r`
times. Principal vertices are `Sum.inl (Sum.inl i)` (size-`n` side) and `Sum.inl (Sum.inr j)`
(size-`m` side). -/
noncomputable def subdividedBiclique (r n m : ℕ) :=
  SparseDisc.subdivide (completeBipartiteGraph (Fin n) (Fin m)) (fun _ => r - 1)

/-- `W(r, n, m)`, the **`r`-biweb** (Definition 6.5, p. 19): `K(r, n, m)` with the
neighbourhoods of the principal vertices on both sides turned into cliques. -/
noncomputable def biweb (r n m : ℕ) :=
  webOf (subdividedBiclique r n m) (Set.range Sum.inl)

/-- `M(r, n, m)`, the **`r`-mixweb** (Definition 6.5, p. 19): `K(r, n, m)` with only the
neighbourhoods of the principal vertices on the size-`n` side turned into cliques. -/
noncomputable def mixweb (r n m : ℕ) :=
  webOf (subdividedBiclique r n m) (Set.range (fun i : Fin n => Sum.inl (Sum.inl i)))

/-- An **`ℓ`-fan** with center `c` and leaf set `X` in `G` (Definition 6.3, p. 17), given by
paths `P x : Fin (ℓ + 1) → V`, `x ∈ X`: `P x` is an induced path `c = P x 0, P x 1, …,
P x ℓ = x` of length `ℓ` (distinct vertices, adjacent exactly when consecutive); the paths of
distinct leaves share no vertex except `c`; and either (independent) there is no edge between
`P_x − c` and `P_y − c` for distinct leaves `x, y`, or (linked) the only such edges are
`p¹_x p¹_y`, all of which are present. `ℓ ≥ 1`. -/
structure IsFan {V : Type} (G : SimpleGraph V) (ℓ : ℕ) (c : V) (X : Set V)
    (P : V → Fin (ℓ + 1) → V) : Prop where
  one_le : 1 ≤ ℓ
  start : ∀ x ∈ X, P x 0 = c
  finish : ∀ x ∈ X, P x (Fin.last ℓ) = x
  injective : ∀ x ∈ X, Function.Injective (P x)
  induced : ∀ x ∈ X, ∀ i j : Fin (ℓ + 1),
    G.Adj (P x i) (P x j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)
  disjoint : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ∀ i j : Fin (ℓ + 1), i ≠ 0 → j ≠ 0 → P x i ≠ P y j
  indep_or_linked :
    (∀ x ∈ X, ∀ y ∈ X, x ≠ y → ∀ i j : Fin (ℓ + 1), i ≠ 0 → j ≠ 0 →
      ¬ G.Adj (P x i) (P y j)) ∨
    (∀ x ∈ X, ∀ y ∈ X, x ≠ y → ∀ i j : Fin (ℓ + 1), i ≠ 0 → j ≠ 0 →
      (G.Adj (P x i) (P y j) ↔ (i.val = 1 ∧ j.val = 1)))

/-- `G` contains an **`ℓ`-fan with leaf set `X`** (some center, some paths). -/
def HasFan {V : Type} (G : SimpleGraph V) (ℓ : ℕ) (X : Set V) : Prop :=
  ∃ (c : V) (P : V → Fin (ℓ + 1) → V), IsFan G ℓ c X P

end FatFlat.Hereditary


