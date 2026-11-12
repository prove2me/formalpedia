-- Prove2me | Definitions.Def_DirKECC1549_Main_Alg3
-- name    : DirKECC1549_Main_Alg3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:42:22.134049+00:00
-- url     : https://prove2.me/theorems/30cfb15a-25b2-46bd-9434-5a26b5f71f34
-- title:
--   §2 and §3.2–3.3 — partitions, common refinement, unit flows, residual graphs, and Algorithm 3 as a run relation
-- statement:
--   A partition of $V=\{0,\dots,n-1\}$ is represented by its equivalence relation. Following p.10, a partition $P$ preserves the $k$-edge-connected components of $G$ when every $C\in P_k(G)$ lies in a block of $P$; $P$ refines $Q$ when every block of $P$ lies in a block of $Q$; and the common refinement $P\wedge Q=\{B\cap C: B\in P, C\in Q, B\cap C\ne\emptyset\}$ relates two vertices exactly when both $P$ and $Q$ do. We write $\varepsilon_k=2^{-(k-1)}$ (a real number).
--
--   The guarantees of Lemma 1 on an output $P$ for input $P_{k-1}$ are: $P$ is a partition refining $P_{k-1}$, it preserves every $k$-edge-connected component of $G$, and it separates every pair that is $(k-1)$-edge-connected but not $(k,\Delta)$-connected. The guarantees of Lemma 2 on $Z$ (graph $D$, root $r$) are: $Z\subseteq V\setminus\{r\}$, $|Z|<(k-1)m/\Delta$, and $S\cap Z\ne\emptyset$ for every $S\subseteq V\setminus\{r\}$ with $\mathrm{out}_D(S)<k$ and $\mathrm{vol}_D(S)>\Delta$.
--
--   A set of edges $F$ is an integral unit-capacity $z\to r$ flow of value $q$ when at every vertex the number of $F$-edges leaving it minus the number entering it is $q$ at $z$, $-q$ at $r$ and $0$ elsewhere. Its residual graph reverses exactly the edges of $F$; after $q$ augmentations of Ford–Fulkerson the reversed edges are the edges flipped an odd number of times, which form such a flow.
--
--   Algorithm 3, $\mathrm{kEdgeConnectedComponents}(G,k)$, is formalized as the relation "$P$ is a possible output on $(G,k)$", defined by its lines:
--
--   1. if $k=1$ or $n=1$, the output is the partition into strongly connected components;
--   2. otherwise, if $G$ is not strongly connected, the output is the union, over the strongly connected components $S$, of outputs on $G[S]$ with the same $k$;
--   3. otherwise, with
--   $$\Delta=\max\{k-1,\lceil m/n^{\varepsilon_k}\rceil\},$$
--   take an output $P_{k-1}$ on $(G,k-1)$, a partition $P$ meeting Lemma 1's guarantees, a root $r$ and sets $Z_G,Z_{G^R}$ meeting Lemma 2's guarantees in $G$ and $G^R$; for each $D\in\{G,G^R\}$ and $z\in Z_D$ let $q=\min\{k,\lambda_D(z,r)\}$ and $H$ the residual graph of a value-$q$ flow from $z$ to $r$ in $D$; whenever $q<k$, refine $P$ by an output on $(H,k-q)$. The output is the resulting common refinement.
--
--   The relation is nondeterministic exactly where the paper's algorithm is: the root, the outputs of Lemmas 1 and 2, and the augmenting paths.
--
--   **Formalization Note** The run relation is an inductive predicate; Lemma 4 quantifies over all its outputs, and Lemma 5 asserts that one program's output is one of them.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 2, p.10; Section 3.2, pp.13–16; Algorithm 3 and Section 3.3, p.17

import Mathlib
import Definitions.Def_DirKECC1549_Main_Graph

set_option autoImplicit false

noncomputable section

open Classical Finset

namespace DirKECC1549.Main

/-!
# Partitions, residual graphs and Algorithm 3 as a run relation (§2, p.10; §3.2–3.3, pp.13–17)

A partition of `V = Fin n` is represented by its equivalence relation `P : Fin n → Fin n → Prop`
(`P u v` iff `u, v` lie in the same block). The common refinement `P ∧ Q` of p.10 is the
conjunction of the relations, and refining by a vertex set `A` intersects with "same side of `A`".
-/

variable {n m : ℕ}

/-- `ε_k = 2^{-(k-1)}` (a real number). -/
def eps (k : ℕ) : ℝ := 1 / 2 ^ (k - 1)

/-- `P` preserves the `k`-edge-connected components of `G` (p.10): every `C ∈ P_k(G)` lies in a
block of `P`. -/
def PreservesKECC (k : ℕ) (G : Fin m → Fin n × Fin n) (P : Fin n → Fin n → Prop) : Prop :=
  ∀ u v, KEdgeConnected k G u v → P u v

/-- `P` is a refinement of `Q`: every block of `P` lies in a block of `Q`. -/
def Refines (P Q : Fin n → Fin n → Prop) : Prop := ∀ u v, P u v → Q u v

/-- The common refinement `P ∧ Q = {B ∩ C : B ∈ P, C ∈ Q, B ∩ C ≠ ∅}` (p.10). -/
def commonRefinement (P Q : Fin n → Fin n → Prop) : Fin n → Fin n → Prop :=
  fun u v => P u v ∧ Q u v

/-- The guarantees of Lemma 1 (p.11) on an output partition `P`, given the input partition
`Pk1` (meant to be `P_{k-1}(G)`): `P` is a partition refining `Pk1`, it preserves every
`k`-edge-connected component of `G`, and it separates every pair of vertices that are
`(k-1)`-edge-connected but not `(k, Δ)`-connected. -/
def Lemma1Guarantee (G : Fin m → Fin n × Fin n) (k Δ : ℕ) (Pk1 P : Fin n → Fin n → Prop) :
    Prop :=
  Equivalence P ∧ Refines P Pk1 ∧ PreservesKECC k G P ∧
    ∀ u v, KEdgeConnected (k - 1) G u v → ¬ KDeltaConnected k Δ G u v → ¬ P u v

/-- The guarantees of Lemma 2 (p.14) on a set `Z` for the graph `D`, root `r`, parameters
`k, Δ`: `Z ⊆ V \ {r}`, `|Z| < (k-1)m/Δ`, and `Z` meets every `S ⊆ V \ {r}` with
`out_D(S) < k` and `vol_D(S) > Δ`. -/
def Lemma2Guarantee (D : Fin m → Fin n × Fin n) (r : Fin n) (k Δ : ℕ) (Z : Finset (Fin n)) :
    Prop :=
  r ∉ Z ∧ (Z.card : ℝ) < ((k : ℝ) - 1) * m / Δ ∧
    ∀ S : Finset (Fin n), r ∉ S → outCount D S < k → Δ < vol D S → (S ∩ Z).Nonempty

/-- `F` is the support of an integral unit-capacity `z → r` flow of value `q` in `D`: at every
vertex, (edges of `F` leaving it) − (edges of `F` entering it) is `q` at `z`, `−q` at `r`,
`0` elsewhere. This is the set of edges reversed an odd number of times by `q` rounds of
Ford–Fulkerson augmentation. -/
def IsUnitFlow (D : Fin m → Fin n × Fin n) (F : Finset (Fin m)) (z r : Fin n) (q : ℕ) : Prop :=
  ∀ x : Fin n,
    ((F.filter (fun e => (D e).1 = x)).card : ℤ) - (F.filter (fun e => (D e).2 = x)).card =
      (if x = z then (q : ℤ) else 0) - (if x = r then (q : ℤ) else 0)

/-- The residual graph: the edges of `F` reversed, all others kept; same vertices, same edge ids. -/
def flipEdges (D : Fin m → Fin n × Fin n) (F : Finset (Fin m)) : Fin m → Fin n × Fin n :=
  fun e => if e ∈ F then ((D e).2, (D e).1) else D e

/-- `Δ ← max{k − 1, ⌈m / n^{ε_k}⌉}` (Algorithm 3, line 6), with real `n^{ε_k}`. -/
def alg3Delta (n m k : ℕ) : ℕ := max (k - 1) ⌈(m : ℝ) / (n : ℝ) ^ eps k⌉₊

/-- `Alg3Run n m G k P`: `P` is a possible output of Algorithm 3, `kEdgeConnectedComponents(G, k)`
(p.17), on the multigraph `G` with `n` vertices and `m` edges. The relation is nondeterministic
exactly where the algorithm is: the root `r`, the outputs of Lemmas 1 and 2 (any outputs meeting
their guarantees), and the Ford–Fulkerson residual graphs.

* `base` — lines 1–2: if `k = 1` or `n = 1`, return the strongly connected components.
* `split` — lines 3–4: otherwise, if `G` is not strongly connected, run on the induced subgraph
  `G[S]` of every strongly connected component `S` with the same `k` and return the union.
* `main` — lines 5–14: otherwise, with `Δ` as in line 6, compute `P_{k-1}` by a run with `k - 1`,
  apply Lemma 1 to get `P`, pick a root `r` and hitting sets `Z_G`, `Z_{Gᴿ}` (Lemma 2), and for
  each `D ∈ {G, Gᴿ}`, `z ∈ Z_D` take `q = min{k, λ_D(z, r)}` and the residual graph `H` of a
  value-`q` flow; if `q < k`, refine `P` by a run on `(H, k − q)`. -/
inductive Alg3Run : (n m : ℕ) → (Fin m → Fin n × Fin n) → ℕ → (Fin n → Fin n → Prop) → Prop
  | base {n m : ℕ} (G : Fin m → Fin n × Fin n) (k : ℕ) :
      (k = 1 ∨ n = 1) → Alg3Run n m G k (StronglyConn G)
  | split {n m : ℕ} (G : Fin m → Fin n × Fin n) (k : ℕ)
      (runs : (S : Finset (Fin n)) → Fin S.card → Fin S.card → Prop) :
      ¬ (k = 1 ∨ n = 1) → ¬ IsStronglyConnected G →
      (∀ u : Fin n, Alg3Run (sccOf G u).card (inducedEdges G (sccOf G u)).card
          (induced G (sccOf G u)) k (runs (sccOf G u))) →
      Alg3Run n m G k (fun u v => liftRel (sccOf G u) (runs (sccOf G u)) u v)
  | main {n m : ℕ} (G : Fin m → Fin n × Fin n) (k : ℕ)
      (Pk1 P : Fin n → Fin n → Prop) (r : Fin n) (ZG ZR : Finset (Fin n))
      (qG qR : Fin n → ℕ) (FG FR : Fin n → Finset (Fin m))
      (QG QR : Fin n → Fin n → Fin n → Prop) :
      ¬ (k = 1 ∨ n = 1) → IsStronglyConnected G →
      Alg3Run n m G (k - 1) Pk1 →
      Lemma1Guarantee G k (alg3Delta n m k) Pk1 P →
      Lemma2Guarantee G r k (alg3Delta n m k) ZG →
      Lemma2Guarantee (Rev G) r k (alg3Delta n m k) ZR →
      (∀ z ∈ ZG, qG z = min k (lam G z r) ∧ IsUnitFlow G (FG z) z r (qG z)) →
      (∀ z ∈ ZG, qG z < k → Alg3Run n m (flipEdges G (FG z)) (k - qG z) (QG z)) →
      (∀ z ∈ ZR, qR z = min k (lam (Rev G) z r) ∧ IsUnitFlow (Rev G) (FR z) z r (qR z)) →
      (∀ z ∈ ZR, qR z < k → Alg3Run n m (flipEdges (Rev G) (FR z)) (k - qR z) (QR z)) →
      Alg3Run n m G k (fun u v => P u v ∧ (∀ z ∈ ZG, qG z < k → QG z u v) ∧
          (∀ z ∈ ZR, qR z < k → QR z u v))

end DirKECC1549.Main


