-- Prove2me | Definitions.Def_FasterDistributedMatching_ApproximateMatching_Supplement_Recursion
-- name    : FasterDistributedMatching_ApproximateMatching_Supplement_Recursion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:36:12.597431+00:00
-- url     : https://prove2.me/theorems/c56768a3-88e5-4783-8120-f31dd3f9e793
-- title:
--   Badness, cluster degree, Lemmas D.1/D.2 and the halving assumption as specifications, and the execution of Algorithm 1
-- statement:
--   Fix a finite simple graph $\bar G$ with vertex set $V$, an implicit input $N$ and an integer $k$. All logarithms are base two.
--
--   1. **Edge counts and neighbourhoods.** $E(\bar G[U])$ is the set of edges with both endpoints in $U\subseteq V$, and $N_{\bar G}[T]$ is the closed neighbourhood of $T$ (the published definition `SmoothedMIS_IsMIS`).
--   2. **Partitions.** A partition $\mathcal C$ of $V$ consists of pairwise disjoint nonempty clusters covering $V$. It has strong diameter at most $D$ if every cluster induces a connected subgraph in which all distances, measured inside the cluster, are at most $D$. The cluster degree is $\deg_{\mathcal C}(v)=|\{C\in\mathcal C: C\cap N_{\bar G}[v]\ne\emptyset\}|$.
--   3. **Badness.** For $h:V\to\mathbb N_0$ and the distance spheres $S_i(v)=\{u:\operatorname{dist}_{\bar G}(u,v)=i\}$ of the whole graph (unreachable vertices lie in no sphere),
--   $$\mathrm{bad}_{h,t}(v)=\max_{0\le i\le t}\bigl|\{u\in S_i(v): h(u)=\max_{z\in S_i(v)}h(z)\}\bigr|,$$
--   empty spheres contributing zero.
--   4. **Subroutine specifications.** *Lemma D.1:* for every integer $s\ge1$ and $h$ with $\max h\le s$, $\mathrm{ALD.1}(h,s)$ is a partition of strong diameter at most $10s$ with $\deg_{\mathcal C}(v)\le 10s\,\mathrm{bad}_{h,10s}(v)$ for all $v$. *Lemma D.2 (constant $c$):* for $U\subseteq V$, real $M_U\ge|E(\bar G[U])|$, integer $k\ge1$, real $B$ with $\max\{c,k\}\le B\le N$, and positive $h$ with $\max_{u\in U}h(u)\le 10k$ and $\mathrm{bad}_{h,100k}(u)\le B$ on $U$, the output $h'=\mathrm{ALD.2}(U,M_U,B,k,h)$ is positive, $\max h'\le 2\max h+1$, and $|E(\bar G[U])\setminus E(\bar G[U'])|\le M_U/B^3$ for $U'=\{u\in U:\mathrm{bad}_{h',100k}(u)\le B^{1/2+\varepsilon_B}\}$, $\varepsilon_B=(\log\log B)^{-2}$. *Halving assumption:* whenever $\mathcal C$ is a partition of strong diameter at most $100k$ and every $v\in U$ has $\deg_{\mathcal C}(v)\le\lceil 100kN^{1/k}\rceil$, $\mathrm{Half}(U,\mathcal C,k)$ is an independent $P\subseteq U$ with $|E(\bar G[U\setminus N_{\bar G}[P]])|\le\tfrac12|E(\bar G[U])|$. Each specification constrains the output only on inputs meeting its hypotheses.
--   5. **Algorithm 1.** $\mathrm{BaseIS}(U,k,h)$ builds $\mathcal C=\mathrm{ALD.1}(h,10k)$ and runs $\lceil 200(\log N)/k\rceil$ iterations of $P\leftarrow\mathrm{Half}(W,\mathcal C,k)$, $I\leftarrow I\cup P$, $W\leftarrow W\setminus N_{\bar G}[P]$ from $I=\emptyset$, $W=U$. $\mathrm{AlmostMIS}(U,M_U,B,h)$ returns $\mathrm{BaseIS}(U,k,h)$ if $B\le N^{1/k}$; otherwise it sets $h_{rec}=\mathrm{ALD.2}(U,M_U,B,k,h)$, $B_{rec}=B^{1/2+\varepsilon_B}$, $U_1=\{u\in U:\mathrm{bad}_{h_{rec},100k}(u)\le B_{rec}\}$, $I_1=\mathrm{AlmostMIS}(U_1,M_U,B_{rec},h_{rec})$, $U_2=U_1\setminus N_{\bar G}[I_1]$, $I_2=\mathrm{AlmostMIS}(U_2,M_U/B_{rec}^2,B_{rec},h_{rec})$ and returns $I_1\cup I_2$. The relation "the call terminates and returns $I$" is the least relation closed under these two rules (a finite derivation). The reached calls are the root call $\mathrm{AlmostMIS}(V,N^2,N,h\equiv1)$ of ComputeMIS, the first child of a reached internal call, and its second child once the first child has returned. All subroutine calls are valid if at each reached internal call the ALD.2 call meets the hypotheses of Lemma D.2, and at each reached base call the ALD.1 call meets those of Lemma D.1 and every Half call of the loop meets the halving assumption's hypotheses. ComputeMIS outputs $I\cup(V\setminus N_{\bar G}[I])$ for the root output $I$.
--
--   These objects carry the statement of Theorem D.3, the correctness of the recursion behind the paper's MIS routine (Lemma 4.4).
--
--   **Formalization Note** The subroutines are arbitrary functions (the graph and $N$ are fixed), $B$ and $M_U$ are real, $B^{1/2+\varepsilon_B}$ is the real power, and $\log$ is the base mission's `logTwo`. Lean's $1/0=0$ in $\varepsilon_B$ can only occur at $B$ with $\log\log B=0$, which never happens at an internal call of the range of Theorem D.3.
-- source:
--   Mohsen Ghaffari, Christoph Grunau, STOC 2027 submission #1024 (October 2026), Appendix D: cluster degree and badness, printed p.25, PDF p.27; Lemma D.1, printed p.25, PDF p.27; Algorithm 1 and Lemma D.2, printed p.26, PDF p.28; halving assumption of Lemma 4.4, printed p.19, PDF p.21 (restated printed p.25, PDF p.27)

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Basic
import Definitions.Def_SmoothedMIS_IsMIS

namespace FasterDistributedMatching.ApproximateMatching.Supplement

/-! Source: Ghaffari--Grunau, STOC 2027 submission #1024, Appendix D, printed pp. 25–26
(PDF pp. 27–28): cluster degree, badness, Lemmas D.1/D.2 as subroutine specifications,
the halving assumption of Lemma 4.4, and Algorithm 1 with an explicit execution semantics.
The fixed graph `Ḡ` is a simple graph `G` on a finite vertex type `V`; logarithms are base two
(`logTwo` of the base mission). -/

open Classical

variable {V : Type} [Fintype V]

/-- `E(Ḡ[U])`: the edges of `G` with both endpoints in `U`. -/
noncomputable def inducedEdges (G : SimpleGraph V) (U : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ U)

/-- `|E(Ḡ[U])|`. -/
noncomputable def edgeCount (G : SimpleGraph V) (U : Finset V) : ℕ :=
  (inducedEdges G U).card

/-- `N_Ḡ[T]` as a finite set: the closed neighbourhood of the published definition. -/
noncomputable def closedNbhdF (G : SimpleGraph V) (T : Finset V) : Finset V :=
  Finset.univ.filter (fun v => v ∈ SmoothedMIS.closedNbhd G (T : Set V))

/-- `U \ N_Ḡ[T]`. -/
noncomputable def removeNbhd (G : SimpleGraph V) (U T : Finset V) : Finset V :=
  U \ closedNbhdF G T

/-- A partition `𝒞` of `V(Ḡ)`: pairwise disjoint nonempty clusters covering every vertex. -/
def IsPartition (𝒞 : Finset (Finset V)) : Prop :=
  (∀ C ∈ 𝒞, C.Nonempty) ∧
  (∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, C ≠ C' → Disjoint C C') ∧
  (∀ v : V, ∃ C ∈ 𝒞, v ∈ C)

/-- Strong diameter at most `D`: every cluster induces a connected subgraph of `G` in which all
distances (measured inside the induced cluster) are at most `D`. -/
def StrongDiamLE (G : SimpleGraph V) (𝒞 : Finset (Finset V)) (D : ℕ) : Prop :=
  ∀ C ∈ 𝒞, (G.induce (C : Set V)).Connected ∧
    ∀ u v : (C : Set V), (G.induce (C : Set V)).dist u v ≤ D

/-- Cluster degree `deg_𝒞(v) = |{C ∈ 𝒞 : C ∩ N_Ḡ[v] ≠ ∅}|`. -/
noncomputable def clusterDeg (G : SimpleGraph V) (𝒞 : Finset (Finset V)) (v : V) : ℕ :=
  (𝒞.filter (fun C => ∃ u ∈ C, u ∈ SmoothedMIS.closedNbhd G ({v} : Set V))).card

/-- The distance sphere `S_i(v) = {u : dist_Ḡ(u, v) = i}` in the whole graph `G`; unreachable
vertices (extended distance `⊤`) lie in no sphere. -/
noncomputable def sphere (G : SimpleGraph V) (v : V) (i : ℕ) : Finset V :=
  Finset.univ.filter (fun u => G.edist u v = (i : ℕ∞))

/-- Badness `bad_{h,t}(v) = max_{0 ≤ i ≤ t} |{u ∈ S_i(v) : h(u) = max_{z ∈ S_i(v)} h(z)}|`;
an empty sphere contributes zero. -/
noncomputable def bad (G : SimpleGraph V) (h : V → ℕ) (t : ℕ) (v : V) : ℕ :=
  (Finset.range (t + 1)).sup (fun i =>
    ((sphere G v i).filter (fun u => h u = (sphere G v i).sup h)).card)

/-- `max h` over all of `V(Ḡ)` (zero on an empty vertex set). -/
def maxH (h : V → ℕ) : ℕ := Finset.univ.sup h

/-- The base-case threshold `N^{1/k}`. -/
noncomputable def threshold (N k : ℕ) : ℝ := (N : ℝ) ^ ((1 : ℝ) / (k : ℝ))

/-- `ε_B = 1 / (log₂ log₂ B)²`. -/
noncomputable def epsB (B : ℝ) : ℝ := 1 / (logTwo (logTwo B)) ^ 2

/-- `B_rec = B^{1/2 + ε_B}`. -/
noncomputable def Brec (B : ℝ) : ℝ := B ^ ((1 : ℝ) / 2 + epsB B)

/-- Number of halving iterations of `BaseIS`: `⌈200 (log N) / k⌉`. -/
noncomputable def baseIters (N k : ℕ) : ℕ := ⌈200 * logTwo (N : ℝ) / (k : ℝ)⌉₊

/-- **Hypotheses of Lemma D.1** for the call `ALD.1(h, s)`: `s ≥ 1` and `max h ≤ s`. -/
def D1Hyp (h : V → ℕ) (s : ℕ) : Prop := 1 ≤ s ∧ ∀ v, h v ≤ s

/-- **Lemma D.1 as a specification** of a routine `ald1` (only its input/output guarantee; no
round bound): whenever `s ≥ 1` and `max h ≤ s`, `ald1 h s` is a partition of `V(Ḡ)` of strong
diameter at most `10 s` with `deg_𝒞(v) ≤ 10 s · bad_{h,10s}(v)` for every vertex `v`. -/
def D1Spec (G : SimpleGraph V) (ald1 : (V → ℕ) → ℕ → Finset (Finset V)) : Prop :=
  ∀ (h : V → ℕ) (s : ℕ), D1Hyp h s →
    IsPartition (ald1 h s) ∧ StrongDiamLE G (ald1 h s) (10 * s) ∧
    ∀ v, clusterDeg G (ald1 h s) v ≤ 10 * s * bad G h (10 * s) v

/-- **Hypotheses of Lemma D.2** (constant `c`, implicit input `N`) for the call
`ALD.2(U, M_U, B, k, h)`. -/
def D2Hyp (c : ℝ) (G : SimpleGraph V) (N : ℕ) (U : Finset V) (M B : ℝ) (k : ℕ)
    (h : V → ℕ) : Prop :=
  (edgeCount G U : ℝ) ≤ M ∧ 1 ≤ k ∧ max c (k : ℝ) ≤ B ∧ B ≤ (N : ℝ) ∧
  (∀ v, 1 ≤ h v) ∧ (∀ u ∈ U, h u ≤ 10 * k) ∧ (∀ u ∈ U, (bad G h (100 * k) u : ℝ) ≤ B)

/-- **Lemma D.2 as a specification** of a routine `ald2` (only its guarantee; no round bound):
on inputs meeting `D2Hyp`, the output `h'` is positive, `max h' ≤ 2 max h + 1`, and
`|E(Ḡ[U]) \ E(Ḡ[U'])| ≤ M_U / B³` for `U' = {u ∈ U : bad_{h',100k}(u) ≤ B^{1/2+ε_B}}`. -/
def D2Spec (c : ℝ) (G : SimpleGraph V) (N : ℕ)
    (ald2 : Finset V → ℝ → ℝ → ℕ → (V → ℕ) → (V → ℕ)) : Prop :=
  ∀ (U : Finset V) (M B : ℝ) (k : ℕ) (h : V → ℕ), D2Hyp c G N U M B k h →
    (∀ v, 1 ≤ ald2 U M B k h v) ∧
    (∀ v, ald2 U M B k h v ≤ 2 * maxH h + 1) ∧
    (((inducedEdges G U \ inducedEdges G
        (U.filter (fun u => (bad G (ald2 U M B k h) (100 * k) u : ℝ) ≤ Brec B))).card : ℝ)
      ≤ M / B ^ 3)

/-- **Hypotheses of the halving routine** (Lemma 4.4) for the call `Half(U, 𝒞, k)`: `𝒞` is a
partition of strong diameter at most `100k` and each node of `U` has cluster degree at most
`⌈100 k N^{1/k}⌉`. -/
def HalfHyp (G : SimpleGraph V) (N k : ℕ) (U : Finset V) (𝒞 : Finset (Finset V)) : Prop :=
  IsPartition 𝒞 ∧ StrongDiamLE G 𝒞 (100 * k) ∧
  ∀ v ∈ U, (clusterDeg G 𝒞 v : ℝ) ≤ (⌈100 * (k : ℝ) * threshold N k⌉₊ : ℝ)

/-- **The stated halving assumption** (Lemma 4.4): on inputs meeting `HalfHyp`, `Half(U, 𝒞, k)`
returns an independent set `P ⊆ U` with `|E(Ḡ[U \ N_Ḡ[P]])| ≤ ½ |E(Ḡ[U])|`. -/
def HalfSpec (G : SimpleGraph V) (N k : ℕ)
    (half : Finset V → Finset (Finset V) → ℕ → Finset V) : Prop :=
  ∀ (U : Finset V) (𝒞 : Finset (Finset V)), HalfHyp G N k U 𝒞 →
    half U 𝒞 k ⊆ U ∧ G.IsIndepSet ((half U 𝒞 k : Finset V) : Set V) ∧
    (edgeCount G (removeNbhd G U (half U 𝒞 k)) : ℝ) ≤ 1 / 2 * (edgeCount G U : ℝ)

/-- The data of one run of Algorithm 1: the fixed graph `Ḡ`, the implicit input `N`, the
parameter `k`, and the three subroutines. -/
structure Setup (V : Type) where
  G : SimpleGraph V
  N : ℕ
  k : ℕ
  ald1 : (V → ℕ) → ℕ → Finset (Finset V)
  ald2 : Finset V → ℝ → ℝ → ℕ → (V → ℕ) → (V → ℕ)
  half : Finset V → Finset (Finset V) → ℕ → Finset V

namespace Setup

variable (S : Setup V)

/-- The partition `𝒞 ← ALD.1(h, 10k)` built by `BaseIS(U, k, h)` (line 18). -/
noncomputable def basePartition (h : V → ℕ) : Finset (Finset V) := S.ald1 h (10 * S.k)

/-- The state `(I, W)` of the loop of `BaseIS(U, k, h)` after `t` iterations (lines 19–24):
`I ← ∅, W ← U`, then `P ← Half(W, 𝒞, k); I ← I ∪ P; W ← W \ N_Ḡ[P]`. -/
noncomputable def baseState (U : Finset V) (h : V → ℕ) : ℕ → Finset V × Finset V
  | 0 => (∅, U)
  | t + 1 =>
    let st := baseState U h t
    let P := S.half st.2 (S.basePartition h) S.k
    (st.1 ∪ P, removeNbhd S.G st.2 P)

/-- The output of `BaseIS(U, k, h)`: `I` after `⌈200 (log N)/k⌉` iterations. -/
noncomputable def baseIS (U : Finset V) (h : V → ℕ) : Finset V :=
  (S.baseState U h (baseIters S.N S.k)).1

/-- `h_rec ← ALD.2(U, M_U, B, k, h)` (line 6). -/
noncomputable def hrec (U : Finset V) (M B : ℝ) (h : V → ℕ) : V → ℕ := S.ald2 U M B S.k h

/-- `U₁ ← {u ∈ U : bad_{h_rec,100k}(u) ≤ B_rec}` (line 9). -/
noncomputable def U1 (U : Finset V) (M B : ℝ) (h : V → ℕ) : Finset V :=
  U.filter (fun u => (bad S.G (S.hrec U M B h) (100 * S.k) u : ℝ) ≤ Brec B)

/-- **Big-step semantics of `AlmostMIS`** (lines 1–16): `Runs U M B h I` means that the call
`AlmostMIS(U, M_U, B, h)` terminates (has a finite derivation) and returns `I`. -/
inductive Runs : Finset V → ℝ → ℝ → (V → ℕ) → Finset V → Prop
  | base (U : Finset V) (M B : ℝ) (h : V → ℕ) :
      B ≤ threshold S.N S.k → Runs U M B h (S.baseIS U h)
  | step (U : Finset V) (M B : ℝ) (h : V → ℕ) (I₁ I₂ : Finset V) :
      ¬ B ≤ threshold S.N S.k →
      Runs (S.U1 U M B h) M (Brec B) (S.hrec U M B h) I₁ →
      Runs (removeNbhd S.G (S.U1 U M B h) I₁) (M / Brec B ^ 2) (Brec B) (S.hrec U M B h) I₂ →
      Runs U M B h (I₁ ∪ I₂)

/-- **Reached calls** of `AlmostMIS`: the root call `AlmostMIS(V(Ḡ), N², N, h ≡ 1)` made by
`ComputeMIS` (lines 28–29); the first child `AlmostMIS(U₁, M_U, B_rec, h_rec)` of a reached
internal call (line 10); and the second child `AlmostMIS(U₁ \ N_Ḡ[I₁], M_U/B_rec², B_rec, h_rec)`
(lines 11–13), reached once the first child has returned `I₁`. -/
inductive Reached : Finset V → ℝ → ℝ → (V → ℕ) → Prop
  | root : Reached Finset.univ ((S.N : ℝ) ^ 2) (S.N : ℝ) (fun _ => 1)
  | left (U : Finset V) (M B : ℝ) (h : V → ℕ) :
      Reached U M B h → ¬ B ≤ threshold S.N S.k →
      Reached (S.U1 U M B h) M (Brec B) (S.hrec U M B h)
  | right (U : Finset V) (M B : ℝ) (h : V → ℕ) (I₁ : Finset V) :
      Reached U M B h → ¬ B ≤ threshold S.N S.k →
      Runs S (S.U1 U M B h) M (Brec B) (S.hrec U M B h) I₁ →
      Reached (removeNbhd S.G (S.U1 U M B h) I₁) (M / Brec B ^ 2) (Brec B) (S.hrec U M B h)

/-- **All subroutine calls are valid**: at every reached internal call the `ALD.2` call meets the
hypotheses of Lemma D.2 (constant `c`); at every reached base call the `ALD.1(h, 10k)` call meets
the hypotheses of Lemma D.1, and each of the `⌈200 (log N)/k⌉` calls `Half(W, 𝒞, k)` meets the
halving assumption's hypotheses. -/
def AllCallsValid (c : ℝ) : Prop :=
  ∀ (U : Finset V) (M B : ℝ) (h : V → ℕ), S.Reached U M B h →
    (¬ B ≤ threshold S.N S.k → D2Hyp c S.G S.N U M B S.k h) ∧
    (B ≤ threshold S.N S.k →
      D1Hyp h (10 * S.k) ∧
      ∀ t < baseIters S.N S.k, HalfHyp S.G S.N S.k (S.baseState U h t).2 (S.basePartition h))

/-- The output of `ComputeMIS` given the root output `I`: `I ∪ (V(Ḡ) \ N_Ḡ[I])` (line 30). -/
noncomputable def computeMISOutput (I : Finset V) : Finset V :=
  I ∪ removeNbhd S.G Finset.univ I

end Setup

end FasterDistributedMatching.ApproximateMatching.Supplement


