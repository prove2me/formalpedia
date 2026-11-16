-- Prove2me | Definitions.Def_STCSublinear1377_Main_Supplement_Section2
-- name    : STCSublinear1377_Main_Supplement_Section2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:19:26.570271+00:00
-- url     : https://prove2.me/theorems/037e5be9-f8ff-4bce-a500-143ae84cf824
-- title:
--   The Section 2 algorithm: hubs, regions, sub-regions and runs
-- statement:
--   Let $G$ be a connected simple unweighted graph on $n$ vertices, $k=\mathrm{STC}(G)$, and $D=4n^{8/9}$. The **hubs** are $H=\{v:d_G(v)>D\}$, $q=|H|$. A **run** of the algorithm of §2 (p.5) consists of the following data and conditions.
--
--   1. If $q=n$, the output is a Chandran–Cheung–Issac tree: any spanning tree of congestion at most $8\sqrt{mn}$ (Proposition 1.2).
--   2. If $q=0$, a spanning tree $T$ of $G$ is built by the Lemma 2.3 routine on $P=V(G)$, and the better of $T$ and the baseline tree is returned.
--   3. If $1\le q<n$: (2a) the **regions** arise from $\{V\}$ by repeatedly splitting a current region $R$ containing two distinct hubs $a,b$ along an exact minimum $a$–$b$ cut of $G[R]$, until every region contains exactly one hub; (2b) the **terminals** of a region $R$ with hub $v$ are the neighbours of $v$ in $R$, and the **sub-regions** partition $V\setminus H$: each lies in a connected component of $G[R\setminus\{v\}]$, is connected and contains exactly one terminal, and a component with exactly one terminal is kept whole; (3a) each sub-region $P$ gets a spanning tree of $G[P]$; (3b) every terminal is joined to the hub of its region; (3c) graph edges between different regions join the regional trees, and the union $T$ is a spanning tree of $G$; (4) the better of $T$ and the baseline tree is returned.
--
--   A run **succeeds with constants** $C_1,C_2$ if every sub-region tree satisfies $c(G[P],T_P)\le C_2\,k\max\{D_P,b_G(P)\}\log^{3/2}n$ (with $D_P=\max_{u\in P}d_G(u)$) and, on every component $K$ with $t_K\ge2$ terminals, every sub-region inside $K$ has boundary in $G[K]$ at most $C_1\min\{\sqrt{t_K}\,\mathrm{OPT}_K\log^2 n,\ \sqrt{M_K\,\mathrm{OPT}_K}\log^{3/2}n\}$, where $\mathrm{OPT}_K$ is the connected multiway-cut optimum of $G[K]$ and $M_K$ its number of edges (the guarantees of Lemma 2.3 and Theorem 1.4).
--
--   These objects let Theorem 2.4 speak about this particular algorithm rather than about any algorithm with the same ratio.
--
--   **Formalization Note** The randomized subroutines are represented by arbitrary outputs constrained by their output format; their guarantees enter only through the success predicate. In step (4) a tie may return either tree. $D$ is the real number $4n^{8/9}$, compared exactly with integer degrees.
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, §2, steps (1)–(4) and (2.1)–(2.3), PDF/printed pp.3–5

import Definitions.Def_STCSublinear1377_Main_Supplement_Terminal
set_option autoImplicit false

namespace STCSublinear1377.Main.Supplement

/-- The Section 2 degree threshold `D = 4 n^{8/9}`. -/
noncomputable def threshold (n : ℕ) : ℝ := 4 * Real.rpow (n : ℝ) (8 / 9 : ℝ)

/-- The hubs of Section 2: vertices of degree greater than `D = 4 n^{8/9}`. -/
noncomputable def sec2Hubs {n : ℕ} (g : Table n) : Finset (Fin n) :=
  hubs (original g) (threshold n)

/-- The terminals of a region `R` with hub `v`: the neighbours of `v` lying in `R`. -/
noncomputable def regionTerminals {n : ℕ} (g : Table n) (R : Finset (Fin n))
    (v : Fin n) : Finset (Fin n) := by
  classical
  exact R.filter (fun u => (tableGraph g).Adj v u)

/-- `K` is a connected component of `G[S]`. -/
def IsComponent {n : ℕ} (g : Table n) (S K : Finset (Fin n)) : Prop :=
  K ⊆ S ∧ (original g).connectedSet K ∧
    ∀ u ∈ K, ∀ w ∈ S, (tableGraph g).Adj u w → w ∈ K

/-- Largest original degree on a vertex set (zero on the empty set). -/
noncomputable def maxDegreeOn {n : ℕ} (g : Table n) (P : Finset (Fin n)) : ℝ :=
  P.fold max 0 (fun u => (original g).degree u)

/-- Step (2a): the families of regions reachable from `{V}` by repeatedly splitting a current
region `R` containing two distinct hubs `a, b` along an exact minimum `a`–`b` cut of `G[R]`. -/
inductive RegionSplit {n : ℕ} (g : Table n) (H : Finset (Fin n)) :
    Finset (Finset (Fin n)) → Prop
  | start : RegionSplit g H {Finset.univ}
  | cut (fam : Finset (Finset (Fin n))) (R X : Finset (Fin n)) (a b : Fin n)
      (prev : RegionSplit g H fam) (hR : R ∈ fam) (ha : a ∈ R ∩ H) (hb : b ∈ R ∩ H)
      (hab : a ≠ b) (haX : a ∈ X) (hXR : X ⊆ R) (hbX : b ∉ X)
      (hmin : ((original g).induced R).boundary X =
        ((original g).induced R).mincut {a} {b}) :
      RegionSplit g H (insert X (insert (R \ X) (fam.erase R)))

/-- The data of one run of the Section 2 algorithm: regions, sub-regions, their internal trees,
region-joining edges, the assembled tree `T`, the Proposition 1.2 tree and the returned tree. -/
structure Section2Run {n : ℕ} (g : Table n) where
  regions : Finset (Finset (Fin n))
  parts : Finset (Finset (Fin n))
  internal : Finset (Fin n) → Table n
  join : Table n
  candidate : Table n
  baseline : Table n
  output : Table n

variable {n : ℕ} {g : Table n}

/-- The Chandran–Cheung–Issac tree: any spanning tree with the guarantee of Proposition 1.2. -/
def Section2Run.baselineOK (x : Section2Run g) : Prop :=
  spanning g x.baseline ∧
    (congestion g x.baseline : ℝ) ≤ 8 * Real.sqrt ((edgeCount g : ℝ) * n)

/-- Step (4): the better of the assembled tree and the baseline tree is returned. -/
def Section2Run.better (x : Section2Run g) : Prop :=
  (x.output = x.candidate ∨ x.output = x.baseline) ∧
    congestion g x.output = min (congestion g x.candidate) (congestion g x.baseline)

/-- Step (2a): the regions come from exact minimum hub cuts and each holds exactly one hub. -/
def Section2Run.regionsOK (x : Section2Run g) : Prop :=
  RegionSplit g (sec2Hubs g) x.regions ∧ ∀ R ∈ x.regions, (R ∩ sec2Hubs g).card = 1

/-- Step (2b): the sub-regions partition `V ∖ H`; each lies in a component of some `R_i ∖ {v_i}`,
is connected and holds exactly one terminal; a one-terminal component is kept intact. -/
def Section2Run.partsOK (x : Section2Run g) : Prop :=
  (∀ P ∈ x.parts, ∀ Q ∈ x.parts, P ≠ Q → Disjoint P Q) ∧
  x.parts.biUnion id = Finset.univ \ sec2Hubs g ∧
  (∀ P ∈ x.parts, ∃ R ∈ x.regions, ∃ v ∈ R ∩ sec2Hubs g, ∃ K : Finset (Fin n),
    IsComponent g (R.erase v) K ∧ P ⊆ K ∧ (original g).connectedSet P ∧
      (regionTerminals g R v ∩ P).card = 1) ∧
  (∀ R ∈ x.regions, ∀ v ∈ R ∩ sec2Hubs g, ∀ K : Finset (Fin n),
    IsComponent g (R.erase v) K → (regionTerminals g R v ∩ K).card = 1 → K ∈ x.parts)

/-- Step (3): internal spanning trees of the sub-regions, attachment of every terminal to its
hub, region-joining graph edges between different regions, and the union is a spanning tree. -/
def Section2Run.treesOK (x : Section2Run g) : Prop :=
  (∀ P ∈ x.parts, ((original g).induced P).tree (x.internal P)) ∧
  (∀ u v, x.join u v = true →
    (tableGraph g).Adj u v ∧ ∀ R ∈ x.regions, u ∈ R → v ∉ R) ∧
  (∀ u v, x.candidate u v = true ↔
    ((∃ P ∈ x.parts, x.internal P u v = true) ∨
      (u ∈ sec2Hubs g ∧ ∃ R ∈ x.regions, u ∈ R ∧ v ∈ regionTerminals g R u) ∨
      (v ∈ sec2Hubs g ∧ ∃ R ∈ x.regions, v ∈ R ∧ u ∈ regionTerminals g R v) ∨
      x.join u v = true)) ∧
  spanning g x.candidate

/-- A legal run of steps (1)–(4) with arbitrary outputs of the randomized subroutines. -/
def Section2Run.valid (x : Section2Run g) : Prop :=
  x.baselineOK ∧
  (((sec2Hubs g).card = n ∧ x.regions = ∅ ∧ x.parts = ∅ ∧ x.output = x.baseline) ∨
   ((sec2Hubs g).card = 0 ∧ x.regions = ∅ ∧ x.parts = {Finset.univ} ∧
      ((original g).induced Finset.univ).tree (x.internal Finset.univ) ∧
      x.candidate = x.internal Finset.univ ∧ x.better) ∨
   (1 ≤ (sec2Hubs g).card ∧ (sec2Hubs g).card < n ∧
      x.regionsOK ∧ x.partsOK ∧ x.treesOK ∧ x.better))

/-- Every subroutine call of the run meets its guarantee with constants `C₁` (Theorem 1.4, both
bounds, on each component of `R_i ∖ {v_i}` with at least two terminals) and `C₂` (Lemma 2.3, on
each sub-region). Logarithms are of the order `n` of `G`. -/
def Section2Run.succeeds (x : Section2Run g) (C₁ C₂ : ℝ) : Prop :=
  (∀ P ∈ x.parts, ((original g).induced P).congestion (x.internal P) ≤
    C₂ * (stc g : ℝ) * max (maxDegreeOn g P) ((original g).boundary P) *
      Real.rpow (Real.log (n : ℝ)) (3 / 2 : ℝ)) ∧
  (∀ R ∈ x.regions, ∀ v ∈ R ∩ sec2Hubs g, ∀ K : Finset (Fin n),
    IsComponent g (R.erase v) K → 2 ≤ (regionTerminals g R v ∩ K).card →
    ∀ P ∈ x.parts, P ⊆ K →
      ((original g).induced K).boundary P ≤ C₁ * min
        (Real.sqrt ((regionTerminals g R v ∩ K).card : ℝ) *
          opt ((original g).induced K) (regionTerminals g R v ∩ K) *
          Real.log (n : ℝ) ^ 2)
        (Real.sqrt (((original g).induced K).totalWeight *
            opt ((original g).induced K) (regionTerminals g R v ∩ K)) *
          Real.rpow (Real.log (n : ℝ)) (3 / 2 : ℝ)))

end STCSublinear1377.Main.Supplement


