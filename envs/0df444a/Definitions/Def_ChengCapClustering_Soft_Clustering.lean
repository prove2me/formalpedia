-- Prove2me | Definitions.Def_ChengCapClustering_Soft_Clustering
-- name    : ChengCapClustering_Soft_Clustering
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:51:19.774869+00:00
-- url     : https://prove2.me/theorems/84a6ef6f-a809-4763-80db-33f6bb6096cf
-- title:
--   Capacitated $(k,z)$-clustering with uniform soft capacities: solutions, cost, OPT, $K=k+\lfloor\varepsilon k\rfloor$, block partitions, movable blocks, transport supports, aspect ratio, $\Psi_Q$
-- statement:
--   Definition 2.1 and §§2–3 (printed pp. 1, 4–8), §5.2 and §5.3 (printed pp. 23, 26).
--
--   - **Instance.** A metric space $V$, clients $p:\mathrm{Fin}\,n\to V$ (a multiset: coincident clients keep multiplicity), locations $F\subseteq V$ (finite and listed injectively in the metric setting, $F=\mathbb R^d$ in the Euclidean setting), positive integers $k$, $U$, and a real exponent $z\ge 1$.
--   - **Soft solution** (`SoftSolution`, `IsSoftSolution F U K S`): $c\le K$ centers with locations $\mathrm{loc}_j\in F$ (several may coincide) and an assignment $\sigma$ of every client to a center, each center serving at most $U$ clients. **Cost** $\sum_p \mathrm{dist}(p,\mathrm{loc}_{\sigma(p)})^z$. An **uncapacitated solution** drops the capacity constraint.
--   - **OPT** (`opt`): the infimum, in $[0,\infty]$, of the cost over soft solutions with at most $k$ centers ($=\infty$ when none exists).
--   - $K=k+\lfloor\varepsilon k\rfloor$ (eq. (1), `numOpenK`). `IdxSolution` stores center locations as indices into a list of locations, with its integer output layout `[c, loc indices…, assignment…]`.
--   - **Block partition** (Definition 3.1): blocks $P_1,\dots,P_m$ (a block label for every client) and representatives $a_i\in F$, with $m\le 2k-1$, every block nonempty of size $w_i\le U$; internal cost $A_i=\sum_{p\in P_i}\mathrm{dist}(p,a_i)^z$, $A=\sum_i A_i$.
--   - **$(u,v)$-movable** (Definition 3.3, $u\ge1$, $v\ge0$): for every list of $|Q|$ slots $y_1,\dots,y_{|Q|}\in F$ (repetitions allowed) some bijection $\varphi:Q\to\{1,\dots,|Q|\}$ has $\sum_{q}\mathrm{dist}(q,y_{\varphi(q)})^z\le u\sum_q\mathrm{dist}(q,a)^z+v\sum_q\mathrm{dist}(a,y_{\varphi(q)})^z$.
--   - **Support of a transport plan** $\pi:I\times J\to\mathbb N$: the bipartite graph on $I\sqcup J$ with an edge $ij$ when $\pi_{ij}>0$.
--   - **Aspect ratio** $\Delta$ of a point list: largest over smallest positive distance ($1$ if no positive distance). Inputs list a metric instance as the $(n+m)\times(n+m)$ distance matrix (clients first), a Euclidean one by coordinates.
--   - $D'(D,\eta_c)=\log_2\big(2^{4D}+6(768/\eta_c)^D N\big)$ with $N=(1+11/\eta_c)^{(32/\eta_c)^D+\lceil\log_2(2/\eta_c)\rceil(16/\eta_c)^D}$ (Lemma 5.1).
--   - $\Psi_Q(c)=\sum_{q\in Q}\|q-c\|^z$ in $\mathbb R^d$, with multiplicity (§5.3).
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), eq. (1), printed p. 1; Definition 2.1 and §2, printed pp. 4–6 / PDF pp. 6–8; Definitions 3.1, 3.3, printed p. 7 / PDF p. 9; Lemma 5.1, printed p. 23; §5.3, printed p. 26 / PDF p. 28

import Mathlib
import Definitions.Def_MinSumDimRed_Doubling_Metric

namespace ChengCapClustering.Soft

/-!
# Capacitated (k, z)-clustering with uniform soft capacities, blocks, movability, transport plans

Cheng, Mo, Ding, arXiv:2610.40625 (held manuscript SHA-256 9d298191…): §1 eq. (1) (printed p. 1 /
PDF p. 3), Definition 2.1 and §2 (printed pp. 4–6 / PDF pp. 6–8), Definitions 3.1 and 3.3 (printed
p. 7 / PDF p. 9), §3.2 (printed p. 8 / PDF p. 10), §5.3 (printed p. 26 / PDF p. 28).

**Formalization Note.**
* Clients are an indexed family `p : Fin n → V`, so coincident clients keep their multiplicity.
  A solution is a finite family of `numCenters` centers (locations may coincide: soft capacities)
  and a total assignment of clients to center indices. The location set `F` is a `Set V`; in the
  Euclidean setting it is `Set.univ`.
* `opt` is an infimum in `ℝ≥0∞` over solutions with at most `k` centers, so an instance without
  feasible solutions has `opt = ⊤` (never the real `sInf ∅ = 0`).
* A block partition has `m ≤ 2k − 1` written `m + 1 ≤ 2k`, nonempty blocks of size at most `U`,
  and representatives in `F`.
* `aspectRatio` is the ratio of the largest to the smallest positive distance among the listed
  points, and `1` when no two listed points are at positive distance.
-/

open scoped BigOperators ENNReal

variable {V : Type*}

/-- The number of centers the algorithm may open, `K = k + ⌊εk⌋` (eq. (1)). -/
noncomputable def numOpenK (k : ℕ) (ε : ℝ) : ℕ := k + ⌊ε * (k : ℝ)⌋₊

/-- A (soft) solution for `n` clients: `numCenters` centers at locations `loc`, and an assignment
of every client to a center index. Several centers may share a location. -/
structure SoftSolution (V : Type*) (n : ℕ) where
  numCenters : ℕ
  loc : Fin numCenters → V
  assign : Fin n → Fin numCenters

/-- The number of clients served by center `j`. -/
def SoftSolution.load {n : ℕ} (S : SoftSolution V n) (j : Fin S.numCenters) : ℕ :=
  (Finset.univ.filter fun i => S.assign i = j).card

/-- `S` is a soft solution with at most `K` centers, all at locations in `F`, every center serving
at most `U` clients. -/
def IsSoftSolution {n : ℕ} (F : Set V) (U K : ℕ) (S : SoftSolution V n) : Prop :=
  S.numCenters ≤ K ∧ (∀ j, S.loc j ∈ F) ∧ ∀ j, S.load j ≤ U

/-- `S` is an uncapacitated solution with at most `K` centers at locations in `F` (no capacity
constraint on the assignment). -/
def IsUncapSolution {n : ℕ} (F : Set V) (K : ℕ) (S : SoftSolution V n) : Prop :=
  S.numCenters ≤ K ∧ ∀ j, S.loc j ∈ F

/-- The cost `∑_p dist(p, σ(p))^z` of a solution (real power `z`). -/
noncomputable def SoftSolution.cost [PseudoMetricSpace V] {n : ℕ} (z : ℝ) (p : Fin n → V)
    (S : SoftSolution V n) : ℝ :=
  ∑ i, dist (p i) (S.loc (S.assign i)) ^ z

/-- `OPT`: the minimum cost of a soft solution with at most `k` centers at locations in `F` and
capacity `U`, as an infimum in `ℝ≥0∞` (`⊤` if there is no such solution). -/
noncomputable def opt [PseudoMetricSpace V] {n : ℕ} (z : ℝ) (p : Fin n → V) (F : Set V)
    (U k : ℕ) : ℝ≥0∞ :=
  ⨅ (S : SoftSolution V n) (_ : IsSoftSolution F U k S), ENNReal.ofReal (S.cost z p)

/-- A solution whose centers are given by indices into a finite list of locations `f : Fin m → V`. -/
structure IdxSolution (n m : ℕ) where
  numCenters : ℕ
  locIdx : Fin numCenters → Fin m
  assign : Fin n → Fin numCenters

/-- The solution with locations `f ∘ locIdx`. -/
def IdxSolution.toSoft {n m : ℕ} (f : Fin m → V) (S : IdxSolution n m) : SoftSolution V n :=
  ⟨S.numCenters, fun j => f (S.locIdx j), S.assign⟩

/-- The integer output layout of an index solution: `[c] ++ [locIdx 0, …, locIdx (c-1)] ++
[assign 0, …, assign (n-1)]`. -/
def IdxSolution.encode {n m : ℕ} (S : IdxSolution n m) : List ℤ :=
  (S.numCenters : ℤ) :: (List.ofFn fun j => ((S.locIdx j : ℕ) : ℤ)) ++
    List.ofFn fun i => ((S.assign i : ℕ) : ℤ)

/-- Definition 3.1 data: `numBlocks` blocks, the block of every client, and a representative for
every block. -/
structure BlockPartition (V : Type*) (n : ℕ) where
  numBlocks : ℕ
  block : Fin n → Fin numBlocks
  rep : Fin numBlocks → V

/-- The clients of block `i`. -/
def BlockPartition.members {n : ℕ} (B : BlockPartition V n) (i : Fin B.numBlocks) :
    Finset (Fin n) :=
  Finset.univ.filter fun q => B.block q = i

/-- The size `w_i = |P_i|`. -/
def BlockPartition.size {n : ℕ} (B : BlockPartition V n) (i : Fin B.numBlocks) : ℕ :=
  (B.members i).card

/-- The internal cost `A_i = ∑_{p ∈ P_i} dist(p, a_i)^z`. -/
noncomputable def BlockPartition.internalCost [PseudoMetricSpace V] {n : ℕ} (z : ℝ)
    (p : Fin n → V) (B : BlockPartition V n) (i : Fin B.numBlocks) : ℝ :=
  ∑ q ∈ B.members i, dist (p q) (B.rep i) ^ z

/-- `A = ∑_i A_i`. -/
noncomputable def BlockPartition.totalCost [PseudoMetricSpace V] {n : ℕ} (z : ℝ)
    (p : Fin n → V) (B : BlockPartition V n) : ℝ :=
  ∑ i, B.internalCost z p i

/-- Definition 3.1: a block partition of the clients for parameters `k`, `U` and locations `F`:
`m ≤ 2k − 1` blocks, every block nonempty of size at most `U`, every representative in `F`. -/
def IsBlockPartition {n : ℕ} (k U : ℕ) (F : Set V) (B : BlockPartition V n) : Prop :=
  B.numBlocks + 1 ≤ 2 * k ∧ (∀ i, (B.members i).Nonempty) ∧ (∀ i, B.size i ≤ U) ∧
    ∀ i, B.rep i ∈ F

/-- Definition 3.3: the block `Q` (points `pt q`, `q ∈ Q`) with representative `a` is
`(u, v)`-movable (`u ≥ 1`, `v ≥ 0`): for all `|Q|` slots `y_1, …, y_{|Q|} ∈ F` (not necessarily
distinct) some bijection `φ : Q → {1, …, |Q|}` satisfies
`∑_{q ∈ Q} dist(q, y_{φ(q)})^z ≤ u · ∑_{q ∈ Q} dist(q, a)^z + v · ∑_{q ∈ Q} dist(a, y_{φ(q)})^z`. -/
def IsMovable [PseudoMetricSpace V] {ι : Type*} (z u v : ℝ) (F : Set V) (Q : Finset ι)
    (pt : ι → V) (a : V) : Prop :=
  1 ≤ u ∧ 0 ≤ v ∧
    ∀ y : Fin Q.card → V, (∀ j, y j ∈ F) →
      ∃ e : Q ≃ Fin Q.card,
        ∑ q : Q, dist (pt q) (y (e q)) ^ z ≤
          u * (∑ q ∈ Q, dist (pt q) a ^ z) + v * (∑ q : Q, dist a (y (e q)) ^ z)

/-- The support of a transport plan `π` (rows `I`, columns `J`): the bipartite graph on `I ⊕ J`
with an edge `ij` whenever `π i j > 0`. -/
def supportGraph {I J : Type*} (π : I → J → ℕ) : SimpleGraph (I ⊕ J) :=
  SimpleGraph.fromRel fun x y => ∃ i j, x = Sum.inl i ∧ y = Sum.inr j ∧ 0 < π i j

/-- The positive distances among the listed points. -/
noncomputable def positiveDistances [PseudoMetricSpace V] {N : ℕ} (x : Fin N → V) : Finset ℝ :=
  ((Finset.univ : Finset (Fin N × Fin N)).image fun ij => dist (x ij.1) (x ij.2)).filter
    fun r => 0 < r

/-- The aspect ratio `Δ`: the largest over the smallest positive distance among the listed points,
and `1` if no two of them are at positive distance. -/
noncomputable def aspectRatio [PseudoMetricSpace V] {N : ℕ} (x : Fin N → V) : ℝ :=
  if h : (positiveDistances x).Nonempty then
    (positiveDistances x).max' h / (positiveDistances x).min' h
  else 1

/-- The real input layout of a finite point list: the distance matrix in row-major order,
`dist (x 0) (x 0), dist (x 0) (x 1), …`. -/
noncomputable def distanceList [PseudoMetricSpace V] {N : ℕ} (x : Fin N → V) : List ℝ :=
  List.ofFn fun ij : Fin (N * N) => dist (x (finProdFinEquiv.symm ij).1) (x (finProdFinEquiv.symm ij).2)

/-- The metric instance with clients `p : Fin n → V` and locations `f : Fin m → V` as one list of
`n + m` points: clients first, then locations. -/
def instancePoints {n m : ℕ} (p : Fin n → V) (f : Fin m → V) : Fin (n + m) → V :=
  Fin.append p f

/-- Lemma 5.1 (printed p. 23 / PDF p. 25): the number of signatures
`N = (1 + 11/η_c)^{(32/η_c)^D + ⌈log₂(2/η_c)⌉ (16/η_c)^D}`. -/
noncomputable def signatureCount (D ηc : ℝ) : ℝ :=
  (1 + 11 / ηc) ^ ((32 / ηc) ^ D + (⌈Real.logb 2 (2 / ηc)⌉₊ : ℝ) * (16 / ηc) ^ D)

/-- Lemma 5.1: the doubling bound `D′ = log₂(2^{4D} + 6 (768/η_c)^D N)` after compression. -/
noncomputable def compressedDim (D ηc : ℝ) : ℝ :=
  Real.logb 2 ((2 : ℝ) ^ (4 * D) + 6 * (768 / ηc) ^ D * signatureCount D ηc)

/-- Euclidean space `ℝ^d`. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The real layout of a list of points of `ℝ^d`: all coordinates, point by point. -/
noncomputable def coordList {d N : ℕ} (x : Fin N → Euc d) : List ℝ :=
  List.ofFn fun ij : Fin (N * d) => x (finProdFinEquiv.symm ij).1 (finProdFinEquiv.symm ij).2

/-- `Ψ_Q(c) = ∑_{q ∈ Q} ‖pt q − c‖^z`, with multiplicity (§5.3). -/
noncomputable def psi {d : ℕ} {ι : Type*} (z : ℝ) (Q : Finset ι) (pt : ι → Euc d) (c : Euc d) : ℝ :=
  ∑ q ∈ Q, ‖pt q - c‖ ^ z

end ChengCapClustering.Soft


