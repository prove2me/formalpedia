-- Prove2me | Definitions.Def_NetUnrelDesign_Main_Model
-- name    : NetUnrelDesign_Main_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:08:50.300638+00:00
-- url     : https://prove2.me/theorems/417a928a-83d0-476b-9e0c-19f4eb97cf95
-- title:
--   The random working graph, components, pivotal marks, cuts, minors and the design instance
-- statement:
--   A network is a multigraph on the vertex set $\{0,\dots,n-1\}$ with $m$ labelled edges, given by the two endpoints of each edge; parallel edges and self-loops are allowed. Edges fail independently: a failure set $F$ has probability $\prod_{e\in F}q_e\prod_{e\notin F}(1-q_e)$, and expectations are the corresponding finite sums. The working graph joins two distinct vertices when some edge outside $F$ has them as endpoints.
--
--   - **Unreliability** $u$ is the probability that the working graph is disconnected; $R=1-u$ is the probability that it is connected. With weights $w$, edges fail with probability $e^{-w_e}$, and $R_G(w)$ is the connectivity probability; $-\log R_G$ takes the value $+\infty$ where $R_G=0$ (an extended real).
--   - $K$ is the number of working components and $\Pi$ the partition of the vertices into them. For a partition $\pi$, the **pivotal mark** is $b_e(\pi)=1$ when $\pi$ has two blocks and the endpoints of $e$ lie in different blocks, and $0$ otherwise (a loop has mark $0$).
--   - A **cut** is a nontrivial bipartition $\{S,V\setminus S\}$ with the two shores identified. An edge crosses a cut when its endpoints lie on different shores; $w(C)=\sum_{e\text{ crosses }C}w_e$, $\lambda=\min_C w(C)$, $z=\sum_C e^{-w(C)}$ and $M=\binom n2$ (2.3).
--   - The **design instance** of (1.1) is $(G,q^0,A,b)$ with $q_e(x)=q^0_e e^{-x_e}$, $w_e(x)=-\log q^0_e+x_e$, $X=\{x\ge0:Ax\le b\}$, $u(x)$ the unreliability under $q(x)$, $u^*=\min_X u$, $\lambda(x)$, $z(x)$ and $\Phi(x)=-\log(1-u(x))$. The standing assumptions are: $G$ connected, $n\ge2$, $0<q^0_e\le1$, $A_{ij}>0$, $b_i>0$, $k\ge1$.
--   - A graph $H$ with failure probabilities $q'$ is an **iterated deletion/contraction minor** of $(G,q)$ when, for disjoint edge sets $D$ (deleted) and $C$ (contracted), the vertices of $H$ are the components of $(V,C)$, its edges are the remaining edges with the images of their endpoints, and each keeps its original failure probability.
--
--   **Formalization Note.** Endpoints are a map `Fin m → Fin n × Fin n`; the order within a pair has no meaning. A cut is the unordered pair `s(S, Sᶜ)` of `Sym2 (Finset (Fin n))`. `minCut` is `0` when there is no cut ($n\le1$, excluded by the standing assumption). $u^*$ is written as `sInf (u '' X)`: $X$ is nonempty ($0\in X$) and compact, and $u$ is continuous, so the infimum is attained. Partitions are `Setoid (Fin n)`, and the number of components is `Nat.card` of the connected components. Iterated minors are encoded through a surjection on vertices, whose fibres are the components of the contracted edges, and an injection on edge labels onto the edges that are neither deleted nor contracted. Contracting edges one at a time gives the same graph as contracting the whole set at once.
-- source:
--   Sun 2026, Fast Approximation Algorithms for Minimizing Network Unreliability, doi:10.5281/zenodo.23914978 (PDF sha256 1120f100…), §1 (p. 1, PDF 2: (1.1)–(1.2)); §2.1 (p. 6, PDF 7: Π, K, b_e); Lemma 2.1 (p. 6, PDF 7: R_G); §2.2–2.3 (p. 7, PDF 8: Φ, cuts, (2.3)); App. A.1 (p. 21–22, PDF 22–23: deletion/contraction minors)

import Mathlib

open scoped BigOperators Classical

noncomputable section

namespace NetUnrelDesign.Main

/-!
# Network unreliability: the random working graph, components, pivotal marks, cuts and the
design instance

Mu-Xia Sun, *Fast Approximation Algorithms for Minimizing Network Unreliability* (2026),
doi:10.5281/zenodo.23914978, §1 (p. 1, PDF 2: the model (1.1)–(1.2)), §2.1 (p. 6, PDF 7: `Π`,
`K`, `b_e(Π)`, (2.1)), Lemma 2.1 (p. 6, PDF 7: `R_G`), §2.2 (p. 7, PDF 8: `Φ`), §2.3 (p. 7,
PDF 8: cuts, (2.3)), App. A.1 (p. 21–22, PDF 22–23: deletion/contraction minors).

* A multigraph on the vertex set `Fin n` with `m` labelled edges is a map `ends : Fin m → Fin n × Fin n`
  (the two endpoints of each edge; the order of a pair carries no meaning). Parallel edges (two labels
  with the same endpoints) and self-loops (`(ends e).1 = (ends e).2`) are allowed.
* A configuration is the finset `F` of **failed** edge labels. Under failure probabilities `q`
  (independent edges) it has probability `Π_{e∈F} q_e · Π_{e∉F} (1 − q_e)` (`configProb`), and the
  expectation of `f` is the finite sum `expect q f`. The working graph `workingGraph ends F` joins
  `a ≠ b` when some working edge has endpoints `a, b` (a loop joins nothing).
* `unrel ends q` is the probability that the working graph is disconnected; `connProb ends q` is the
  probability that it is connected (`R_G`). With weights `w`, edges fail with probability `e^{−w_e}`
  (`expNeg w`).
* `numComponents ends F` is `K`, the number of working components; `partitionOf ends F` is `Π`, the
  partition of the vertices into working components (as a `Setoid`). For any partition `π`,
  `numBlocks π` is its number of blocks and `pivotal ends π e = b_e(π) = 1` exactly when `π` has two
  blocks and the endpoints of `e` lie in different blocks (a loop has mark `0`).
* A **cut** is a nontrivial bipartition `{S, V∖S}` of the vertices with the two shores identified:
  the unordered pair `s(S, Sᶜ)` of `Sym2 (Finset (Fin n))` with `S` nonempty and `S ≠ V`. `cuts n`
  is the finset of all cuts. An edge crosses a cut when its endpoints lie on different shores;
  `cutWeight ends w C = Σ_{e crosses C} w_e`, `minCut ends w = min_C w(C)` (`λ`; `0` when there is no
  cut, i.e. `n ≤ 1`, which never occurs under the standing assumption `n ≥ 2`),
  `cutSum ends w = Σ_C e^{−w(C)}` (`z`), and `pairCount n = n(n−1)/2` (`M`).
* The design instance `(G, q⁰, A, b)` of (1.1): `q_e(x) = q⁰_e e^{−x_e}`, `w_e(x) = −log q⁰_e + x_e`,
  `X = {x ≥ 0 : Ax ≤ b}`, `u(x) = unrel ends (q(x))`, `u* = min_X u` (written `sInf (u '' X)`: `X`
  is nonempty (`0 ∈ X`) and compact and `u` is continuous, so the infimum is attained),
  `λ(x)`, `z(x)`, `Φ(x) = −log(1 − u(x))`.
* `IsMinor ends q ends' q'`: the graph `ends'` on `Fin n'` with failure probabilities `q'` is an
  iterated deletion/contraction minor of `(ends, q)` with inherited failure probabilities: for
  disjoint label sets `Del` (deleted) and `Con` (contracted), the vertices of the minor are the
  connected components of `(V, Con)` (through a surjection `f` whose fibres are those components),
  its edges are the labels outside `Del ∪ Con` (through a bijection `g`), each with the images of
  its endpoints and its original failure probability. Contracting edges one at a time gives the
  same graph as contracting the set at once, so iterated minors are exactly these.
-/

/-- Edge endpoints of a multigraph on `Fin n` with `m` labelled edges. -/
abbrev Ends (n m : ℕ) := Fin m → Fin n × Fin n

/-- The working graph when the edges in `F` have failed. -/
def workingGraph {n m : ℕ} (ends : Ends n m) (F : Finset (Fin m)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b => ∃ e, e ∉ F ∧ ends e = (a, b)

/-- The multigraph itself (no edge failed) is connected. -/
def IsConnectedGraph {n m : ℕ} (ends : Ends n m) : Prop := (workingGraph ends ∅).Connected

/-- Probability of the failure set `F` under independent failure probabilities `q`. -/
def configProb {m : ℕ} (q : Fin m → ℝ) (F : Finset (Fin m)) : ℝ :=
  (∏ e ∈ F, q e) * ∏ e ∈ Fᶜ, (1 - q e)

/-- Expectation of a function of the failure set. -/
def expect {m : ℕ} (q : Fin m → ℝ) (f : Finset (Fin m) → ℝ) : ℝ :=
  ∑ F : Finset (Fin m), configProb q F * f F

/-- Probability of an event of the failure set. -/
def prob {m : ℕ} (q : Fin m → ℝ) (P : Finset (Fin m) → Prop) : ℝ :=
  expect q fun F => if P F then 1 else 0

/-- The working graph is disconnected. -/
def Disconnected {n m : ℕ} (ends : Ends n m) (F : Finset (Fin m)) : Prop :=
  ¬ (workingGraph ends F).Connected

/-- Unreliability: the probability that the working edges leave the graph disconnected. -/
def unrel {n m : ℕ} (ends : Ends n m) (q : Fin m → ℝ) : ℝ :=
  prob q fun F => Disconnected ends F

/-- Connectivity probability `R`. -/
def connProb {n m : ℕ} (ends : Ends n m) (q : Fin m → ℝ) : ℝ :=
  prob q fun F => (workingGraph ends F).Connected

/-- Failure probabilities `e^{−w_e}` of weights `w`. -/
def expNeg {m : ℕ} (w : Fin m → ℝ) : Fin m → ℝ := fun e => Real.exp (-w e)

/-- `R_G(w)`: probability that edges failing independently with probability `e^{−w_e}` form a
connected graph. -/
def connW {n m : ℕ} (ends : Ends n m) (w : Fin m → ℝ) : ℝ := connProb ends (expNeg w)

/-- `−log R_G(w)` with the value `+∞` when `R_G(w) = 0`. -/
def negLogConnW {n m : ℕ} (ends : Ends n m) (w : Fin m → ℝ) : EReal :=
  if connW ends w = 0 then ⊤ else ((-Real.log (connW ends w) : ℝ) : EReal)

/-- Unreliability under failure probabilities `e^{−w_e}`. -/
def unrelW {n m : ℕ} (ends : Ends n m) (w : Fin m → ℝ) : ℝ := unrel ends (expNeg w)

/-- `K`: the number of working components. -/
def numComponents {n m : ℕ} (ends : Ends n m) (F : Finset (Fin m)) : ℕ :=
  Nat.card (workingGraph ends F).ConnectedComponent

/-- `Π`: the partition of the vertices into working components. -/
def partitionOf {n m : ℕ} (ends : Ends n m) (F : Finset (Fin m)) : Setoid (Fin n) :=
  Setoid.ker (workingGraph ends F).connectedComponentMk

/-- Number of blocks of a partition. -/
def numBlocks {n : ℕ} (π : Setoid (Fin n)) : ℕ := Nat.card (Quotient π)

/-- The pivotal mark `b_e(π) = 1{π has two blocks and the endpoints of e lie in different blocks}`. -/
def pivotal {n m : ℕ} (ends : Ends n m) (π : Setoid (Fin n)) (e : Fin m) : ℝ :=
  if numBlocks π = 2 ∧ ¬ π.r (ends e).1 (ends e).2 then 1 else 0

/-- A cut: an unordered pair of shores. -/
abbrev Cut (n : ℕ) := Sym2 (Finset (Fin n))

/-- All cuts: `{S, Sᶜ}` with `S` nonempty and `S ≠ V`, shores identified. -/
def cuts (n : ℕ) : Finset (Cut n) :=
  (Finset.univ.filter fun S : Finset (Fin n) => S.Nonempty ∧ S ≠ Finset.univ).image
    fun S => s(S, Sᶜ)

/-- The cut built from the shore `S` (a cut when `S` is nonempty and `S ≠ V`). -/
def cutOfShore {n : ℕ} (S : Finset (Fin n)) : Cut n := s(S, Sᶜ)

/-- Edge `e` crosses the cut `C`: its endpoints lie on different shores. -/
def Crosses {n m : ℕ} (ends : Ends n m) (C : Cut n) (e : Fin m) : Prop :=
  ∃ S T, C = s(S, T) ∧ (ends e).1 ∈ S ∧ (ends e).2 ∈ T

/-- Cut weight `w(C) = Σ_{e crosses C} w_e`. -/
def cutWeight {n m : ℕ} (ends : Ends n m) (w : Fin m → ℝ) (C : Cut n) : ℝ :=
  ∑ e, if Crosses ends C e then w e else 0

/-- Minimum cut weight `λ` (`0` if there is no cut). -/
def minCut {n m : ℕ} (ends : Ends n m) (w : Fin m → ℝ) : ℝ :=
  if h : (cuts n).Nonempty then (cuts n).inf' h (cutWeight ends w) else 0

/-- Cut sum `z = Σ_C e^{−w(C)}`. -/
def cutSum {n m : ℕ} (ends : Ends n m) (w : Fin m → ℝ) : ℝ :=
  ∑ C ∈ cuts n, Real.exp (-cutWeight ends w C)

/-- `M = n(n−1)/2`. -/
def pairCount (n : ℕ) : ℝ := (n.choose 2 : ℝ)

/-- The design instance `(G, q⁰, A, b)` of (1.1). -/
structure Instance (n m k : ℕ) where
  /-- Edge endpoints. -/
  ends : Ends n m
  /-- Base failure probabilities `q⁰`. -/
  q0 : Fin m → ℝ
  /-- Resource matrix `A ∈ ℝ^{k×m}`. -/
  A : Fin k → Fin m → ℝ
  /-- Budgets `b ∈ ℝ^k`. -/
  b : Fin k → ℝ

/-- Standing assumptions on the network: `n ≥ 2`, `G` connected, `0 < q⁰_e ≤ 1`. -/
def NetStanding {n m : ℕ} (ends : Ends n m) (q0 : Fin m → ℝ) : Prop :=
  2 ≤ n ∧ IsConnectedGraph ends ∧ ∀ e, 0 < q0 e ∧ q0 e ≤ 1

/-- Standing assumptions of (1.1): the network ones, `k ≥ 1`, `A_ij > 0`, `b_i > 0`. -/
def Instance.Standing {n m k : ℕ} (I : Instance n m k) : Prop :=
  NetStanding I.ends I.q0 ∧ 1 ≤ k ∧ (∀ i j, 0 < I.A i j) ∧ ∀ i, 0 < I.b i

/-- `q_e(x) = q⁰_e e^{−x_e}`. -/
def failProbAt {m : ℕ} (q0 x : Fin m → ℝ) : Fin m → ℝ := fun e => q0 e * Real.exp (-x e)

/-- `w_e(x) = −log q⁰_e + x_e`. -/
def weightAt {m : ℕ} (q0 x : Fin m → ℝ) : Fin m → ℝ := fun e => -Real.log (q0 e) + x e

/-- `u(x)` for a network `(G, q⁰)`. -/
def risk {n m : ℕ} (ends : Ends n m) (q0 x : Fin m → ℝ) : ℝ := unrel ends (failProbAt q0 x)

/-- `u(x)`. -/
def Instance.u {n m k : ℕ} (I : Instance n m k) (x : Fin m → ℝ) : ℝ := risk I.ends I.q0 x

/-- `X = {x ∈ ℝ^m_+ : Ax ≤ b}`. -/
def Instance.feasible {n m k : ℕ} (I : Instance n m k) : Set (Fin m → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ ∀ i, ∑ j, I.A i j * x j ≤ I.b i}

/-- `u* = min_{x ∈ X} u(x)`. -/
def Instance.uStar {n m k : ℕ} (I : Instance n m k) : ℝ := sInf (I.u '' I.feasible)

/-- `λ(x)`. -/
def Instance.lam {n m k : ℕ} (I : Instance n m k) (x : Fin m → ℝ) : ℝ :=
  minCut I.ends (weightAt I.q0 x)

/-- `z(x)`. -/
def Instance.z {n m k : ℕ} (I : Instance n m k) (x : Fin m → ℝ) : ℝ :=
  cutSum I.ends (weightAt I.q0 x)

/-- `Φ(x) = −log(1 − u(x))`. -/
def Instance.Phi {n m k : ℕ} (I : Instance n m k) (x : Fin m → ℝ) : ℝ :=
  -Real.log (1 - I.u x)

/-- `(ends', q')` on `Fin n'` is an iterated deletion/contraction minor of `(ends, q)` with
inherited failure probabilities. -/
def IsMinor {n m n' m' : ℕ} (ends : Ends n m) (q : Fin m → ℝ) (ends' : Ends n' m')
    (q' : Fin m' → ℝ) : Prop :=
  ∃ (Del Con : Finset (Fin m)) (f : Fin n → Fin n') (g : Fin m' → Fin m),
    Disjoint Del Con ∧ Function.Surjective f ∧
    (∀ a b, f a = f b ↔ (workingGraph ends (Finset.univ \ Con)).Reachable a b) ∧
    Function.Injective g ∧ (∀ e', g e' ∉ Del ∧ g e' ∉ Con) ∧
    (∀ e, e ∉ Del → e ∉ Con → ∃ e', g e' = e) ∧
    (∀ e', ends' e' = (f (ends (g e')).1, f (ends (g e')).2) ∨
      ends' e' = (f (ends (g e')).2, f (ends (g e')).1)) ∧
    ∀ e', q' e' = q (g e')

end NetUnrelDesign.Main


