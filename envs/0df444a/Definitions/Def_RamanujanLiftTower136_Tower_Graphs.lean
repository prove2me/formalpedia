-- Prove2me | Definitions.Def_RamanujanLiftTower136_Tower_Graphs
-- name    : RamanujanLiftTower136_Tower_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:35:09.203814+00:00
-- url     : https://prove2.me/theorems/0090705c-637a-4c7d-8a0a-a39c79ce81d2
-- title:
--   Labeled multigraphs, covers, adjacency, and the counting inner product
-- statement:
--   A labeled incidence system on vertex set $V$ and label set $L$ specifies maps $f_j:V\to V$ and a reversal $j\mapsto j^*$. Validity means each $f_j$ is bijective, reversal is involutive, and $f_{j^*}f_j=\mathrm{id}$. Connectedness means reachability by finitely many incidences. Non-bipartiteness excludes a Boolean coloring that changes along every incidence.
--
--   Adjacency retains every label:
--   $$ (Ah)(t)=\sum_{j\in L}h(f_j(t)),\qquad A(t,s)=\#\{j:f_j(t)=s\}. $$
--   Half-loops contribute one and paired loop labels contribute two. A label-preserving two-cover is a surjection commuting with every neighbor map and the reversal, with exactly two vertices in each fiber.
--
--   For the arithmetic family, define $B_{n,p}$ with weights $(-1)^{\beta_n(t,j)}$. The explicit map from a pair of functions $(h_+,h_-)$ to the lifted vertices has values $(h_+(t)\pm h_-(t))/\sqrt2$ on the two sheets. The decomposition predicate requires this map to be bijective, preserve the sum of squares, intertwine adjacency with $A_{n,p}\oplus B_{n,p}$, and satisfy
--   $$\sum_t(B_{n,p}h(t))^2\le(2\sqrt p)^2\sum_t h(t)^2.$$
--   This is the operator-norm bound for the counting inner product. The generic incidence data carry no spectral or connectivity assumptions.
-- source:
--   Olga Kharlampovich, Igor Pak, Alina Vdovina, STOC 2027 submission #136 (October 2026), source.pdf SHA-256 27d691a82d8af863e511e7e6b00cee95779d914645846d2974f876836db8f83b, p.7 (PDF p.8), §2; §4, (4.3)–(4.4); §6, (6.4)–(6.5). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/136.pdf

import Definitions.Def_RamanujanLiftTower136_Tower_Construction

noncomputable section

namespace RamanujanLiftTower136.Tower
open Classical

/-- Raw incidence data; validity is asserted, not assumed, for the arithmetic family. -/
structure LabeledGraphData (V L : Type) where
  step : V → L → V
  rev : L → L

def LabeledGraphData.Valid {V L : Type} (G : LabeledGraphData V L) : Prop :=
  Function.Involutive G.rev ∧ (∀ j, Function.Bijective (fun t => G.step t j)) ∧
    ∀ t j, G.step (G.step t j) (G.rev j) = t

def LabeledGraphData.Connected {V L : Type} (G : LabeledGraphData V L) : Prop :=
  ∀ t u, Relation.ReflTransGen (fun x y => ∃ j, G.step x j = y) t u

def LabeledGraphData.NonBipartite {V L : Type} (G : LabeledGraphData V L) : Prop :=
  ¬ ∃ chi : V → Bool, ∀ t j, chi (G.step t j) ≠ chi t

def LabeledGraphData.adjacency {V L : Type} [Fintype L]
    (G : LabeledGraphData V L) (h : V → ℂ) (t : V) : ℂ := ∑ j, h (G.step t j)

def LabeledGraphData.matrix {V L : Type} [Fintype L]
    (G : LabeledGraphData V L) : Matrix V V ℝ :=
  fun t s => ((Finset.univ.filter (fun j => G.step t j = s)).card : ℝ)

def LabeledGraphData.TwoCover {V W L : Type} (G : LabeledGraphData V L)
    (H : LabeledGraphData W L) (proj : W → V) : Prop :=
  Function.Surjective proj ∧ G.rev = H.rev ∧
  (∀ w j, proj (H.step w j) = G.step (proj w) j) ∧
  ∀ t, Nat.card {w : W // proj w = t} = 2

def graph (p n : ℕ) : LabeledGraphData (Vertex n) (Label p) := ⟨neighbor p n, reverse p⟩
def adjacency (p n : ℕ) := (graph p n).adjacency
def adjacencyReal (p n : ℕ) (h : Vertex n → ℝ) (t : Vertex n) : ℝ :=
  ∑ j, h (neighbor p n t j)
def signedAdjacency (p n : ℕ) (h : Vertex n → ℝ) (t : Vertex n) : ℝ :=
  ∑ j, signing p n t j * h (neighbor p n t j)
def liftRule (p n : ℕ) : Prop :=
  ∀ t j b, neighbor p (n+1) (sheet n t b) j =
    sheet n (neighbor p n t j) (Bool.xor b (liftBit p n t j))
def reverseBitRule (p n : ℕ) : Prop :=
  ∀ t j, liftBit p n t j = liftBit p n (neighbor p n t j) (reverse p j)

def countingSquare (n : ℕ) (h : Vertex n → ℝ) : ℝ := ∑ t, (h t)^2
/-- Normalized explicit change from fiber-even/odd coordinates to upstairs functions. -/
def haar (n : ℕ) (h : (Vertex n → ℝ) × (Vertex n → ℝ)) (w : Vertex (n+1)) : ℝ :=
  (h.1 (reduction n w) + if w.val < 2^n then h.2 (reduction n w) else -h.2 (reduction n w)) / Real.sqrt 2

def signedDecomposition (p n : ℕ) : Prop :=
  Function.Bijective (haar n) ∧
  (∀ h, countingSquare (n+1) (haar n h) = countingSquare n h.1 + countingSquare n h.2) ∧
  (∀ h, adjacencyReal p (n+1) (haar n h) =
    haar n (adjacencyReal p n h.1, signedAdjacency p n h.2)) ∧
  ∀ h, countingSquare n (signedAdjacency p n h) ≤
    (2 * Real.sqrt p)^2 * countingSquare n h

def spectralConclusion (p n : ℕ) : Prop :=
  (∀ t s, (graph p n).matrix t s = (graph p n).matrix s t) ∧
  (∀ (lambda : ℝ) (h : Vertex n → ℝ), h ≠ 0 →
    (∀ t, adjacencyReal p n h t = lambda * h t) → lambda < (p+1 : ℝ) →
    |lambda| ≤ 2 * Real.sqrt p) ∧ (graph p n).NonBipartite

end RamanujanLiftTower136.Tower


