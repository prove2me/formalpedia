-- Prove2me | Definitions.Def_FeasibleBasesHC_Structure_Setting
-- name    : FeasibleBasesHC_Structure_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:02.68096+00:00
-- url     : https://prove2.me/theorems/a8298af4-8bd0-47b3-989e-186f240674fe
-- title:
--   §2–§3.3, pp. 2–12 — 𝒲ℋβ(G), feasible and ultimate bases, G′, thick and thin arcs
-- statement:
--   Let $G$ be a loopless digraph on $[n]$ and $0<\beta<1$. The polytope $\mathcal{WH}_\beta(G)$ consists of arc flows $x_{ij}$ and nonroot slacks $y_i$ satisfying equations (2.10)–(2.13) and bounds (2.14)–(2.15). In particular,
--
--   $$\Psi(1)-\beta\Phi(1)=1-\beta^n,\quad \Psi(1)=1,\quad \Psi(i)-\beta\Phi(i)=0,\quad \Psi(i)-y_i=\beta^{n-1},\quad 0\le y_i\le\beta-\beta^{n-1}.$$
--
--   A basis $(A,Y,L,U)$ partitions nonroot slack indices, has $|A|+|Y|=2n$ independent equality columns, and fixes flows outside $A$ and nonbasic slacks at their stated bounds. It is feasible when the resulting solution lies in the polytope. $\Gamma(G,\beta)$ is the set of feasible bases; $\Gamma(G)$ comprises bases feasible eventually as $\beta\to1^-$.
--
--   The split digraph $G'$ has vertices $v_i,w_i$, original arc $(i,j)$ represented by $(w_i,v_j)$, and a slack arc $(v_i,w_i)$ for each $i\ne1$. Its supply at $v_1$ is $-\beta^n$, as (2.10) and (2.12) require; the displayed vector on pp. 6–7 mistakenly prints $-\beta^{n-1}$ there. A basic arc is thick if its flow is $1-O(1-\beta)$, and thin if its flow is $O(1-\beta)$. This common model is used by every theorem in the mission.
--
--   **Formalization Note** Paper node $1$ is `0 : Fin n`, so `[NeZero n]` is required. The big-O statements use eventual uniform constant bounds over the unique basic solution.
-- source:
--   Kalinowski, Mohammadian, Feasible Bases for a Polytope Related to the Hamilton Cycle Problem, arXiv:1907.12691v1, pp. 2–12, (2.10)–(2.15), Definitions 3 and 7

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_GNF

namespace FeasibleBasesHC.Structure
open Filter

structure Digraph (n : ℕ) where
  E : Finset (Fin n × Fin n)
  loopless : ∀ i : Fin n, (i, i) ∉ E

structure Basis (n : ℕ) where
  A : Finset (Fin n × Fin n)
  Y : Finset (Fin n)
  L : Finset (Fin n)
  U : Finset (Fin n)

variable {n : ℕ} [NeZero n]

/-- Basic x and y column indices. -/
def Basis.vars (b : Basis n) : Finset ((Fin n × Fin n) ⊕ Fin n) :=
  b.A.image Sum.inl ∪ b.Y.image Sum.inr

/-- The basis partition and its 2n columns. -/
def Basis.Shape (G : Digraph n) (b : Basis n) : Prop :=
  b.A ⊆ G.E ∧ b.Y ∪ b.L ∪ b.U = Finset.univ.erase 0 ∧
  Disjoint b.Y b.L ∧ Disjoint b.Y b.U ∧ Disjoint b.L b.U ∧
  b.vars.card = 2 * n

def inflow (G : Digraph n) (x : Fin n × Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ e ∈ G.E.filter (fun e => e.2 = i), x e

def outflow (G : Digraph n) (x : Fin n × Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ e ∈ G.E.filter (fun e => e.1 = i), x e

/-- Equations (2.10)--(2.13), with unused coordinates fixed to zero. -/
def WHCore (G : Digraph n) (beta : ℝ) (x : Fin n × Fin n → ℝ)
    (y : Fin n → ℝ) : Prop :=
  (∀ e ∉ G.E, x e = 0) ∧ y 0 = 0 ∧
  (∀ i, outflow G x i - beta * inflow G x i = if i = 0 then 1 - beta ^ n else 0) ∧
  (∀ i, outflow G x i - (if i = 0 then 0 else y i) =
    if i = 0 then 1 else beta ^ (n - 1))

/-- The polytope 𝒲ℋβ(G), including (2.14)--(2.15). -/
def WH (G : Digraph n) (beta : ℝ) (x : Fin n × Fin n → ℝ)
    (y : Fin n → ℝ) : Prop :=
  WHCore G beta x y ∧ (∀ e ∈ G.E, 0 ≤ x e) ∧
  (∀ i : Fin n, i ≠ 0 → 0 ≤ y i ∧ y i ≤ beta - beta ^ (n - 1))

/-- Column of the 2n by (|E|+n-1) equality matrix. -/
def WHColumn (beta : ℝ) (z : (Fin n × Fin n) ⊕ Fin n) : (Fin n ⊕ Fin n) → ℝ :=
  fun row => match z, row with
  | Sum.inl e, Sum.inl i =>
      (if e.1 = i then 1 else 0) - beta * (if e.2 = i then 1 else 0)
  | Sum.inl e, Sum.inr i => if e.1 = i then 1 else 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr j, Sum.inr i => if j = i then -1 else 0

def IsIndependent (beta : ℝ) (b : Basis n) : Prop :=
  LinearIndependent ℝ (fun z : b.vars => WHColumn beta z.1)

/-- The unique basic solution, including nonsingularity and nonbasic values. -/
def IsBasicSolution (G : Digraph n) (beta : ℝ) (b : Basis n)
    (x : Fin n × Fin n → ℝ) (y : Fin n → ℝ) : Prop :=
  b.Shape G ∧ IsIndependent beta b ∧ WHCore G beta x y ∧
  (∀ e ∉ b.A, x e = 0) ∧
  (∀ i ∈ b.L, y i = 0) ∧
  (∀ i ∈ b.U, y i = beta - beta ^ (n - 1))

/-- Γ(G,β): feasible bases at a fixed discount factor. -/
def Gam (G : Digraph n) (beta : ℝ) : Set (Basis n) :=
  {b | 0 < beta ∧ beta < 1 ∧ ∃ x y, IsBasicSolution G beta b x y ∧ WH G beta x y}

/-- Γ(G): bases feasible eventually as β approaches one from below. -/
def GamUlt (G : Digraph n) : Set (Basis n) :=
  {b | Filter.Eventually (fun beta : ℝ => b ∈ Gam G beta) (nhdsWithin (1 : ℝ) (Set.Iio 1))}

/-- The finite family 𝓑 of column sets independent at some β∈(0,1). -/
def CandidateBasis (G : Digraph n) (b : Basis n) : Prop :=
  b.Shape G ∧ ∃ beta : ℝ, 0 < beta ∧ beta < 1 ∧ IsIndependent beta b

abbrev GpVertex (n : ℕ) := Fin n ⊕ Fin n
abbrev GpArc (n : ℕ) := (Fin n × Fin n) ⊕ Fin n

/-- The split digraph G′. `inl i` is vᵢ and `inr i` is wᵢ. -/
def Gp (G : Digraph n) (beta : ℝ) : GNF (GpVertex n) (GpArc n) where
  arcs := G.E.image Sum.inl ∪ (Finset.univ.erase (0 : Fin n)).image Sum.inr
  tail := fun a => match a with
    | Sum.inl e => Sum.inr e.1
    | Sum.inr i => Sum.inl i
  head := fun a => match a with
    | Sum.inl e => Sum.inl e.2
    | Sum.inr i => Sum.inr i
  mu := fun a => match a with
    | Sum.inl _ => beta
    | Sum.inr _ => 1
  -- At v₁, (2.10) and (2.12) give -βΦ(1) = -βⁿ. The displayed
  -- supply vector on pp. 6–7 prints -βⁿ⁻¹ there, an algebraic slip.
  supply := fun v => match v with
    | Sum.inl i => if i = 0 then -(beta ^ n) else -(beta ^ (n - 1))
    | Sum.inr i => if i = 0 then 1 else beta ^ (n - 1)
  cap := fun a => match a with
    | Sum.inl _ => none
    | Sum.inr _ => some (beta - beta ^ (n - 1))

/-- B′, the basic arc set in G′. -/
def Bp (b : Basis n) : Finset (GpArc n) := b.vars

def splitFlow (x : Fin n × Fin n → ℝ) (y : Fin n → ℝ) : GpArc n → ℝ
  | Sum.inl e => x e
  | Sum.inr i => y i

/-- The quantified O(1-β) reading of a thick arc. -/
def thick (G : Digraph n) (b : Basis n) (e : Fin n × Fin n) : Prop :=
  e ∈ b.A ∧ ∃ C : ℝ, 0 ≤ C ∧
    Filter.Eventually (fun beta : ℝ => ∀ x y,
      IsBasicSolution G beta b x y → |1 - x e| ≤ C * (1 - beta)) (nhdsWithin (1 : ℝ) (Set.Iio 1))

/-- The quantified O(1-β) reading of a thin arc. -/
def thin (G : Digraph n) (b : Basis n) (e : Fin n × Fin n) : Prop :=
  e ∈ b.A ∧ ∃ C : ℝ, 0 ≤ C ∧
    Filter.Eventually (fun beta : ℝ => ∀ x y,
      IsBasicSolution G beta b x y → |x e| ≤ C * (1 - beta)) (nhdsWithin (1 : ℝ) (Set.Iio 1))

noncomputable def thickArcs (G : Digraph n) (b : Basis n) : Finset (Fin n × Fin n) := by
  classical
  exact b.A.filter (thick G b)

noncomputable def thinArcs (G : Digraph n) (b : Basis n) : Finset (Fin n × Fin n) := by
  classical
  exact b.A.filter (thin G b)

/-- A set of arcs covers every vertex exactly once. -/
def GNF.IsPerfectMatching {V A : Type*} [Fintype V] [DecidableEq V]
    (N : GNF V A) (M : Finset A) : Prop :=
  M ⊆ N.arcs ∧ ∀ v : V, ∃! a : A, a ∈ M ∧ (N.tail a = v ∨ N.head a = v)

end FeasibleBasesHC.Structure


