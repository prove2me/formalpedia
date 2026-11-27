-- Prove2me | Definitions.Def_NashStackelberg_Supplement_TrivialNASP
-- name    : NashStackelberg_Supplement_TrivialNASP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:30:54.614922+00:00
-- url     : https://prove2.me/theorems/286d4df6-1b37-4b81-928b-3a60995dac94
-- title:
--   Definition 8 — trivial NASPs and their rational instances
-- statement:
--   A **NASP** (Definition 4) is a simultaneous game among $n$ players in which player $i$ is a leader with variables $w^i$ whose followers play a game $P(w^i)$; player $i$'s pure strategies are the points $x^i=(w^i,y^i)$ of its feasible region $\mathcal F^i=\{x^i\in\mathcal S^i:\ y^i\in\mathrm{SOL}(P(w^i))\}$, and it minimizes $(c^i)^\top x^i+(C^ix^{-i})^\top x^i$.
--
--   A NASP is **trivial** (Definition 8) if $n=2$ and each leader has a **single follower** who solves a **linear program with a simple parameterization** in its leader's variables:
--   $$
--   \min_{y}\ (c_f+Hw)^\top y\quad\text{s.t.}\quad Aw+By\le b .
--   $$
--
--   A **rational instance** of a trivial NASP consists of, for each player $i\in\{0,1\}$: the numbers $n_\ell$ of leader variables, $d$ of follower variables, $r$ of follower constraints and $r_S$ of leader constraints; the follower's data $c_f\in\mathbb Q^d$, $H\in\mathbb Q^{d\times n_\ell}$, $A\in\mathbb Q^{r\times n_\ell}$, $B\in\mathbb Q^{r\times d}$, $b\in\mathbb Q^r$; the leader's polyhedron $\mathcal S=\{x\in\mathbb R^{n_\ell+d}: A_Sx\le b_S\}$ and cost vector $c\in\mathbb Q^{n_\ell+d}$; and the blocks $C_{ij}$ of the bilinear cost terms. The instance describes the trivial NASP with these data, read as real numbers.
--
--   These are the inputs of the decision problems of Theorems 1 and 2.
--
--   **Formalization Note** The trivial NASP is the published `NashStackelberg.NASP` with the published `FollowerGame` having $K=1$ follower and quadratic term $Q=0$. A rational player's joint vector is indexed leader-first by $\{0,\dots,n_\ell+d-1\}$. The followers' cross-coupling (unused with one follower) is set to $0$; the diagonal blocks $C_{ii}$ never enter the cost. No boundedness, nonemptiness or integrality is imposed.
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, Definition 8, p.30; §4, p.8; Definitions 3–4, pp.7–8

import Mathlib
import Definitions.Def_NashStackelberg_NASP_Var

open Matrix

namespace NashStackelberg.Supplement

/-!
# Trivial NASPs and their rational instances

Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*,
arXiv:1910.06452v6, Definition 8, p.30 (and §4, p.8: "two leaders have a single follower each,
and each follower solves a parametrized linear problem"), on Definitions 3–4, pp.7–8.

* `IsTrivial N`: the NASP `N` has `n = 2` players, and each leader has exactly one follower
  (`K = 1`) whose problem is a linear program (`Q = 0`) with a simple parameterization in its
  leader's variables (`min (c + H w)ᵀ y  s.t.  A w + B y ≤ b`, the published `FollowerGame` with
  one follower and no quadratic term).
* `RatPlayer`, `RatInstance`: the rational data of a trivial NASP, as an input of the decision
  problems of Theorems 1–2. `RatInstance.toNASP` is the NASP it describes (data cast to `ℝ`).

**Formalization Note.** A rational player stores its joint vector `xⁱ = (wⁱ, yⁱ)` with index type
`Fin (nl + d)` (the first `nl` coordinates are the leader's, the last `d` the follower's);
`RatPlayer.idx` maps the published index type `Fin nl ⊕ Σ k : Fin 1, Fin d` onto it. The
followers' cross-coupling `Cₖₖ'` of the published `FollowerGame` is never used when `K = 1` and
is set to `0`; the diagonal blocks `C i i` of the leaders' cost are never used by `NASP.cost` and
are kept only to make the data rectangular. No boundedness, nonemptiness or integer requirement is
imposed: every polyhedron and every follower LP may be empty or unbounded.
-/

/-- **Trivial NASP** (Definition 8, p.30): a NASP with two players in which every leader has a
single follower solving a linear program with a simple parameterization with respect to its
leader's variables, i.e. the followers' game has `K = 1` follower and no quadratic term. -/
def IsTrivial (N : NASP 2) : Prop :=
  ∀ i, (N.P i).K = 1 ∧ ∀ k, (N.P i).Q k = 0

/-- The rational data of one player of a trivial NASP: the leader has `nl` variables `w`, the
follower `d` variables `y`; the follower solves `min (cf + H w)ᵀ y  s.t.  A w + B y ≤ b`
(`r` rows); the leader's polyhedron is `𝓢 = {x ∈ ℝ^{nl+d} : AS x ≤ bS}` (`rS` rows) and its
linear cost vector is `c`. -/
structure RatPlayer where
  /-- Number of leader variables. -/
  nl : ℕ
  /-- Number of follower variables. -/
  d : ℕ
  /-- Number of rows of the follower's LP. -/
  r : ℕ
  /-- Number of rows of the leader's polyhedron `𝓢`. -/
  rS : ℕ
  /-- Linear cost of the follower. -/
  cf : Fin d → ℚ
  /-- Simple parameterization `(H w)ᵀ y` of the follower's objective. -/
  H : Matrix (Fin d) (Fin nl) ℚ
  /-- Leader part of the follower's constraints. -/
  A : Matrix (Fin r) (Fin nl) ℚ
  /-- Follower part of the follower's constraints. -/
  B : Matrix (Fin r) (Fin d) ℚ
  /-- Right-hand side of the follower's constraints. -/
  b : Fin r → ℚ
  /-- Constraint matrix of `𝓢` on the joint vector `(w, y)`. -/
  AS : Matrix (Fin rS) (Fin (nl + d)) ℚ
  /-- Right-hand side of `𝓢`. -/
  bS : Fin rS → ℚ
  /-- Linear cost `c` of the leader on the joint vector `(w, y)`. -/
  c : Fin (nl + d) → ℚ

/-- The rational data of a trivial NASP: two players and the blocks `C i j` of the bilinear
cost terms `(Cⁱ x⁻ⁱ)ᵀ xⁱ`. -/
structure RatInstance where
  /-- The two players. -/
  P : Fin 2 → RatPlayer
  /-- Block of `Cⁱ` acting on player `j`'s joint vector (only `j ≠ i` enters the cost). -/
  C : (i j : Fin 2) → Matrix (Fin ((P i).nl + (P i).d)) (Fin ((P j).nl + (P j).d)) ℚ

/-- The follower's LP of a rational player, as a published `FollowerGame` with one follower and
`Q = 0`, data cast to `ℝ`. -/
def RatPlayer.toFollowerGame (p : RatPlayer) : FollowerGame p.nl where
  K := 1
  d := fun _ => p.d
  Q := fun _ => 0
  Q_psd := fun _ v => by simp
  c := fun _ l => (p.cf l : ℝ)
  C := fun _ _ => 0
  H := fun _ => p.H.map (fun q : ℚ => (q : ℝ))
  r := fun _ => p.r
  A := fun _ => p.A.map (fun q : ℚ => (q : ℝ))
  B := fun _ => p.B.map (fun q : ℚ => (q : ℝ))
  b := fun _ l => (p.b l : ℝ)

/-- Position of a coordinate of the published joint index type
`Fin nl ⊕ Σ k : Fin 1, Fin d` in `Fin (nl + d)`: the leader first, then the follower. -/
def RatPlayer.idx (p : RatPlayer) : Fin p.nl ⊕ (Σ _ : Fin 1, Fin p.d) → Fin (p.nl + p.d)
  | Sum.inl a => Fin.castAdd p.d a
  | Sum.inr ⟨_, l⟩ => Fin.natAdd p.nl l

/-- The trivial NASP described by rational data (all data cast to `ℝ`). -/
def RatInstance.toNASP (I : RatInstance) : NASP 2 where
  nl := fun i => (I.P i).nl
  P := fun i => (I.P i).toFollowerGame
  rS := fun i => (I.P i).rS
  AS := fun i ρ v => ((I.P i).AS ρ ((I.P i).idx v) : ℝ)
  bS := fun i ρ => ((I.P i).bS ρ : ℝ)
  c := fun i v => ((I.P i).c ((I.P i).idx v) : ℝ)
  C := fun i j u v => (I.C i j ((I.P i).idx u) ((I.P j).idx v) : ℝ)

end NashStackelberg.Supplement


