-- Prove2me | Definitions.Def_SaturatedNet_Uniqueness_Model
-- name    : SaturatedNet_Uniqueness_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:54.434134+00:00
-- url     : https://prove2.me/theorems/c7a0f9b5-c645-4584-a5cf-555500af474f
-- title:
--   (1)–(4), p. 2; Notation, p. 5; §3.2–3.3, pp. 10–11 — saturated network equilibria, spectral radius, classes, basic and final classes, non-expansive networks, node partition
-- statement:
--   This file fixes the model of Massai, Como and Fagnani for saturated networks and the
--   spectral and graph-theoretic notions used by their uniqueness theory.
--
--   **Network and equilibria.** The nodes form a finite set $\mathcal V$. A *network* is a pair
--   $(P, w)$ with $P \in \mathbb R_+^{\mathcal V \times \mathcal V}$ entrywise nonnegative and
--   $w \in \mathbb R_+^{\mathcal V}$ nonnegative ($w_i = 0$ is allowed); an *exogenous flow* is any
--   $c \in \mathbb R^{\mathcal V}$, of any sign. For $a \ge 0$ the scalar saturation is
--   $S_0^{a}(y) = \min\{\max\{y, 0\}, a\}$, and the *inflow* to node $i$ at the state $x$ is
--   $(P^\top x + c)_i = \sum_j x_j P_{ji} + c_i$. A vector $x$ is a *network equilibrium* if
--
--   $$x_i = \min\Big\{\max\Big\{\sum_{j} x_j P_{ji} + c_i,\ 0\Big\},\ w_i\Big\}\qquad\text{for every node } i,$$
--
--   i.e. $x = S_0^w(P^\top x + c)$ (equations (1)–(3)). The set of equilibria is denoted $\mathcal X$.
--
--   **Spectral radius and blocks.** For a real square matrix $A$, $\rho(A)$ is its spectral radius:
--   the largest modulus of a *complex* eigenvalue of $A$. For a node set $V$, $P^{(VV)}$ is the
--   principal block of $P$ with rows and columns in $V$.
--
--   **Graph, classes.** The digraph $\mathcal G_P$ has a link $i \to j$ whenever $P_{ij} \ne 0$.
--   A node $i$ *reaches* $j$ if there is a directed path from $i$ to $j$ (the empty path included).
--   A *class* of $P$ is a strongly connected component of $\mathcal G_P$: a set $V$ containing some
--   node $i$ such that $V$ consists exactly of the nodes $j$ with $i$ reaching $j$ and $j$ reaching $i$.
--   A class $V$ is *basic* if $\rho(P^{(VV)}) = \rho(P)$, and *final* if no link of $\mathcal G_P$
--   leaves it ($P_{ij} = 0$ whenever $i \in V$, $j \notin V$). $P$ is *irreducible* if for all $i, j$
--   there is $l \ge 1$ with $(P^l)_{ij} > 0$.
--
--   **Non-expansive networks (Definition 1).** $(P, w)$ is non-expansive if $\rho(P) < 1$, or
--   $\rho(P) = 1$ and every basic class of $P$ is final.
--
--   **Node partition (19).** For an equilibrium $x$, node $i$ is *surplus* if
--   $c_i + \sum_k P_{ki} x_k > w_i$, *exposed* if $0 \le c_i + \sum_k P_{ki} x_k \le w_i$, and *deficit*
--   if $c_i + \sum_k P_{ki} x_k < 0$; these are the sets $\mathcal V_+^x$, $\mathcal V_0^x$, $\mathcal V_-^x$.
--
--   **Class projections.** For a class $V$ and an equilibrium $x$, the *upstream* nodes of $V$ are
--   the nodes outside $V$ from which $V$ can be reached. The class projection given $x$ is the set of
--   restrictions to $V$ of all equilibria $x'$ that agree with $x$ on every upstream node of $V$. The
--   exogenous flow into $V$ given $x$ is $u_j = c_j + \sum_{k \notin V} P_{kj} x_k$ for $j \in V$
--   (the paper's $c^{(l)} + \sum_{i<l} P^{(il)\top} x^{(i)}$). Finally, for vectors $a, b$ on a finite
--   nonempty index set, $\min_i\{a_i/b_i\}$ is the minimum of the ratios.
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note.** Nodes are a `Fintype` with decidable equality. The spectral radius is
--   Mathlib's `spectralRadius ℂ` of the complexified matrix, an element of $[0, \infty]$ (finite for
--   matrices); the real spectrum would miss complex eigenvalues. Three readings of the printed text are
--   made: the "connected components" of p. 10 are read as **strongly** connected components (the block
--   form (14) requires irreducible diagonal blocks and no backward links), with reachability including
--   the empty path so that a node without a self-loop that lies on no cycle forms a singleton class with
--   block $[0]$; the sums $\sum_{k \ne i}$ in (19) are read as the full sums $\sum_k$, which is the
--   argument of $S_0^{w_i}$ in (1) and is how Remark 5 and the proof of Theorem 1 use them (with the
--   literal $k \ne i$, (20) contradicts (1) whenever $P_{ii} \ne 0$); and "given
--   $(x^{(1)}, \dots, x^{(l-1)})$" of Theorem 2 is encoded by fixing $x$ on the upstream nodes of the
--   class, which is permutation-free. Non-expansiveness depends on $P$ only. The file also contains the
--   one-line fact that a class is nonempty, used to form the minima over a class.
-- source:
--   Massai, Como & Fagnani, Equilibria and Systemic Risk in Saturated Networks, arXiv:1912.04815v2, pp. 2, 5, 10–11, 16, (1)–(4), (14), Definition 1, (19), (34)–(37)

import Mathlib

namespace SaturatedNet.Uniqueness

open Finset

/-- The scalar saturation `S_0^a(y) = min{max{y, 0}, a}` of (3). -/
noncomputable def sat (a y : ℝ) : ℝ := min (max y 0) a

/-- The inflow `(Pᵀx + c)_i = Σ_j x_j P_{ji} + c_i` to node `i`, the argument of `S_0^{w_i}` in (1). -/
noncomputable def inflow {n : Type*} [Fintype n] (P : Matrix n n ℝ) (c x : n → ℝ) (i : n) : ℝ :=
  ∑ j, x j * P j i + c i

/-- `x` is a network equilibrium of `(P, w)` with exogenous flow `c`: it solves (1)–(2). -/
def IsEquilibrium {n : Type*} [Fintype n] (P : Matrix n n ℝ) (w c x : n → ℝ) : Prop :=
  ∀ i, x i = sat (w i) (inflow P c x i)

/-- The set `𝒳` of network equilibria of `(P, w)` with exogenous flow `c`. -/
def equilibria {n : Type*} [Fintype n] (P : Matrix n n ℝ) (w c : n → ℝ) : Set (n → ℝ) :=
  {x | IsEquilibrium P w c x}

/-- The spectral radius `ρ(A)` of a real square matrix, taken over `ℂ` (all complex eigenvalues),
as an element of `ℝ≥0∞`. -/
noncomputable def specRad {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℝ) : ENNReal :=
  spectralRadius ℂ (A.map (algebraMap ℝ ℂ))

/-- The principal block `P^{(VV)}` of `P` on the node set `V` (rows and columns in `V`). -/
def block {n : Type*} (P : Matrix n n ℝ) (V : Finset n) : Matrix V V ℝ :=
  P.submatrix Subtype.val Subtype.val

/-- `Reaches P i j`: there is a path (of length `≥ 0`) from `i` to `j` in the digraph `𝒢_P`,
whose links are the pairs `(a, b)` with `P_{ab} ≠ 0`. -/
def Reaches {n : Type*} (P : Matrix n n ℝ) (i j : n) : Prop :=
  Relation.ReflTransGen (fun a b => P a b ≠ 0) i j

/-- `V` is a class of `P`: a strongly connected component of `𝒢_P`. -/
def IsClass {n : Type*} (P : Matrix n n ℝ) (V : Finset n) : Prop :=
  ∃ i ∈ V, ∀ j, j ∈ V ↔ (Reaches P i j ∧ Reaches P j i)

/-- A class `V` is basic if `ρ(P^{(VV)}) = ρ(P)`. -/
def IsBasic {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) (V : Finset n) : Prop :=
  specRad (block P V) = specRad P

/-- A class `V` is final if no link of `𝒢_P` leaves it: `P_{ij} = 0` for `i ∈ V`, `j ∉ V`. -/
def IsFinal {n : Type*} (P : Matrix n n ℝ) (V : Finset n) : Prop :=
  ∀ i ∈ V, ∀ j ∉ V, P i j = 0

/-- `P` is irreducible (p. 5): for all `i, j` there is `l ≥ 1` with `(P^l)_{ij} > 0`. -/
def IsIrreducible {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) : Prop :=
  ∀ i j, ∃ l : ℕ, 1 ≤ l ∧ 0 < (P ^ l) i j

/-- Definition 1: the network is non-expansive if `ρ(P) < 1`, or `ρ(P) = 1` and every basic class
of `P` is final. (It depends on `P` only.) -/
def IsNonExpansive {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) : Prop :=
  specRad P < 1 ∨ (specRad P = 1 ∧ ∀ V : Finset n, IsClass P V → IsBasic P V → IsFinal P V)

/-- The surplus nodes `𝒱₊^x` of (19): inflow strictly above `w_i`. -/
noncomputable def surplus {n : Type*} [Fintype n] (P : Matrix n n ℝ) (w c x : n → ℝ) : Finset n :=
  Finset.univ.filter (fun i => w i < inflow P c x i)

/-- The exposed nodes `𝒱₀^x` of (19): inflow in `[0, w_i]`. -/
noncomputable def exposed {n : Type*} [Fintype n] (P : Matrix n n ℝ) (w c x : n → ℝ) : Finset n :=
  Finset.univ.filter (fun i => 0 ≤ inflow P c x i ∧ inflow P c x i ≤ w i)

/-- The deficit nodes `𝒱₋^x` of (19): inflow strictly below `0`. -/
noncomputable def deficit {n : Type*} [Fintype n] (P : Matrix n n ℝ) (c x : n → ℝ) : Finset n :=
  Finset.univ.filter (fun i => inflow P c x i < 0)

/-- The nodes outside `V` from which `V` can be reached in `𝒢_P`. -/
def upstream {n : Type*} (P : Matrix n n ℝ) (V : Finset n) : Set n :=
  {k | k ∉ V ∧ ∃ j ∈ V, Reaches P k j}

/-- The projections on `V` of those network equilibria that agree with `x` on every node upstream
of `V` (the paper's "given `(x^{(1)}, …, x^{(l-1)})`"). -/
def classProj {n : Type*} [Fintype n] (P : Matrix n n ℝ) (w c : n → ℝ) (V : Finset n)
    (x : n → ℝ) : Set (V → ℝ) :=
  {z | ∃ x' ∈ equilibria P w c, (∀ k ∈ upstream P V, x' k = x k) ∧ ∀ i : V, x' i = z i}

/-- The exogenous flow into the class `V` given `x` outside it:
`c^{(l)} + Σ_{i<l} P^{(il)ᵀ} x^{(i)}`, i.e. `c_j + Σ_{k ∉ V} P_{kj} x_k` for `j ∈ V`. -/
noncomputable def classInflow {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (c : n → ℝ) (V : Finset n) (x : n → ℝ) : V → ℝ :=
  fun j => c j + ∑ k ∈ Finset.univ.filter (fun k => k ∉ V), P k j * x k

/-- `min_i { a_i / b_i }` over a finite nonempty index type. -/
noncomputable def minRatio {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (h : (Finset.univ : Finset ι).Nonempty) : ℝ :=
  Finset.univ.inf' h (fun i => a i / b i)

/-- A class is nonempty. -/
theorem IsClass.univ_nonempty {n : Type*} {P : Matrix n n ℝ} {V : Finset n} (h : IsClass P V) :
    (Finset.univ : Finset V).Nonempty := by
  obtain ⟨i, hi, _⟩ := h
  exact ⟨⟨i, hi⟩, Finset.mem_univ _⟩

end SaturatedNet.Uniqueness


