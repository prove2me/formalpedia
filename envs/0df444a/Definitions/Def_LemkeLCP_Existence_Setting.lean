-- Prove2me | Definitions.Def_LemkeLCP_Existence_Setting
-- name    : LemkeLCP_Existence_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:46:31.359921+00:00
-- url     : https://prove2.me/theorems/22e41fd0-892d-480b-8b0d-fce4d78f7c50
-- title:
--   §B, pp. 2–6 — Z of (1), equilibrium points, N(z), non-degeneracy, edges, rays, adjacency paths, Zᵢ, Z*, Z₀*, E₀*, Z** and conditions (i)–(ii)
-- statement:
--   This file fixes the vocabulary of Lemke's existence proofs (§B of the paper). Throughout, $M$ is a real square matrix of order $n$, with rows and columns indexed by a finite set $\iota$ of size $n$, and $q\in\mathbb R^n$. Vector inequalities are componentwise, $e$ is the all-ones vector, and $(M^{\mathsf T})_i$ is the $i$-th column of $M^{\mathsf T}$.
--
--   1. **The set $Z$** ((1), p. 2). Given $z$, the vector $w = Mz-q$ is always determined by $z$, and
--   $$Z=\{z\in\mathbb R^n : z\ge 0,\ w = Mz-q\ge 0\}.$$
--   2. **Equilibrium points** (Def. 1, p. 2). A point $z\in Z$ with $z^{\mathsf T}w=0$ is an equilibrium point; $S$ is the set of all of them.
--   3. **The matrix $N(z)$** (p. 2). For $z\in\mathbb R^n$, $N(z)$ is obtained from $(M^{\mathsf T}, I)$ by deleting $(M^{\mathsf T})_i$ exactly when $w_i\ne 0$ and $(I)_i$ exactly when $z_i\ne 0$. Its zero pattern is the pair of index sets $\{i: w_i=0\}$, $\{i : z_i=0\}$; two points have the same $N(z)$ exactly when their zero patterns agree.
--   4. **Extreme points and open-edge points** (Def. 2, p. 2). $z$ is an extreme point of $Z$ if $z\in Z$ and $\operatorname{rank}N(z)=n$; $z$ lies on an open edge if $z\in Z$ and $\operatorname{rank}N(z)=n-1$.
--   5. **Non-degeneracy** (Def. 3, p. 2). $Z$ is non-degenerate if for every $z\in\mathbb R^n$ the columns of $N(z)$ are linearly independent, i.e. the number of columns of $N(z)$ equals its rank.
--   6. **Edges and rays** (p. 3). An open edge is a set of the form $\{z\in Z : N(z)=N(z_0)\}$ where $z_0$ lies on an open edge; a closed edge is the closure of an open edge. The end-points of an open edge $E$ are the points of $\overline E\setminus E$, and a ray of $Z$ is an open edge with exactly one end-point.
--   7. **The sets $Z_s$** (Def. 5, (4), p. 3). For an index $s$, $Z_s=\{z\in Z : z^{\mathsf T}w = z_s w_s\}$.
--   8. **Adjacency paths** (Def. 4, p. 3). An adjacency path is a non-empty class of closed edges of $Z$ whose union is connected and no three distinct edges of which have a common point. An end-point of the path is an extreme point of $Z$ that lies on exactly one edge of the class.
--   9. **Conditions (i)–(ii) of Theorem 4** (p. 7). For every $u\ge 0$: (i) $u^{\mathsf T}Mu\ge0$, and (ii) $u^{\mathsf T}Mu=0$ implies $Mu+M^{\mathsf T}u=0$. (Such matrices were later called *copositive-plus*.)
--   10. **The device of (9)–(10)** (p. 5). With an extra scalar variable $z_0$,
--   $$Z^*=\{(z,z_0) : z\ge0,\ z_0\ge0,\ w = Mz+z_0e-q\ge 0\},\qquad Z_0^*=\{(z,z_0)\in Z^* : z^{\mathsf T}w=0\}.$$
--   11. **The bordered system (13)** (p. 6). For a number $k$, the bordered data
--   $$M^{**}=\begin{pmatrix} M & e\\ -e^{\mathsf T} & 0\end{pmatrix},\qquad q^{**}=\begin{pmatrix} q\\ -k\end{pmatrix}$$
--   give $Z^{**}=Z(M^{**},q^{**})$, a set of the form (1) in $n+1$ variables $z^*=(z,z_0)$ whose last slack is $w_0=k-e^{\mathsf T}z$; and $Z_0^{**}$, the set of points of $Z^{**}$ with $z^{*\mathsf T}w^*=z_0w_0$ (14), is the set $Z_s$ of this bordered system for the index $s$ of $z_0$.
--   12. **The ray $E_0^*$** ((11), p. 6). $E_0^*=\{(z,z_0) : z=0,\ z_0>\max_i q_i,\ z_0>0\}$, with $w=z_0e-q$; the clause $z_0>0$ is the constraint $z_0\ge0$ of (9), omitted in (11), made strict so that the end-point is not on the open edge.
--
--   These objects are shared by every statement of the mission: Theorems 1–5, the Corollary, the two lemmas labelled "Lemma 2" and Lemma 3.
--
--   **Formalization Note** The index set is a general finite type $\iota$ ($n=|\iota|$), so that the bordered system lives on $\iota\oplus\{\ast\}$ without reindexing; $\iota=\mathrm{Fin}\,n$ is a special case. $w$ is never a separate variable: it is always $Mz-q$ (resp. $M^{**}z^*-q^{**}$). $N(z)$ is represented by the indexed family of its columns, and $\operatorname{rank}N(z)$ by the dimension of their span; "rank $N(z)=n-1$" is written $\operatorname{rank}N(z)+1=n$ to avoid natural-number subtraction. In Def. 3 the phrase "(but not all)" is read as excluding only the empty matrix (which satisfies the condition trivially); the alternative reading would also exempt $N(z)=(M^{\mathsf T},I)$, which occurs only when $z=0$ and $q=0$, so the definition used here is the stronger of the two hypotheses. Closures are taken in the usual topology of $\mathbb R^n$.
-- source:
--   Lemke, Bimatrix equilibrium points and mathematical programming, hal-01885823v1, pp. 2–7, (1), Defs. 1–5, (9)–(14), Theorem 4 (i)–(ii)

import Mathlib
open Matrix

namespace LemkeLCP.Existence

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The set `Z` of (1), Lemke 1965, p. 2: `Z = {z : Mz − w = q, z ≥ 0, w ≥ 0}`, where
`w = Mz − q` always defines `w` (p. 2). -/
def Z (M : Matrix ι ι ℝ) (q : ι → ℝ) : Set (ι → ℝ) :=
  {z | 0 ≤ z ∧ 0 ≤ M *ᵥ z - q}

/-- Def. 1, p. 2: an equilibrium point is a point of `Z` with `zᵀw = 0`, `w = Mz − q`. -/
def IsEquilibriumPoint (M : Matrix ι ι ℝ) (q : ι → ℝ) (z : ι → ℝ) : Prop :=
  z ∈ Z M q ∧ z ⬝ᵥ (M *ᵥ z - q) = 0

/-- The set `S` of all equilibrium points of `Z` (p. 3, after Def. 5). -/
def S (M : Matrix ι ι ℝ) (q : ι → ℝ) : Set (ι → ℝ) :=
  {z | IsEquilibriumPoint M q z}

/-- The columns of `N(z)` (p. 2): from `(Mᵀ, I)` delete `(Mᵀ)ᵢ` iff `(w)ᵢ ≠ 0` and `(I)ᵢ` iff
`(z)ᵢ ≠ 0`. The kept column `(Mᵀ)ᵢ` is indexed by `Sum.inl i`, the kept `(I)ᵢ` by `Sum.inr i`. -/
def Ncols (M : Matrix ι ι ℝ) (q : ι → ℝ) (z : ι → ℝ) :
    {i // (M *ᵥ z - q) i = 0} ⊕ {i // z i = 0} → (ι → ℝ)
  | Sum.inl i => fun j => M i.1 j
  | Sum.inr i => Pi.single i.1 1

/-- `rank N(z)`: the dimension of the span of the columns of `N(z)`. -/
noncomputable def rankN (M : Matrix ι ι ℝ) (q : ι → ℝ) (z : ι → ℝ) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (Set.range (Ncols M q z)))

/-- Def. 2, p. 2: `z` is an extreme point of `Z` iff `z ∈ Z` and `rank N(z) = n`. -/
def IsExtremePoint (M : Matrix ι ι ℝ) (q : ι → ℝ) (z : ι → ℝ) : Prop :=
  z ∈ Z M q ∧ rankN M q z = Fintype.card ι

/-- Def. 2, p. 2: `z` lies on an open edge of `Z` iff `z ∈ Z` and `rank N(z) = n − 1`
(written `rank N(z) + 1 = n`, so that no truncated subtraction occurs). -/
def OnOpenEdge (M : Matrix ι ι ℝ) (q : ι → ℝ) (z : ι → ℝ) : Prop :=
  z ∈ Z M q ∧ rankN M q z + 1 = Fintype.card ι

/-- Def. 3, p. 2: `Z` is non-degenerate iff for every `z ∈ Rₙ` the columns of `N(z)` are
linearly independent (number of columns = rank). -/
def NonDegenerate (M : Matrix ι ι ℝ) (q : ι → ℝ) : Prop :=
  ∀ z : ι → ℝ, LinearIndependent ℝ (Ncols M q z)

/-- Which columns `N(z)` keeps: the indices with `(w)ᵢ = 0` and those with `(z)ᵢ = 0`.
`N(z) = N(z')` iff the zero patterns of `z` and `z'` agree. -/
def zeroPattern (M : Matrix ι ι ℝ) (q : ι → ℝ) (z : ι → ℝ) : Set ι × Set ι :=
  ({i | (M *ᵥ z - q) i = 0}, {i | z i = 0})

/-- An open edge of `Z` (p. 3): the set of points `z ∈ Z` with a given `N(z)`, where that
`N(z)` is the one of a point lying on an open edge. -/
def IsOpenEdge (M : Matrix ι ι ℝ) (q : ι → ℝ) (E : Set (ι → ℝ)) : Prop :=
  ∃ z₀, OnOpenEdge M q z₀ ∧ E = {z | z ∈ Z M q ∧ zeroPattern M q z = zeroPattern M q z₀}

/-- A closed edge of `Z`: the closure of an open edge (p. 3). -/
def IsClosedEdge (M : Matrix ι ι ℝ) (q : ι → ℝ) (C : Set (ι → ℝ)) : Prop :=
  ∃ E, IsOpenEdge M q E ∧ C = closure E

/-- A ray of `Z` (p. 3): an edge having just one end-point; the end-points of an open edge `E`
are the points of `closure E` not in `E`. -/
def IsRay (M : Matrix ι ι ℝ) (q : ι → ℝ) (E : Set (ι → ℝ)) : Prop :=
  IsOpenEdge M q E ∧ ∃ p, closure E \ E = {p}

/-- Def. 5, (4), p. 3: `Zₛ = {z ∈ Z : zᵀw = (z)ₛ(w)ₛ}`. -/
def Zs (M : Matrix ι ι ℝ) (q : ι → ℝ) (s : ι) : Set (ι → ℝ) :=
  {z | z ∈ Z M q ∧ z ⬝ᵥ (M *ᵥ z - q) = z s * (M *ᵥ z - q) s}

/-- Def. 4, p. 3: an adjacency path is a non-empty class `𝒞` of closed edges of `Z` whose union
is connected and such that no three distinct edges of the class intersect. The path as a set
is `⋃₀ 𝒞`. -/
def IsAdjacencyPath (M : Matrix ι ι ℝ) (q : ι → ℝ) (𝒞 : Set (Set (ι → ℝ))) : Prop :=
  𝒞.Nonempty ∧ (∀ C ∈ 𝒞, IsClosedEdge M q C) ∧ IsConnected (⋃₀ 𝒞) ∧
    ∀ C₁ ∈ 𝒞, ∀ C₂ ∈ 𝒞, ∀ C₃ ∈ 𝒞, C₁ ≠ C₂ → C₁ ≠ C₃ → C₂ ≠ C₃ → C₁ ∩ C₂ ∩ C₃ = ∅

/-- p. 3: an end-point of an adjacency path is an extreme point of `Z` meeting exactly one
edge of the path. -/
def IsPathEndPoint (M : Matrix ι ι ℝ) (q : ι → ℝ) (𝒞 : Set (Set (ι → ℝ))) (z : ι → ℝ) :
    Prop :=
  IsExtremePoint M q z ∧ ∃! C, C ∈ 𝒞 ∧ z ∈ C

/-- Conditions (i)–(ii) of Theorem 4, p. 7: for every `u ≥ 0`, (i) `uᵀMu ≥ 0`, and
(ii) `uᵀMu = 0` implies (21) `Mu + Mᵀu = 0` (later called *copositive-plus*). -/
def CopositivePlus (M : Matrix ι ι ℝ) : Prop :=
  ∀ u : ι → ℝ, 0 ≤ u → 0 ≤ u ⬝ᵥ (M *ᵥ u) ∧ (u ⬝ᵥ (M *ᵥ u) = 0 → M *ᵥ u + Mᵀ *ᵥ u = 0)

/-- (9), p. 5: `Z* = {(z, z₀) : Mz + z₀e − w = q, w ≥ 0, z ≥ 0, z₀ ≥ 0}`. -/
def Zstar (M : Matrix ι ι ℝ) (q : ι → ℝ) : Set ((ι → ℝ) × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ 0 ≤ M *ᵥ p.1 + (fun _ => p.2) - q}

/-- (10), p. 5: `Z₀* = {z* ∈ Z* : zᵀw = 0}`. -/
def Z0star (M : Matrix ι ι ℝ) (q : ι → ℝ) : Set ((ι → ℝ) × ℝ) :=
  {p | p ∈ Zstar M q ∧ p.1 ⬝ᵥ (M *ᵥ p.1 + (fun _ => p.2) - q) = 0}

/-- The bordered matrix of (13), p. 6: `(M e; −eᵀ 0)`, indexed by `ι ⊕ Unit`
(the extra coordinate `Sum.inr ()` is `z₀`). -/
def Mss (M : Matrix ι ι ℝ) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
  Matrix.fromBlocks M (Matrix.of fun _ _ => 1) (Matrix.of fun _ _ => -1) 0

/-- The bordered right-hand side of (13), p. 6: `(q; −k)`. With it,
`Z** = Z (Mss M) (qss q k)` and `Z₀** = Zs (Mss M) (qss q k) (Sum.inr ())` (14). -/
def qss (q : ι → ℝ) (k : ℝ) : ι ⊕ Unit → ℝ :=
  Sum.elim q (fun _ => -k)

/-- The ray `E₀*` of (11), p. 6, as a set of points `z* = (z, z₀)` of the bordered system (13)
(`Sum.inr ()` is `z₀`): `z = 0` and `z₀ > Maxᵢ (q)ᵢ`, with `w = z₀e − q` the defined `w`.
The clause `z₀ > 0`, which (11) omits, is the constraint `z₀ ≥ 0` of (9) made strict so that the
end-point is not on the open edge. -/
def E0ss (q : ι → ℝ) : Set (ι ⊕ Unit → ℝ) :=
  {p | (∀ i : ι, p (Sum.inl i) = 0) ∧ 0 < p (Sum.inr ()) ∧ ∀ i : ι, q i < p (Sum.inr ())}

end LemkeLCP.Existence


