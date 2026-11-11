-- Prove2me | Definitions.Def_RandProdExp_TwoSided_Grid
-- name    : RandProdExp_TwoSided_Grid
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:17:48.987759+00:00
-- url     : https://prove2.me/theorems/012d40ec-daf0-4871-9148-4579fae070d2
-- title:
--   Axis-parallel lines and planes of $[n]^D$, $\varepsilon$-closed and $\varepsilon$-sparse sets, maximal planes, $\mathcal P_\cap(M)$ and anchor sets (Definitions 3.1–3.12)
-- statement:
--   Write $[n]=\{1,\dots,n\}$ and, for a finite coordinate set $S$, $[n]^S$ for the grid of functions $S\to[n]$. The **axis-parallel line** of $[n]^S$ in direction $j\in S$ through a point $x$ is the set of points agreeing with $x$ outside coordinate $j$; $L(M)$ is the set of axis-parallel lines contained in $M$.
--
--   A set $M\subseteq[n]^S$ is **$\varepsilon$-closed** (Definition 3.4) if every axis-parallel line $\ell$ satisfies
--   $$\ell\subseteq M\quad\text{or}\quad |M\cap\ell|\le\varepsilon n,$$
--   and it is **$\varepsilon$-sparse** (Definition 3.5) if it is $\varepsilon$-closed and contains no axis-parallel line. The paper uses these notions for $S=[D]$ and for anchor sets in $[n]^{I^c}$.
--
--   For free coordinates $I\subseteq[D]$ and an anchor $a\in[n]^{I^c}$, the **axis-parallel plane** is $P(I,a)=\{x\in[n]^D:\ x_j=a_j\ \forall j\in I^c\}$ (Definition 3.1); points are the planes with $I=\emptyset$. For $M\subseteq[n]^D$: $\mathcal P_{\mathrm{all}}(M)$ is the set of planes contained in $M$ (Definition 3.8); $\mathcal P(M)$ is the set of **maximal planes**, those $P(I,a)\subseteq M$ with no plane $P(J,b)$ satisfying $P(I,a)\subsetneq P(J,b)\subseteq M$ (Definition 3.9); and
--   $$\mathcal P_\cap(M)=\Big\{\textstyle\bigcap_{P\in\mathcal S}P:\ \emptyset\ne\mathcal S\subseteq\mathcal P(M),\ \bigcap_{P\in\mathcal S}P\neq\emptyset\Big\}$$
--   (Definition 3.10). The **anchor sets** are $\Omega_I(M)=\{a\in[n]^{I^c}: P(I,a)\in\mathcal P(M)\}$ (Definition 3.12) and $\Omega^\cap_I(M)=\{a\in[n]^{I^c}:P(I,a)\in\mathcal P_\cap(M)\}$ (p. 23).
--
--   These are the combinatorial objects on which the whole argument runs: an $\varepsilon$-closed set is the support of a potential counterexample to product expansion, and its maximal planes index the local pieces of the corestriction map.
--
--   **Formalization Note** $[n]$ is `Fin n` and $[n]^S$ is `S → Fin n`; the line in direction $j$ through $x$ is `axisLine j x`. An anchor $a\in[n]^{I^c}$ is a function on the subtype `{j // j ∉ I}`. For the algebraic diagram a plane is also named by a partial point `PlaneIdx D n = Fin D → Option (Fin n)` (`none` = free coordinate); `planeOf` gives its plane, a bijection with the pairs $(I,a)$, and `capIdx M` lists the indices of the planes in $\mathcal P_\cap(M)$.
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), pp. 19–23, Definitions 3.1–3.5, 3.8–3.10, 3.12 and p. 23 (Ω∩_I(M))

import Mathlib

namespace RandProdExp.TwoSided

/-!
# The grid `[n]^S`, axis-parallel lines and planes, ε-closed and ε-sparse sets, maximal planes,
# their intersection closure and anchor sets

Chattopadhyay, Ringach, Spooner, *Product Expansion of Random Codes via Analytic Techniques*,
STOC 2027 submission, §3.1–§3.3, pp. 19–23 (Definitions 3.1–3.5, 3.8–3.10, 3.12 and the
definition of `Ω∩_I(M)` on p. 23).

`[n] = {1, …, n}` is `Fin n`; the grid `[n]^S` over a finite coordinate set `S` is `S → Fin n`.
The ε-closed / ε-sparse notions are stated for any finite coordinate set `S`, because the paper
applies them both to `[n]^D` (`S = Fin D`) and to anchor sets in `[n]^{I^c}`
(`S = {j // j ∉ I}`).
-/

/-- The axis-parallel line of `[n]^S` in direction `j` through the point `x`: the points that agree
with `x` in every coordinate other than `j`. Every axis-parallel line of `[n]^S` (Definition 3.2) is
`axisLine j x` for some `j` and `x`. -/
def axisLine {S : Type} {n : ℕ} (j : S) (x : S → Fin n) : Set (S → Fin n) :=
  {y | ∀ k, k ≠ j → y k = x k}

/-- `L(M)` (Definition 3.3): the axis-parallel lines contained in `M`. -/
def linesIn {S : Type} {n : ℕ} (M : Set (S → Fin n)) : Set (Set (S → Fin n)) :=
  {ℓ | ∃ (j : S) (x : S → Fin n), ℓ = axisLine j x ∧ ℓ ⊆ M}

/-- **ε-closed** (Definition 3.4): every axis-parallel line `ℓ` is either contained in `M` or meets
it in at most `ε n` points. -/
def IsEpsClosed {S : Type} {n : ℕ} (ε : ℝ) (M : Set (S → Fin n)) : Prop :=
  ∀ (j : S) (x : S → Fin n), axisLine j x ⊆ M ∨ ((M ∩ axisLine j x).ncard : ℝ) ≤ ε * n

/-- **ε-sparse** (Definition 3.5): an ε-closed set that contains no axis-parallel line. -/
def IsEpsSparse {S : Type} {n : ℕ} (ε : ℝ) (M : Set (S → Fin n)) : Prop :=
  IsEpsClosed ε M ∧ ∀ (j : S) (x : S → Fin n), ¬ axisLine j x ⊆ M

/-- **Axis-parallel plane** `P(I, a)` (Definition 3.1): for free coordinates `I ⊆ [D]` and an anchor
`a ∈ [n]^{I^c}`, the points of `[n]^D` that agree with `a` on every fixed coordinate `j ∉ I`. -/
def plane {D n : ℕ} (I : Finset (Fin D)) (a : {j // j ∉ I} → Fin n) : Set (Fin D → Fin n) :=
  {x | ∀ (j : Fin D) (h : j ∉ I), x j = a ⟨j, h⟩}

/-- `P_all(M)` (Definition 3.8): all planes `P(I, a)` contained in `M`, points (`I = ∅`) included. -/
def allPlanes {D n : ℕ} (M : Set (Fin D → Fin n)) : Set (Set (Fin D → Fin n)) :=
  {P | ∃ (I : Finset (Fin D)) (a : {j // j ∉ I} → Fin n), P = plane I a ∧ P ⊆ M}

/-- `P(M)` (Definition 3.9): the maximal planes of `M`, i.e. planes `P(I, a) ⊆ M` for which no plane
`P(J, b)` satisfies `P(I, a) ⊊ P(J, b) ⊆ M`. -/
def maxPlanes {D n : ℕ} (M : Set (Fin D → Fin n)) : Set (Set (Fin D → Fin n)) :=
  {P | ∃ (I : Finset (Fin D)) (a : {j // j ∉ I} → Fin n), P = plane I a ∧ P ⊆ M ∧
    ¬ ∃ (J : Finset (Fin D)) (b : {j // j ∉ J} → Fin n), P ⊂ plane J b ∧ plane J b ⊆ M}

/-- `P∩(M)` (Definition 3.10): the nonempty intersections `⋂_{P ∈ S} P` of nonempty subfamilies
`S ⊆ P(M)`. -/
def capPlanes {D n : ℕ} (M : Set (Fin D → Fin n)) : Set (Set (Fin D → Fin n)) :=
  {P | ∃ F : Set (Set (Fin D → Fin n)), F.Nonempty ∧ F ⊆ maxPlanes M ∧ P = ⋂₀ F ∧ P.Nonempty}

/-- The anchor set `Ω_I(M) = {a ∈ [n]^{I^c} : P(I, a) ∈ P(M)}` (Definition 3.12). -/
def anchorSet {D n : ℕ} (I : Finset (Fin D)) (M : Set (Fin D → Fin n)) :
    Set ({j // j ∉ I} → Fin n) :=
  {a | plane I a ∈ maxPlanes M}

/-- The anchor set `Ω∩_I(M) = {a ∈ [n]^{I^c} : P(I, a) ∈ P∩(M)}` (p. 23, before Corollary 3.14). -/
def capAnchorSet {D n : ℕ} (I : Finset (Fin D)) (M : Set (Fin D → Fin n)) :
    Set ({j // j ∉ I} → Fin n) :=
  {a | plane I a ∈ capPlanes M}

/-- A plane index: a partial point `p : [D] → [n] ∪ {free}`; `p j = none` marks a free coordinate
and `p j = some c` fixes coordinate `j` to `c`. It encodes the pair `(I, a)` of Definition 3.1 with
`I = {j : p j = none}` and `a j = c` for `p j = some c` (a bijection). -/
abbrev PlaneIdx (D n : ℕ) := Fin D → Option (Fin n)

/-- The plane `P(I, a)` named by a plane index `p`. -/
def planeOf {D n : ℕ} (p : PlaneIdx D n) : Set (Fin D → Fin n) :=
  {x | ∀ (j : Fin D) (c : Fin n), p j = some c → x j = c}

/-- The free coordinates `I = {j : p j = none}` of a plane index. -/
def freeCoords {D n : ℕ} (p : PlaneIdx D n) : Finset (Fin D) :=
  Finset.univ.filter (fun j => p j = none)

open Classical in
/-- The plane indices of the planes in `P∩(M)`; for `n ≥ 2` a plane determines its index, so this is
`P∩(M)` itself. -/
noncomputable def capIdx {D n : ℕ} (M : Set (Fin D → Fin n)) : Finset (PlaneIdx D n) :=
  Finset.univ.filter (fun p => planeOf p ∈ capPlanes M)

end RandProdExp.TwoSided


