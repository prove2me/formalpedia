-- Prove2me | Definitions.Def_FairFlows_Covering
-- name    : FairFlows_Covering
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:57.838695+00:00
-- url     : https://prove2.me/theorems/339c53ce-603c-4c1a-b2be-e65e95780709
-- title:
--   Covering a set function $p:2^V\to\mathbb Z\cup\{-\infty\}$, supermodularity, laminar families and the value (3.4)
-- statement:
--   Let $D=(V,A)$ be a digraph and $p:2^V\to\mathbb Z\cup\{-\infty\}$ a set function.
--
--   1. $\varrho_X(Z)$ is the number of edges of $X\subseteq A$ entering $Z$; $X$ **covers** $p$ if $\varrho_X(Z)\ge p(Z)$ for every $Z\subseteq V$. A digraph $D_L=(V,L)$ is an edge set $L$, and $X$ is a **minimum cardinality subset of $L$ covering $p$** if $X\subseteq L$ covers $p$ and no subset of $L$ covering $p$ is smaller.
--   2. $p$ is **(fully) supermodular** if $p(X)+p(Y)\le p(X\cap Y)+p(X\cup Y)$ for all $X,Y$ (3.1), and **intersecting supermodular** if this holds whenever $X\cap Y\neq\emptyset$.
--   3. A family of subsets is **laminar** if every two members $X,Y$ satisfy $X\subseteq Y$, $Y\subseteq X$ or $X\cap Y=\emptyset$.
--   4. For a family $\mathcal L$, $\varrho_L(\mathcal L)$ is the number of edges of $L$ entering at least one member, and the value of $\mathcal L$ in (3.4) is $\varrho_L(\mathcal L)-\sum_{Z\in\mathcal L}\bigl(\varrho_L(Z)-p(Z)\bigr)$. The number of members of a family entered by an edge is also defined.
--
--   These objects carry §3, the supermodular covering framework into which §4 translates the flow problem.
--
--   **Formalization Note** $\mathbb Z\cup\{-\infty\}$ is `WithBot ℤ`, whose addition has $-\infty+a=-\infty$; no $+\infty$ occurs, so (3.1) has its usual meaning. The value (3.4) reads $p(Z)$ through `unbotD 0` and is only used for families whose members have $p(Z)>-\infty$.
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, §3 p.7 (laminar, covers, (3.1) supermodular, intersecting supermodular), p.8 (ϱ_L(𝓛), (3.4))

import Mathlib
import Definitions.Def_FairFlows_Network

set_option autoImplicit false

namespace FairFlows

open Finset

variable {V A : Type}

/-- `ϱ_X(Z)`: the number of edges of `X` entering `Z` (Frank, Murota, *Fair integral network
flows*, arXiv:1907.02673v5, §3, p.7; the in-degree function of the digraph `(V, X)`). -/
def inDeg [DecidableEq V] (D : Digraph V A) (X : Finset A) (Z : Finset V) : ℕ :=
  (X.filter (fun e => D.Enters e Z)).card

/-- The edge set `X` covers the set function `p : 2^V → ℤ ∪ {−∞}`: `ϱ_X(Z) ≥ p(Z)` for every
`Z ⊆ V` (arXiv:1907.02673v5, p.7).

**Formalization Note** `ℤ ∪ {−∞}` is `WithBot ℤ`; a set with `p(Z) = −∞` imposes nothing.
A digraph `D_L = (V, L)` is an edge subset `L` of the ambient digraph `D` (the whole of `D`
when `L = univ`); "`D_L` covers `p`" is `Covers D L p`. -/
def Covers [DecidableEq V] (D : Digraph V A) (X : Finset A) (p : Finset V → WithBot ℤ) : Prop :=
  ∀ Z : Finset V, p Z ≤ ((inDeg D X Z : ℤ) : WithBot ℤ)

/-- `p` is fully supermodular: `p(X) + p(Y) ≤ p(X ∩ Y) + p(X ∪ Y)` for all `X, Y ⊆ V`
(arXiv:1907.02673v5, (3.1), p.7).

**Formalization Note** The sums are in `WithBot ℤ`, where `−∞ + a = −∞`; no `+∞` occurs, so
the inequality has its usual meaning for `ℤ ∪ {−∞}`-valued functions. -/
def IsSupermodular [DecidableEq V] (p : Finset V → WithBot ℤ) : Prop :=
  ∀ X Y : Finset V, p X + p Y ≤ p (X ∩ Y) + p (X ∪ Y)

/-- `p` is intersecting supermodular: (3.1) holds for every intersecting pair, `X ∩ Y ≠ ∅`
(arXiv:1907.02673v5, p.7). -/
def IsIntersectingSupermodular [DecidableEq V] (p : Finset V → WithBot ℤ) : Prop :=
  ∀ X Y : Finset V, (X ∩ Y).Nonempty → p X + p Y ≤ p (X ∩ Y) + p (X ∪ Y)

/-- A family of subsets is laminar: for every pair of members one of `X ⊆ Y`, `Y ⊆ X`,
`X ∩ Y = ∅` holds (arXiv:1907.02673v5, p.7). -/
def IsLaminar (𝓛 : Set (Finset V)) : Prop :=
  ∀ X ∈ 𝓛, ∀ Y ∈ 𝓛, X ⊆ Y ∨ Y ⊆ X ∨ Disjoint X Y

/-- `X` is a minimum cardinality subset of `L` covering `p` (a smallest subset of `L`
covering `p`) (arXiv:1907.02673v5, pp.7–10). -/
def IsMinCover [DecidableEq V] (D : Digraph V A) (L X : Finset A) (p : Finset V → WithBot ℤ) :
    Prop :=
  X ⊆ L ∧ Covers D X p ∧ ∀ X' : Finset A, X' ⊆ L → Covers D X' p → X.card ≤ X'.card

/-- `ϱ_L(𝓛)`: the number of edges of `L` entering at least one member of the family `𝓛`
(arXiv:1907.02673v5, p.8). -/
def famInDeg [DecidableEq V] (D : Digraph V A) (L : Finset A) (𝓛 : Finset (Finset V)) : ℕ :=
  (L.filter (fun e => ∃ Z ∈ 𝓛, D.Enters e Z)).card

/-- The number of members of the family `𝓒` entered by the edge `e`. -/
def enterCount [DecidableEq V] (D : Digraph V A) (𝓒 : Finset (Finset V)) (e : A) : ℕ :=
  (𝓒.filter (fun Z => D.Enters e Z)).card

/-- The value `ϱ_L(𝓛) − Σ[ϱ_L(Z) − p(Z) : Z ∈ 𝓛]` of a family `𝓛` in the min-max formula
(3.4) (arXiv:1907.02673v5, p.8).

**Formalization Note** It is used only for families whose members all have `p(Z) > −∞`; there
`(p Z).unbotD 0` is the integer `p(Z)`. -/
def lamValue [DecidableEq V] (D : Digraph V A) (L : Finset A) (p : Finset V → WithBot ℤ)
    (𝓛 : Finset (Finset V)) : ℤ :=
  (famInDeg D L 𝓛 : ℤ) - ∑ Z ∈ 𝓛, ((inDeg D L Z : ℤ) - (p Z).unbotD 0)

end FairFlows


