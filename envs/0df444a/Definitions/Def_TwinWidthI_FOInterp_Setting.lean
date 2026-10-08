-- Prove2me | Definitions.Def_TwinWidthI_FOInterp_Setting
-- name    : TwinWidthI_FOInterp_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:35.132002+00:00
-- url     : https://prove2.me/theorems/16689eb7-bd1a-42bb-aba4-468dac2ffc1b
-- title:
--   pp. 3:12, 3:17, 3:32, 3:40 — twin-width (partition form), r-refinement, quantifier depth and the interpretation φ(G)
-- statement:
--   Let $G$ be a finite simple graph on a vertex set $V$.
--
--   **Twin-width.** Two vertex sets $X, Y$ are *homogeneous* in $G$ if either every pair $(x,y)\in X\times Y$ is an edge or no pair is. For a partition $\mathcal P$ of $V$, the *red degree* of a part $X$ is the number of other parts $Y\neq X$ of $\mathcal P$ that are not homogeneous to $X$; $\mathcal P$ is a *$d$-partition* if every part has red degree at most $d$. A *merge step* replaces two distinct parts $X, Y$ by $X\cup Y$. The graph $G$ has *twin-width at most $d$*, written $\operatorname{tww}(G)\le d$, if there is a sequence of partitions
--   $$\mathcal P_0,\ \mathcal P_1,\ \dots,\ \mathcal P_N$$
--   of $V$ such that $\mathcal P_0$ is the partition into singletons, $\mathcal P_N$ has at most one part, each $\mathcal P_{i+1}$ is obtained from $\mathcal P_i$ by one merge step, and every $\mathcal P_i$ is a $d$-partition.
--
--   **Refinement.** A partition $\mathcal Q$ *$r$-refines* a partition $\mathcal Q'$ if every part of $\mathcal Q$ is contained in a part of $\mathcal Q'$ and every part of $\mathcal Q'$ contains at most $r$ parts of $\mathcal Q$.
--
--   **Prenex formulas and their depth.** First-order graph formulas are built from atoms $u=v$ and $E(u,v)$ with Boolean connectives and quantifiers. The *quantifier depth* of a formula counts nested quantifiers: atoms have depth $0$, a Boolean combination has the largest depth of its arguments, and $\forall x\,\psi$, $\exists x\,\psi$ have depth one more than $\psi$. A formula
--   $$\varphi(x,y)=Q_1x_1\,Q_2x_2\cdots Q_\ell x_\ell\ \varphi^*,\qquad Q_i\in\{\forall,\exists\},$$
--   with $\varphi^*$ quantifier-free in the variables $x_1,\dots,x_\ell,x,y$, is *prenex of depth $\ell$*.
--
--   **Interpretations.** For a formula $\varphi(x,y)$ with two free variables, the *interpretation* $\varphi(G)$ of $G$ by $\varphi$ is the graph on the vertex set $V$ in which two distinct vertices $u,v$ are adjacent if and only if
--   $$G\models\varphi(u,v)\wedge\varphi(v,u).$$
--
--   These are the objects of Theorem 8.3: an interpretation of a class of graphs of bounded twin-width has bounded twin-width.
--
--   **Formalization Note.** Twin-width is stated in the paper's equivalent partition form (p. 3:12: a red edge between two contracted vertices exactly when their vertex sets are not homogeneous; p. 3:32: sequences of $d$-partitions); trigraphs are not formalized. Twin-width is never a number here: $\operatorname{tww}(G)\le d$ is the predicate `TwinWidthLE G d`, so no infimum over an empty set can occur, and the final partition has *at most* one part, which covers the empty vertex set. Formulas are Mathlib's first-order formulas in the language of graphs (one binary relation symbol), evaluated in the structure `G.structure` that interprets the symbol as adjacency; free variable `0` is $x$ and free variable `1` is $y$. Mathlib has no quantifier depth, so it is defined here (`qdepth`); since Mathlib writes $\exists$ as $\neg\forall\neg$, both quantifiers add one. The condition $u\neq v$ in $\varphi(G)$ is added because $\varphi(G)$ is a simple graph (the page lists "all the pairs $uv$").
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), pp. 3:11–3:12 §3 (twin-width), p. 3:17 §5.2 (r-refines), p. 3:32 §7.2 (d-partitions, sequences of d-partitions), p. 3:40 §8 (prenex formulas of depth ℓ, interpretation φ(G))

import Mathlib
import Definitions.Def_TwinWidthI_BoolWidth_Setting

namespace TwinWidthI.FOInterp

open Finset

/-! ### Graph twin-width in partition form (pp. 3:11–3:12, p. 3:32) -/

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in

/-- p. 3:17 (§5.2): `Q` `r`-refines `Q'`: every part of `Q` lies in a part of `Q'`, and every
part of `Q'` contains at most `r` parts of `Q`. -/
def RRefines (r : ℕ) (Q Q' : Finpartition (univ : Finset V)) : Prop :=
  Q ≤ Q' ∧ ∀ Y ∈ Q'.parts, #{X ∈ Q.parts | X ⊆ Y} ≤ r

end TwinWidthI.FOInterp

namespace TwinWidthI.FOInterp

open FirstOrder FirstOrder.Language

/-! ### First-order interpretations (§8, p. 3:40) -/

/-- p. 3:40: the quantifier depth of a first-order formula: `∀` adds one, a Boolean connective
takes the maximum of its arguments, atoms have depth `0`. (`∃ = ¬∀¬` in Mathlib, so `∃` also
adds one.) On a prenex formula `Q₁x₁ … Q_ℓx_ℓ φ*` this is the length `ℓ` of the prefix. -/
def qdepth {L : Language} {α : Type*} : ∀ {n : ℕ}, L.BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ ψ => max (qdepth φ) (qdepth ψ)
  | _, .all φ => qdepth φ + 1

/-- p. 3:40: `φ` is a prenex first-order formula of depth `ℓ`. -/
def IsPrenexOfDepth {L : Language} {α : Type*} {n : ℕ} (φ : L.BoundedFormula α n) (ℓ : ℕ) :
    Prop :=
  φ.IsPrenex ∧ qdepth φ = ℓ

/-- p. 3:40: the interpretation `φ(G)` of the graph `G` by the formula `φ(x, y)` (free variable
`0` is `x`, free variable `1` is `y`): vertex set `V(G)`, and `uv` is an edge iff
`G ⊨ φ(u, v) ∧ φ(v, u)`. The condition `u ≠ v` is added because `φ(G)` is a simple graph. -/
def interp (φ : Language.graph.Formula (Fin 2)) {W : Type*} (G : SimpleGraph W) :
    SimpleGraph W where
  Adj u v := u ≠ v ∧ (letI := G.structure; φ.Realize ![u, v]) ∧
    (letI := G.structure; φ.Realize ![v, u])
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end TwinWidthI.FOInterp


