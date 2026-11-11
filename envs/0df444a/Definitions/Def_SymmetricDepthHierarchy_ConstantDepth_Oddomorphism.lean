-- Prove2me | Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Oddomorphism
-- name    : SymmetricDepthHierarchy_ConstantDepth_Oddomorphism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:41.888187+00:00
-- url     : https://prove2.me/theorems/5c4c7312-6aeb-45c8-9f09-579943b14193
-- title:
--   Oddomorphisms, weak oddomorphisms, $K_1$, minor-closed and weak-oddomorphism-closed classes
-- statement:
--   Let $F,G$ be graphs and $\varphi:F\to G$ a homomorphism. A vertex $a\in V(F)$ is **$\varphi$-even** (resp. **$\varphi$-odd**) if $|N_F(a)\cap\varphi^{-1}(x)|$ is even (resp. odd) for every $x\in N_G(\varphi(a))$. The homomorphism $\varphi$ is an **oddomorphism** if
--
--   1. every vertex $a\in V(F)$ is $\varphi$-even or $\varphi$-odd, and
--   2. for every $x\in V(G)$, the set $\varphi^{-1}(x)$ contains an odd number of $\varphi$-odd vertices.
--
--   It is a **weak oddomorphism** if there is a subgraph $F'\subseteq F$ such that $\varphi|_{F'}:F'\to G$ is an oddomorphism.
--
--   A graph class $\mathcal F$ is **minor-closed** if it contains every minor of each of its members, and **closed under weak oddomorphisms** if for every $F\in\mathcal F$ and every weak oddomorphism $F\to G$ also $G\in\mathcal F$. $K_1$ is the one-vertex graph.
--
--   These are the hypotheses of the monotonicity theorem (Theorem 3.7).
--
--   **Formalization Note.** Minors are ordinary minors given by pairwise disjoint connected branch sets with an edge between the branch sets of adjacent vertices (`HadwigerConj.IsMinor`, a published definition). The subgraph $F'$ need not be induced or spanning; a vertex whose image has no neighbour is both even and odd.
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), Definition B.15, p. 35 (PDF p. 38); Theorem 3.7, p. 11 (PDF p. 14)

import Mathlib
import Definitions.Def_HadwigerConj_Defs
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Pattern

open scoped Classical

noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth

/-!
# Oddomorphisms, weak oddomorphisms, and closure properties of graph classes

STOC 2027 submission #1521, Definition B.15 (printed p. 35, PDF p. 38, after [Rob26]) and the
closure notions used in Theorem 3.7 (printed p. 11, PDF p. 14).

Minors are ordinary graph minors given by disjoint connected branch sets
(`HadwigerConj.IsMinor`, a published platform definition).
-/

variable {V W : Type} [Fintype V] [Fintype W]

/-- `a` is `φ`-even: `|N_F(a) ∩ φ⁻¹(x)|` is even for every neighbour `x` of `φ(a)` in `G`. -/
def IsPhiEven {F : SimpleGraph V} {G : SimpleGraph W} (φ : F →g G) (a : V) : Prop :=
  ∀ x, G.Adj (φ a) x → Even (Finset.univ.filter fun b => F.Adj a b ∧ φ b = x).card

/-- `a` is `φ`-odd: `|N_F(a) ∩ φ⁻¹(x)|` is odd for every neighbour `x` of `φ(a)` in `G`. -/
def IsPhiOdd {F : SimpleGraph V} {G : SimpleGraph W} (φ : F →g G) (a : V) : Prop :=
  ∀ x, G.Adj (φ a) x → Odd (Finset.univ.filter fun b => F.Adj a b ∧ φ b = x).card

/-- Definition B.15: the homomorphism `φ : F → G` is an oddomorphism if every vertex of `F` is
`φ`-even or `φ`-odd, and every fibre `φ⁻¹(x)` contains an odd number of `φ`-odd vertices. -/
def IsOddomorphism {F : SimpleGraph V} {G : SimpleGraph W} (φ : F →g G) : Prop :=
  (∀ a, IsPhiEven φ a ∨ IsPhiOdd φ a) ∧
  ∀ x, Odd (Finset.univ.filter fun a => φ a = x ∧ IsPhiOdd φ a).card

/-- Definition B.15: `φ : F → G` is a weak oddomorphism if there is a subgraph `F' ⊆ F` (not
necessarily induced or spanning) such that the restriction `φ|_{F'} : F' → G` is an
oddomorphism. -/
def IsWeakOddomorphism {F : SimpleGraph V} {G : SimpleGraph W} (φ : F →g G) : Prop :=
  ∃ F' : F.Subgraph, IsOddomorphism (φ.comp F'.hom)

/-- The one-vertex graph `K₁`. -/
def K1 : FinGraph := ⟨Fin 1, ⊥⟩

/-- `𝓕` is minor-closed: every minor of a member is a member. -/
def MinorClosed (𝓕 : GraphClass) : Prop :=
  ∀ F ∈ 𝓕, ∀ H : FinGraph, HadwigerConj.IsMinor H.G F.G → H ∈ 𝓕

/-- `𝓕` is closed under weak oddomorphisms: for every `F ∈ 𝓕` and every weak oddomorphism
`F → G`, `G ∈ 𝓕`. -/
def WeakOddClosed (𝓕 : GraphClass) : Prop :=
  ∀ F ∈ 𝓕, ∀ G : FinGraph, ∀ φ : F.G →g G.G, IsWeakOddomorphism φ → G ∈ 𝓕

end SymmetricDepthHierarchy.ConstantDepth


