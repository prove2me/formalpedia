-- Prove2me | Definitions.Def_GroupCohomology_IsTateCupProduct
-- name    : GroupCohomology_IsTateCupProduct
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/8a01aee9-39fd-5eb4-af00-fc75cb2ac9d4
-- title:
--   Axioms characterising the cup product on Tate cohomology
-- statement:
--   Throughout, $k$ is a commutative ring and $G$ a finite group, and $\hat H^n(G,A)$ denotes the Tate cohomology of $A \in \mathrm{Rep}_k G$ in the sense of the project's [`Rep.tateCohomology`](../def/GroupCohomology_TateCohomology.html#L140): $H^n(G,A)$ for $n \ge 1$, $A^G/\operatorname{im}\bar N$ in degree $0$, $\ker \bar N \subseteq A_G$ in degree $-1$, and $H_{-n-1}(G,A)$ for $n \le -2$, where $\bar N \colon A_G \to A^G$ is the map induced by the norm $\sum_{g\in G}\rho(g)$. The abbreviation [`Rep.TateCupFamily k G`](../def/GroupCohomology_IsTateCupProduct.html#L20) is the type of families assigning, to every pair $A,B$ of representations and every triple of integers $p,q,r$ together with a proof that $p+q=r$, a $k$-bilinear map $\hat H^p(G,A) \times \hat H^q(G,B) \to \hat H^r(G,A\otimes B)$; carrying $r$ and the equation $p+q=r$ as separate data avoids any transport along $p+q=r$.
--
--   [`Rep.IsTateCupProduct`](../def/GroupCohomology_IsTateCupProduct.html#L28) is a `Prop`-valued structure: a predicate on such a family $\cup$, with four fields. `cup_ofNat_succ` pins the product down in strictly positive bidegrees: for all $p,q \in \mathbb{N}$ and every family $\cup'$ on $H^\bullet(G,A)\times H^\bullet(G,B)$ satisfying [`groupCohomology.IsGradedCupProduct`](../def/GroupCohomology_IsGradedCupProduct.html#L17) — i.e. such that whenever cocycle representatives $x,y$ have cochain-level cup product (the explicit inhomogeneous formula of [`groupCohomology.cochainCup`](../def/GroupCohomology_CochainCup.html#L17)) annihilated by the differential, $\cup'$ sends their classes to the class of that cochain — the two products agree on $H^{p+1}(G,A)\times H^{q+1}(G,B)$, the target index being the cast of $(p+1)+(q+1)$. `map_cup` is naturality in both variables with respect to the degreewise maps `tateMap`: $(\varphi \otimes \psi)_*(x \cup y) = \varphi_* x \cup \psi_* y$. `delta_cup` and `cup_delta` record compatibility with the connecting maps `tateδ` of the long exact sequence: for a short exact $X$ with $X \otimes B$ again short exact, $\delta_{X\otimes B}(x \cup y) = (\delta_X x)\cup y$ in bidegree $(p+1,q,r+1)$; and for $A \otimes X$ short exact, $\delta_{A\otimes X}(x\cup y) = (-1)^p\, x \cup (\delta_X y)$ in bidegree $(p,q+1,r+1)$, the sign being `Int.negOnePow` of $p$ cast into $k$ and acting through the module structure. The module only states these axioms; existence of a family satisfying them is not part of it.
--
--   **Relation to Mathlib.** Mathlib supplies group cohomology and homology of `Rep k G` and the monoidal structure on it, but no Tate cohomology and no cup product on it; the Tate groups, their functoriality (`tateMap`), their connecting maps (`tateδ`), the cochain-level cup product and both cup-product predicates are the project's own, built on those Mathlib notions.
--
--   **Where it is used.** The axioms fixed here are the interface through which the downstream modules use the cup product on Tate cohomology of finite groups, in particular for dimension-shifting arguments and for the Galois-cohomological computations that enter the deformation-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_IsTateCupProduct.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace Rep

section family

variable (k G : Type u) [CommRing k] [Group G] [Fintype G]

abbrev TateCupFamily : Type (u + 1) :=
  ∀ (A B : Rep.{u} k G) (p q r : ℤ), p + q = r →
    (A.tateCohomology p →ₗ[k] B.tateCohomology q →ₗ[k] (A ⊗ B).tateCohomology r)

end family

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

structure IsTateCupProduct (cup : TateCupFamily k G) : Prop where
  cup_ofNat_succ : ∀ (A B : Rep.{u} k G) (cup' : groupCohomology.GradedCupFamily A B)
      (_hcup' : groupCohomology.IsGradedCupProduct A B cup') (p q : ℕ)
      (x : groupCohomology A (p + 1)) (y : groupCohomology B (q + 1)),
    cup A B (p + 1 : ℕ) (q + 1 : ℕ) (p + 1 + (q + 1) : ℕ) (Nat.cast_add (p + 1) (q + 1)).symm x y
      = cup' (p + 1) (q + 1) x y
  map_cup : ∀ {A A' B B' : Rep.{u} k G} (φ : A ⟶ A') (ψ : B ⟶ B') (p q r : ℤ) (h : p + q = r)
      (x : A.tateCohomology p) (y : B.tateCohomology q),
    (tateMap (φ ⊗ₘ ψ) r).hom (cup A B p q r h x y) = cup A' B' p q r h ((tateMap φ p).hom x) ((tateMap ψ q).hom y)
  delta_cup : ∀ {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (B : Rep.{u} k G)
      (hXB : (X.map (MonoidalCategory.tensorRight B)).ShortExact) (p q r : ℤ) (h : p + q = r)
      (x : X.X₃.tateCohomology p) (y : B.tateCohomology q),
    (tateδ hXB r).hom (cup X.X₃ B p q r h x y) = cup X.X₁ B (p + 1) q (r + 1) (by omega) ((tateδ hX p).hom x) y
  cup_delta : ∀ (A : Rep.{u} k G) {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
      (hAX : (X.map (MonoidalCategory.tensorLeft A)).ShortExact) (p q r : ℤ) (h : p + q = r)
      (x : A.tateCohomology p) (y : X.X₃.tateCohomology q),
    (tateδ hAX r).hom (cup A X.X₃ p q r h x y)
      = ((p.negOnePow : ℤ) : k) • cup A X.X₁ p (q + 1) (r + 1) (by omega) x ((tateδ hX q).hom y)

end Rep


