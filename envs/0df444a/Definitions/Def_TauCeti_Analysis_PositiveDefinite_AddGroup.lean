-- Prove2me | Definitions.Def_TauCeti_Analysis_PositiveDefinite_AddGroup
-- name    : TauCeti_Analysis_PositiveDefinite_AddGroup
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:26:53.088147+00:00
-- url     : https://prove2.me/theorems/8a8c78c7-f0a2-4c0a-b598-341fb5569fe7
-- title:
--   Positive-definite functions on an additive commutative group
-- statement:
--   For an additive commutative group $G$, equip a copy of $G$ with the involution
--
--   $$
--   g^*=-g.
--   $$
--
--   This expresses additive positive-definiteness using the language of involutive algebra.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/PositiveDefinite/AddGroup.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/PositiveDefinite/AddGroup.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.UniformApproximation

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Positive-definite functions on an additive commutative group

On an additive commutative group `G` the classical positive-definiteness condition for
`F : G → ℂ` reads `∑_{i,j} cᵢ · conj(cⱼ) · F(aᵢ - aⱼ) ≥ 0`: the involution is negation, so the
kernel is the translation-invariant `K(a, b) = F(a - b)`. Mathlib's `star` on a real vector space
is the identity, not negation, so the generic involutive predicate
`TauCeti.IsPositiveDefinite` does *not* express this condition for the canonical instances on
`ℝ` or on a Euclidean space. This file supplies the subtraction-form predicate
`TauCeti.IsPositiveDefiniteSub` that does, and connects it to the generic theory.

The connection runs through the type synonym `TauCeti.WithNegStar G`, a copy of `G` carrying the
negation involution `star a = -a` as a genuine `StarAddMonoid` instance. Installing that
involution on `G` itself would clash with Mathlib's star conventions, so it is installed on the
synonym instead, and `TauCeti.isPositiveDefiniteSub_iff_isPositiveDefinite` transports statements
across. The synonym is public: a generic lemma with no transfer lemma here can still be applied to
`fun a : WithNegStar G => F (WithNegStar.ofNegStar a)`.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Objects, which asks for
`IsPositiveDefinite` to be defined generically and then *instantiated* on a finite-dimensional real
inner-product space with the involution `a⋆ = -a`, and the `API to develop` items (closure
properties, the value bounds at the origin, continuity at `0` implying uniform continuity, the
PD-function ↔ PD-kernel equivalence `F(a - b)`, and normalization) at that instantiation. It is
the predicate in which Bochner's theorem is stated, in
`TauCeti/Analysis/Bochner/BochnerTheorem.lean`.

## Main declarations

* `TauCeti.WithNegStar`: the type synonym carrying the negation involution.
* `TauCeti.IsPositiveDefiniteSub`: the subtraction-form positive-definiteness predicate.
* `TauCeti.isPositiveDefiniteSub_iff_forall_sum_nonneg`: the defining finite-family condition.
* `TauCeti.isPositiveDefiniteSub_iff_isPositiveDefinite`: the transfer to the generic predicate.
* `TauCeti.isPositiveDefiniteSub_iff_posSemidef`: the PD-function ↔ PD-kernel equivalence.
* `TauCeti.isPositiveDefinite_iff_isPositiveDefiniteSub`: agreement with the generic predicate on
  a group whose own involution is negation.
* `TauCeti.IsPositiveDefiniteSub.map_zero_nonneg`, `map_zero_re_nonneg`, `map_zero_eq_ofReal_re`,
  `map_neg`, `conj_symm`, `normSq_le`, `norm_apply_le_map_zero_re`: values at and around the
  origin.
* `TauCeti.IsPositiveDefiniteSub.add`, `const_mul`, `real_smul`, `mul`, `sum`, `prod`,
  `TauCeti.isPositiveDefiniteSub_const`: closure properties.
* `TauCeti.IsPositiveDefiniteSub.comp_addMonoidHom`, `comp_smul`, `comp_neg`: pullbacks.
* `TauCeti.IsPositiveDefiniteSub.of_tendsto`: pointwise limits.
* `TauCeti.IsPositiveDefiniteSub.normalize`: normalization to value `1` at the origin.
* `TauCeti.IsPositiveDefiniteSub.uniformContinuous_of_continuousAt_zero`: continuity at `0`
  implies uniform continuity.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
* W. Rudin, *Fourier Analysis on Groups* (1962), §1.4.
-/

 section

open ComplexConjugate Filter
open scoped ComplexOrder Topology

namespace TauCeti

/-! ### The negation involution -/

/-- `WithNegStar G` is a type synonym for an additive commutative group `G`, carrying the negation
involution `star a = -a`.

Mathlib pins no negation `StarAddMonoid` instance on an additive group — on a real vector space
`star` is the identity — so the involution used by classical positive definiteness is installed on
this synonym rather than on `G` itself. -/
@[expose] def WithNegStar (G : Type*) : Type _ := G

namespace WithNegStar

section AddCommGroup

variable {G : Type*} [AddCommGroup G]

instance : AddCommGroup (WithNegStar G) := inferInstanceAs (AddCommGroup G)

instance : Star (WithNegStar G) := ⟨fun a => -a⟩



instance : StarAddMonoid (WithNegStar G) where
  star_involutive a := neg_neg a
  star_add a b := neg_add a b









end AddCommGroup

section Seminormed

variable {G : Type*} [SeminormedAddCommGroup G]

instance : SeminormedAddCommGroup (WithNegStar G) :=
  inferInstanceAs (SeminormedAddCommGroup G)

end Seminormed

end WithNegStar

/-! ### The subtraction-form predicate -/

variable {G : Type*} [AddCommGroup G] {F H : G → ℂ}







namespace IsPositiveDefiniteSub









end IsPositiveDefiniteSub





/-! ### Values at and around the origin -/

namespace IsPositiveDefiniteSub



















-- Not a `simp` lemma: the conclusion `F a = 0` has a variable head symbol, which Lean rejects.


/-! ### Closure properties -/













/-! ### Pullbacks -/







/-! ### Limits -/



/-! ### Normalization -/







end IsPositiveDefiniteSub

/-! ### Continuity -/

namespace IsPositiveDefiniteSub

variable {G : Type*} [SeminormedAddCommGroup G] {F : G → ℂ}





end IsPositiveDefiniteSub





end TauCeti

end
end


