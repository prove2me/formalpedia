-- Prove2me | Definitions.Def_GroupCohomology_GaloisSUnits
-- name    : GroupCohomology_GaloisSUnits
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/f824ed5d-d2d4-51a8-9d24-1c8b3052a18b
-- title:
--   S-units of Q​ as a Galois module
-- statement:
--   Fix a finite set $S$ of rational primes (a `Finset Nat.Primes`) and work inside $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` with $\Gamma$ its group of $\mathbb Q$-algebra automorphisms. Recall the project predicate [`ValuationSubring.LiesOverPrime A q`](../def/FLTPrelim_Ramification.html#L16), which says that the image of $q$ in the ambient field is a non-unit of the valuation subring $A$. The central definition, [`groupCohomology.galoisSUnits S`](../def/GroupCohomology_GaloisSUnits.html#L24), is the subgroup of $\overline{\mathbb Q}^\times$ consisting of those units $x$ such that for every valuation subring $A \subseteq \overline{\mathbb Q}$ for which no $q \in S$ is a non-unit of $A$, both $x$ and $x^{-1}$ lie in $A$; `mem_galoisSUnits_iff` records this membership criterion verbatim. Closure under multiplication and inversion is immediate from the ring axioms for $A$.
--
--   The auxiliary lemma [`ValuationSubring.liesOverPrime_comap_algEquiv_iff`](../def/GroupCohomology_GaloisSUnits.html#L10) states that for $\sigma \in \Gamma$ and $q \in \mathbb N$, the pullback $A$ along $\sigma$ lies over $q$ exactly when $A$ does; from this, `smul_mem_galoisSUnits` shows the subgroup is stable under the natural action $\sigma \cdot x = \sigma(x)$, and `instMulDistribMulActionGaloisSUnits` packages this as a `MulDistribMulAction` of $\Gamma$ on the subgroup, with `coe_smul_galoisSUnits` and `coe_coe_smul_galoisSUnits` identifying the action with application of $\sigma$ at the level of units and of field elements. The abbreviation `galoisSUnitsRep S` is the resulting object of `Rep ℤ Γ`, i.e. the group written additively with its $\Gamma$-action. Finally `galoisSUnitsToUnits S` is the $\mathbb Z$-linear map from `galoisSUnitsRep S` to `Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)` induced by the inclusion of the subgroup into $\overline{\mathbb Q}^\times$; `galoisSUnitsToUnits_apply` describes it on elements, `galoisSUnitsToUnits_injective` gives injectivity, and `galoisSUnitsToUnits_ρ` records its $\Gamma$-equivariance as a separate lemma rather than bundling it into a morphism of representations.
--
--   **Relation to Mathlib.** `ValuationSubring`, `Rep`, `Rep.ofMulDistribMulAction` and `Rep.ofAlgebraAutOnUnits` are Mathlib's; the predicate [`ValuationSubring.LiesOverPrime`](../def/FLTPrelim_Ramification.html#L16) and the subgroup of $S$-units of an algebraic closure cut out by it are the project's own.
--
--   **Where it is used.** This supplies the Galois module of $S$-units of $\overline{\mathbb Q}$, together with its equivariant inclusion into $\overline{\mathbb Q}^\times$, for the group-cohomological part of the argument, where cohomology of subgroups $\mathrm{Gal}(\overline{\mathbb Q}/K) \le \Gamma$ with values in this module computes $S$-unit cohomology of number fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_GaloisSUnits.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ValuationSubring

lemma liesOverPrime_comap_algEquiv_iff (A : ValuationSubring (AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (q : ℕ) :
    (A.comap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)).LiesOverPrime q ↔ A.LiesOverPrime q := by
  simp only [LiesOverPrime, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    map_inv₀, map_natCast]

end ValuationSubring

namespace groupCohomology

open ValuationSubring

variable (S : Finset Nat.Primes)

def galoisSUnits : Subgroup (AlgebraicClosure ℚ)ˣ where
  carrier := {x | ∀ A : ValuationSubring (AlgebraicClosure ℚ), (∀ q ∈ S, ¬ A.LiesOverPrime ((q : Nat.Primes) : ℕ)) →
    ((x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A ∧ ((x⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A}
  one_mem' A _ := by simp
  mul_mem' {x y} hx hy A hA := by
    obtain ⟨hx₁, hx₂⟩ := hx A hA
    obtain ⟨hy₁, hy₂⟩ := hy A hA
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact A.mul_mem _ _ hx₁ hy₁
    · rw [mul_inv_rev, Units.val_mul]; exact A.mul_mem _ _ hy₂ hx₂
  inv_mem' {x} hx A hA := by
    obtain ⟨hx₁, hx₂⟩ := hx A hA
    exact ⟨hx₂, by rwa [inv_inv]⟩

variable {S} in
lemma mem_galoisSUnits_iff (x : (AlgebraicClosure ℚ)ˣ) :
    x ∈ galoisSUnits S ↔ ∀ A : ValuationSubring (AlgebraicClosure ℚ), (∀ q ∈ S, ¬ A.LiesOverPrime ((q : Nat.Primes) : ℕ)) →
      ((x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A ∧ ((x⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A :=
  Iff.rfl

variable {S} in

lemma smul_mem_galoisSUnits (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {x : (AlgebraicClosure ℚ)ˣ}
    (hx : x ∈ galoisSUnits S) : σ • x ∈ galoisSUnits S := by
  intro A hA
  have hA' : ∀ q ∈ S, ¬ (A.comap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)).LiesOverPrime ((q : Nat.Primes) : ℕ) :=
    fun q hq h => hA q hq ((A.liesOverPrime_comap_algEquiv_iff σ q).1 h)
  obtain ⟨h₁, h₂⟩ := hx _ hA'
  rw [ValuationSubring.mem_comap] at h₁ h₂
  refine ⟨h₁, ?_⟩
  rw [← smul_inv']
  exact h₂

instance instMulDistribMulActionGaloisSUnits :
    MulDistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ↥(galoisSUnits S) where
  smul σ x := ⟨σ • (x : (AlgebraicClosure ℚ)ˣ), smul_mem_galoisSUnits σ x.2⟩
  one_smul x := Subtype.ext (one_smul _ (x : (AlgebraicClosure ℚ)ˣ))
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ (x : (AlgebraicClosure ℚ)ˣ))
  smul_mul σ x y := Subtype.ext (smul_mul' σ (x : (AlgebraicClosure ℚ)ˣ) (y : (AlgebraicClosure ℚ)ˣ))
  smul_one σ := Subtype.ext (smul_one σ)

@[simp] lemma coe_smul_galoisSUnits (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ↥(galoisSUnits S)) :
    ((σ • x : ↥(galoisSUnits S)) : (AlgebraicClosure ℚ)ˣ) = σ • (x : (AlgebraicClosure ℚ)ˣ) := rfl

lemma coe_coe_smul_galoisSUnits (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ↥(galoisSUnits S)) :
    (((σ • x : ↥(galoisSUnits S)) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = σ ((x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) :=
  rfl

abbrev galoisSUnitsRep : Rep ℤ (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  Rep.ofMulDistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ↥(galoisSUnits S)

def galoisSUnitsToUnits : galoisSUnitsRep S →ₗ[ℤ] Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ) :=
  (MonoidHom.toAdditive (galoisSUnits S).subtype).toIntLinearMap

@[simp] lemma galoisSUnitsToUnits_apply (x : galoisSUnitsRep S) :
    galoisSUnitsToUnits S x = Additive.ofMul ((Additive.toMul x : ↥(galoisSUnits S)) : (AlgebraicClosure ℚ)ˣ) := rfl

lemma galoisSUnitsToUnits_injective : Function.Injective (galoisSUnitsToUnits S) :=
  fun _ _ h => Additive.toMul.injective (Subtype.ext (Additive.ofMul.injective h))

lemma galoisSUnitsToUnits_ρ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : galoisSUnitsRep S) :
    galoisSUnitsToUnits S ((galoisSUnitsRep S).ρ σ x) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ σ (galoisSUnitsToUnits S x) := rfl

end groupCohomology

end


