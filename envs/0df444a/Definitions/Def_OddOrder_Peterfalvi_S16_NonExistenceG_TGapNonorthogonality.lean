-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TGapNonorthogonality
-- name    : OddOrder_Peterfalvi_S16_NonExistenceG_TGapNonorthogonality
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T17:08:11.506566+00:00
-- url     : https://prove2.me/theorems/bc4fc422-90a3-4e8c-a987-3512b7a8c488
-- title:
--   Peterfalvi §§3, 11, 15: grid rigidity and $\omega$ exhaustion
-- statement:
--   Formalizes the arbitrary-grid dichotomy, $\eta$-residual rigidity and finite $\omega$-grid exhaustion used by the $T$-gap contradiction (Peterfalvi, pp. 5-9, 50-57, 75-86).
--
--   Main declarations: `Hypothesis.alignedOmegaSourceCharacter` (The multiplicative character of the type-P subgroup `W` whose canonical sigma-image is…); `omegaMonoidHom` (The multiplicative character underlying an abstract S15 omega-grid entry); `omegaW1Restriction` (Restriction of the column-zero omega character `omega i 0` to `W₁`); `omegaW2Restriction` (Restriction of the row-zero omega character `omega 0 j` to `W₂`).
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TGapNonorthogonality.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapNonorthogonality.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TGapMemberResidual

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- The multiplicative character of the type-P subgroup `W` whose canonical
sigma-image is `alignedOmegaSigmaGrid i j`.  This exposes the source character
which was previously reconstructed only inside value-level proofs. -/
noncomputable def Hypothesis.alignedOmegaSourceCharacter [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) (j : Fin hyp.w2) :
    ↥(typePData_toTICyclicHypothesis hyp.typeP hodd).W →* ℂˣ := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) :=
    ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) :=
    ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  exact (h.sdiffTICyclicHypothesis.omegaProdChar
    (h.w1CharEquiv (finCongr hcardW1.symm i)) χ₂).comp e.toMonoidHom

end OddOrder.Peterfalvi.S12

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- The multiplicative character underlying an abstract S15 omega-grid entry.
Nonvanishing follows from multiplicativity and `omega i j 1 = 1`. -/
noncomputable def omegaMonoidHom
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (i : Fin base.q) (j : Fin base.p) : ↥base.W →* ℂˣ where
  toFun w := Units.mk0 (base.omega i j w) (by
    intro hz
    have hmul := base.omega_mul i j w w⁻¹
    rw [mul_inv_cancel, base.omega_apply_one, hz, zero_mul] at hmul
    exact zero_ne_one hmul.symm)
  map_one' := Units.ext (base.omega_apply_one i j)
  map_mul' x y := Units.ext (base.omega_mul i j x y)

/-- The underlying omega-grid character has the original class-function value. -/
theorem omegaMonoidHom_coe
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (i : Fin base.q) (j : Fin base.p) (w : ↥base.W) :
    ((omegaMonoidHom base i j w : ℂˣ) : ℂ) = base.omega i j w := rfl

/-- Two linear characters of `W = W₁ ⊔ W₂` are equal when their restrictions
to both factors are equal.  This is the factorwise extensionality used to
recover the two coordinate axes of the abstract omega-grid. -/
theorem monoidHom_eq_of_eq_on_W1_W2 [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {f g : ↥base.W →* ℂˣ}
    (hW1 : ∀ x : ↥(base.W1.subgroupOf base.W), f x = g x)
    (hW2 : ∀ y : ↥(base.W2.subgroupOf base.W), f y = g y) :
    f = g := by
  let := base.W_cyclic
  let : CommGroup ↥base.W := IsCyclic.commGroup
  have hW1le : base.W1 ≤ base.W := by
    rw [base.W_eq_join]
    exact le_sup_left
  have hW2le : base.W2 ≤ base.W := by
    rw [base.W_eq_join]
    exact le_sup_right
  ext w
  have hw : w ∈ (base.W1.subgroupOf base.W) ⊔
      (base.W2.subgroupOf base.W) := by
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, ← base.W_eq_join,
      Subgroup.subgroupOf_self]
    exact Subgroup.mem_top w
  obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup.mp hw
  rw [← hxy, map_mul, map_mul, hW1 ⟨x, hx⟩, hW2 ⟨y, hy⟩]

/-- Restriction of the column-zero omega character `omega i 0` to `W₁`. -/
noncomputable def omegaW1Restriction
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (i : Fin base.q) : ↥(base.W1.subgroupOf base.W) →* ℂˣ :=
  (omegaMonoidHom base i ⟨0, base.p_prime.pos⟩).comp
    (base.W1.subgroupOf base.W).subtype

/-- Restriction of the row-zero omega character `omega 0 j` to `W₂`. -/
noncomputable def omegaW2Restriction
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (j : Fin base.p) : ↥(base.W2.subgroupOf base.W) →* ℂˣ :=
  (omegaMonoidHom base ⟨0, base.q_prime.pos⟩ j).comp
    (base.W2.subgroupOf base.W).subtype

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (3.3), abstract omega-grid exhaustion.**
The `q*p` multiplicative characters underlying the S15 omega-grid are
pairwise distinct by orthonormality.  Since the cyclic group `W` has order
`p*q`, its complex linear-character group has the same cardinality; hence the
grid enumerates every `W →* ℂˣ` character. -/
theorem omegaMonoidHom_bijective [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Function.Bijective
      (fun ij : Fin base.q × Fin base.p => omegaMonoidHom base ij.1 ij.2) := by
  classical
  have hinj : Function.Injective
      (fun ij : Fin base.q × Fin base.p => omegaMonoidHom base ij.1 ij.2) := by
    intro ⟨i, j⟩ ⟨k, l⟩ hhom
    have hcf : base.omega i j = base.omega k l := by
      ext w
      have hw := DFunLike.congr_fun hhom w
      exact congrArg (fun z : ℂˣ => (z : ℂ)) hw
    by_contra hne
    have h1 := eta_orthonormal base i k j l
    rw [base.eta_eq_tau_omega, base.eta_eq_tau_omega,
      base.tau3_isometry.inner_eq, hcf] at h1
    have h2 := base.omega_orthonormal k k l l
    have hcond : ¬ (i = k ∧ j = l) := fun ⟨hi, hj⟩ => hne (by rw [hi, hj])
    rw [if_neg hcond] at h1
    rw [if_pos (⟨rfl, rfl⟩ : k = k ∧ l = l)] at h2
    exact zero_ne_one (h1.symm.trans h2)
  have : Fintype (↥base.W →* ℂˣ) := Fintype.ofFinite _
  have : IsCyclic ↥base.W := base.W_cyclic
  let : CommGroup ↥base.W := IsCyclic.commGroup
  have : NeZero (Monoid.exponent ↥base.W) :=
    ⟨Monoid.exponent_ne_zero_of_finite⟩
  have : NeZero ((Monoid.exponent ↥base.W : ℂ)) :=
    ⟨Nat.cast_ne_zero.2 (NeZero.ne _)⟩
  have hcardHomNat : Nat.card (↥base.W →* ℂˣ) = base.q * base.p := by
    rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ↥base.W ℂ,
      OddOrder.Peterfalvi.S15.card_W_eq_pq base, Nat.mul_comm]
  have hcardHom : Fintype.card (↥base.W →* ℂˣ) = base.q * base.p := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardHomNat
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by simp [hcardHom]⟩

/-- Distinct column-zero omega characters remain distinct on `W₁`; on the
other factor they are all trivial. -/
theorem omegaW1Restriction_injective [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Function.Injective (omegaW1Restriction base) := by
  intro i k hik
  have hhom : omegaMonoidHom base i ⟨0, base.p_prime.pos⟩ =
      omegaMonoidHom base k ⟨0, base.p_prime.pos⟩ := by
    apply monoidHom_eq_of_eq_on_W1_W2 base
    · intro x
      exact DFunLike.congr_fun hik x
    · intro y
      apply Units.ext
      rw [omegaMonoidHom_coe, omegaMonoidHom_coe,
        base.omega_col_zero_apply_of_mem_W2 i y
          (Subgroup.mem_subgroupOf.mp y.property),
        base.omega_col_zero_apply_of_mem_W2 k y
          (Subgroup.mem_subgroupOf.mp y.property)]
  have hp : ((i, ⟨0, base.p_prime.pos⟩) : Fin base.q × Fin base.p) =
      (k, ⟨0, base.p_prime.pos⟩) :=
    (omegaMonoidHom_bijective base).injective hhom
  exact congrArg Prod.fst hp

/-- Distinct row-zero omega characters remain distinct on `W₂`; on the
other factor they are all trivial. -/
theorem omegaW2Restriction_injective [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Function.Injective (omegaW2Restriction base) := by
  intro j l hjl
  have hhom : omegaMonoidHom base ⟨0, base.q_prime.pos⟩ j =
      omegaMonoidHom base ⟨0, base.q_prime.pos⟩ l := by
    apply monoidHom_eq_of_eq_on_W1_W2 base
    · intro x
      apply Units.ext
      rw [omegaMonoidHom_coe, omegaMonoidHom_coe,
        base.omega_row_zero_apply_of_mem_W1 j x
          (Subgroup.mem_subgroupOf.mp x.property),
        base.omega_row_zero_apply_of_mem_W1 l x
          (Subgroup.mem_subgroupOf.mp x.property)]
    · intro y
      exact DFunLike.congr_fun hjl y
  have hp : ((⟨0, base.q_prime.pos⟩, j) : Fin base.q × Fin base.p) =
      (⟨0, base.q_prime.pos⟩, l) :=
    (omegaMonoidHom_bijective base).injective hhom
  exact congrArg Prod.snd hp

open scoped Classical in
/-- **Peterfalvi (3.3), `W₁` axis exhaustion.**  The column-zero omega
characters restrict bijectively to all complex linear characters of `W₁`.
The injectivity is factorwise rigidity; surjectivity follows because both
sides have cardinality `q`. -/
theorem omegaW1Restriction_bijective [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Function.Bijective (omegaW1Restriction base) := by
  classical
  have hinj := omegaW1Restriction_injective base
  have hW1le : base.W1 ≤ base.W := by
    rw [base.W_eq_join]
    exact le_sup_left
  have : IsCyclic ↥base.W := base.W_cyclic
  let : CommGroup ↥base.W := IsCyclic.commGroup
  have : Fintype (↥(base.W1.subgroupOf base.W) →* ℂˣ) := Fintype.ofFinite _
  have : NeZero (Monoid.exponent ↥(base.W1.subgroupOf base.W)) :=
    ⟨Monoid.exponent_ne_zero_of_finite⟩
  have : NeZero ((Monoid.exponent ↥(base.W1.subgroupOf base.W) : ℂ)) :=
    ⟨Nat.cast_ne_zero.2 (NeZero.ne _)⟩
  have hcardHomNat :
      Nat.card (↥(base.W1.subgroupOf base.W) →* ℂˣ) = base.q := by
    rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity
      ↥(base.W1.subgroupOf base.W) ℂ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv,
      ← base.q_eq_card_W1]
  have hcardHom :
      Fintype.card (↥(base.W1.subgroupOf base.W) →* ℂˣ) = base.q := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardHomNat
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by simp [hcardHom]⟩

open scoped Classical in
/-- **Peterfalvi (3.3), `W₂` axis exhaustion.**  The row-zero omega
characters restrict bijectively to all complex linear characters of `W₂`.
The injectivity is factorwise rigidity; surjectivity follows because both
sides have cardinality `p`. -/
theorem omegaW2Restriction_bijective [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Function.Bijective (omegaW2Restriction base) := by
  classical
  have hinj := omegaW2Restriction_injective base
  have hW2le : base.W2 ≤ base.W := by
    rw [base.W_eq_join]
    exact le_sup_right
  have : IsCyclic ↥base.W := base.W_cyclic
  let : CommGroup ↥base.W := IsCyclic.commGroup
  have : Fintype (↥(base.W2.subgroupOf base.W) →* ℂˣ) := Fintype.ofFinite _
  have : NeZero (Monoid.exponent ↥(base.W2.subgroupOf base.W)) :=
    ⟨Monoid.exponent_ne_zero_of_finite⟩
  have : NeZero ((Monoid.exponent ↥(base.W2.subgroupOf base.W) : ℂ)) :=
    ⟨Nat.cast_ne_zero.2 (NeZero.ne _)⟩
  have hcardHomNat :
      Nat.card (↥(base.W2.subgroupOf base.W) →* ℂˣ) = base.p := by
    rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity
      ↥(base.W2.subgroupOf base.W) ℂ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv,
      ← base.p_eq_card_W2]
  have hcardHom :
      Fintype.card (↥(base.W2.subgroupOf base.W) →* ℂˣ) = base.p := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardHomNat
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by simp [hcardHom]⟩

/-- The zero-column indices as an explicit enumeration of `W₁`'s linear
characters. -/
noncomputable def omegaW1RestrictionEquiv [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Fin base.q ≃ (↥(base.W1.subgroupOf base.W) →* ℂˣ) :=
  Equiv.ofBijective (omegaW1Restriction base)
    (omegaW1Restriction_bijective base)

/-- The zero-row indices as an explicit enumeration of `W₂`'s linear
characters. -/
noncomputable def omegaW2RestrictionEquiv [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    Fin base.p ≃ (↥(base.W2.subgroupOf base.W) →* ℂˣ) :=
  Equiv.ofBijective (omegaW2Restriction base)
    (omegaW2Restriction_bijective base)

/-- The zero index on the `W₁` axis is the trivial linear character. -/
theorem omegaW1Restriction_zero [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
  omegaW1Restriction base ⟨0, base.q_prime.pos⟩ = 1 := by
  ext x
  change base.omega ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ x = 1
  exact base.omega_row_zero_apply_of_mem_W1 ⟨0, base.p_prime.pos⟩ x
    (Subgroup.mem_subgroupOf.mp x.property)

/-- The zero index on the `W₂` axis is the trivial linear character. -/
theorem omegaW2Restriction_zero [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
  omegaW2Restriction base ⟨0, base.p_prime.pos⟩ = 1 := by
  ext y
  change base.omega ⟨0, base.q_prime.pos⟩ ⟨0, base.p_prime.pos⟩ y = 1
  exact base.omega_col_zero_apply_of_mem_W2 ⟨0, base.q_prime.pos⟩ y
    (Subgroup.mem_subgroupOf.mp y.property)

/-- The inverse `W₁`-axis enumeration sends the trivial character back to
the distinguished zero index. -/
theorem omegaW1RestrictionEquiv_symm_one [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    (omegaW1RestrictionEquiv base).symm 1 = ⟨0, base.q_prime.pos⟩ := by
  apply (omegaW1RestrictionEquiv base).injective
  rw [Equiv.apply_symm_apply]
  change 1 = omegaW1Restriction base ⟨0, base.q_prime.pos⟩
  exact (omegaW1Restriction_zero base).symm

/-- The inverse `W₂`-axis enumeration sends the trivial character back to
the distinguished zero index. -/
theorem omegaW2RestrictionEquiv_symm_one [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) :
    (omegaW2RestrictionEquiv base).symm 1 = ⟨0, base.p_prime.pos⟩ := by
  apply (omegaW2RestrictionEquiv base).injective
  rw [Equiv.apply_symm_apply]
  change 1 = omegaW2Restriction base ⟨0, base.p_prime.pos⟩
  exact (omegaW2Restriction_zero base).symm

end OddOrder.Peterfalvi.S16


