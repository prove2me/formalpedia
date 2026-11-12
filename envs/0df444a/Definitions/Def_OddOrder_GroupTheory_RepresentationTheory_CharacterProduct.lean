-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterProduct
-- name    : OddOrder_GroupTheory_RepresentationTheory_CharacterProduct
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:38:32.518829+00:00
-- url     : https://prove2.me/theorems/ca605e9e-4fbd-4ee2-885c-a23d085a251b
-- title:
--   Pointwise product of class functions; products of characters
-- statement:
--   Equips class functions on $G$ with the pointwise product, which is conjugation invariant because each factor is, and proves that the product of two genuine characters is a character (via the tensor product of representations) and that $\mathbb{Z}[\mathrm{Irr}\,G]$ is closed under products.
--
--   The bundle introduces the `instMul` instance, the pointwise product of class functions.
--
--   The bundle also proves 19 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CharacterProduct.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CharacterProduct.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_Clifford
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_LinearCharacter

set_option linter.unusedFintypeInType false

namespace OddOrder.RepresentationTheory

namespace ClassFunction

variable {G : Type*} [Group G] {k : Type*} [CommRing k]

/-- **Pointwise product** of class functions.  The product `g ↦ φ g * ψ g` is again constant on
conjugacy classes because each factor is (`ClassFunction.conj_eq`). -/
instance instMul : Mul (ClassFunction G k) where
  mul φ ψ := ⟨fun g => φ g * ψ g, fun g h => by
    simp only [φ.conj_eq, ψ.conj_eq]⟩

@[simp] theorem mul_apply (φ ψ : ClassFunction G k) (g : G) : (φ * ψ) g = φ g * ψ g := rfl

/-- Evaluation commutes with finite sums of class functions: `(∑ i ∈ s, F i) g = ∑ i ∈ s, F i g`.
(`ClassFunction` is an `AddCommGroup` with `rfl` `add_apply`/`zero_apply`, but is not a semiring, so
this and `mul_sum` below are proved by hand.) -/
theorem sum_apply {ι : Type*} (s : Finset ι) (F : ι → ClassFunction G k) (g : G) :
    (∑ i ∈ s, F i) g = ∑ i ∈ s, F i g := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

/-- Pointwise multiplication distributes over finite sums of class functions:
`φ · ∑ i ∈ s, F i = ∑ i ∈ s, φ · F i`.  (`ClassFunction` carries `Mul` but not a semiring, so
`Finset.mul_sum` does not apply; proved pointwise, reducing to `Finset.mul_sum` in `k`.) -/
theorem mul_sum {ι : Type*} (φ : ClassFunction G k) (s : Finset ι) (F : ι → ClassFunction G k) :
    φ * ∑ i ∈ s, F i = ∑ i ∈ s, φ * F i := by
  ext g
  rw [mul_apply, sum_apply, sum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => (mul_apply φ (F i) g).symm

/-- **Twisting by the trivial linear character is the identity**: `χ · lcf(1) = χ`.  The
degenerate case of the extension classification (`β = 1` forces `χ₂ = χ₁`, issue 9002
(v-c4)). -/
@[simp] theorem mul_linearClassFunction_one (χ : ClassFunction G ℂ) :
    χ * linearClassFunction (1 : G →* ℂˣ) = χ := by
  ext y
  rw [mul_apply, linearClassFunction_apply]
  simp

/-- Restriction to a subgroup is multiplicative for the pointwise product. -/
@[simp] theorem restrict_mul (H : Subgroup G) (φ ψ : ClassFunction G k) :
    restrict H (φ * ψ) = restrict H φ * restrict H ψ := by
  ext h; simp

/-- **The projection (Frobenius–Nakayama) formula.**  For `H ≤ G`, a class function `φ` on `G` and
a class function `χ` on `H`, `Ind_H^G (Res_H φ · χ) = φ · Ind_H^G χ`.  Each induction term
`induceTerm H (Res_H φ · χ) x g` factors as `φ(g) · induceTerm H χ x g`: `φ` is constant on the
conjugacy class of `g` (`conj_eq`), so `φ(x⁻¹gx) = φ(g)` pulls out of the sum.

Key identity behind Peterfalvi (1.7.b): with `χ = Res_H ψ` (`ψ ∈ Irr T` over `θ`), `H ⊴ T`,
`T/H` abelian, `Ind_H^T(Res_H ψ) = ψ · Ind_H^T 1_H = ∑_{λ ∈ Irr(T/H)} λψ` — the equal-degree
induced-constituent decomposition for an abelian inertia quotient, needed at the `H'/H` level of
Peterfalvi (12.5) where `T/H` abelian is automatic (`H' = [H,H]`). -/
theorem induce_restrict_mul [Fintype G] {H : Subgroup G} [Invertible (Nat.card H : k)]
    (φ : ClassFunction G k) (χ : ClassFunction ↥H k) :
    induce H (restrict H φ * χ) = φ * induce H χ := by
  classical
  ext g
  have hterm : ∀ x : G, induceTerm H (restrict H φ * χ) x g = φ g * induceTerm H χ x g := by
    intro x
    by_cases hx : x⁻¹ * g * x ∈ H
    · rw [induceTerm_of_mem _ hx, induceTerm_of_mem _ hx, mul_apply, restrict_apply]
      have h : φ ((⟨x⁻¹ * g * x, hx⟩ : ↥H) : G) = φ g := by
        have h2 := φ.conj_eq g x⁻¹
        rwa [inv_inv] at h2
      rw [h]
    · rw [induceTerm_of_not_mem _ hx, induceTerm_of_not_mem _ hx, mul_zero]
  rw [mul_apply, induce_apply, induce_apply, Finset.sum_congr rfl (fun x _ => hterm x),
    ← Finset.mul_sum]
  ring

/-- Pullback along a group homomorphism is multiplicative for the pointwise product. -/
@[simp] theorem compHom_mul {K : Type*} [Group K] (f : K →* G) (φ ψ : ClassFunction G k) :
    compHom f (φ * ψ) = compHom f φ * compHom f ψ := by
  ext x; simp

/-- **Twisting by a factor that is `1` on `H` does not change the restriction to `H`.**  If
`lam x = 1` for every `x ∈ H`, then `Res_H (χ · lam) = Res_H χ`.  In Gallagher's theorem `lam =
Inf(β)` is inflated from `I/H`, hence `1` on `H`, so `χ · Inf(β)` restricts to `Res_H χ = θ` — i.e.
it lies over `θ` — and `⟨Ind_H^I θ, χ·Inf(β)⟩ = ⟨θ, Res_H(χ·Inf β)⟩ = ⟨θ, θ⟩ = 1`. -/
theorem restrict_mul_of_apply_eq_one {H : Subgroup G} (χ lam : ClassFunction G k)
    (hlam : ∀ x : ↥H, lam (x : G) = 1) :
    restrict H (χ * lam) = restrict H χ := by
  ext h
  simp only [restrict_apply, mul_apply, hlam, mul_one]

end ClassFunction

variable {G : Type*} [Group G]

/-- **The product of two characters is a character.**  If `φ = χ_ρ` and `ψ = χ_σ` are the characters
of finite-dimensional representations `ρ, σ`, then `φ · ψ` is the character of the tensor-product
representation `ρ ⊗ σ` (`Representation.char_tensor`), hence a genuine character.  This is the
character-level form of "`Irr` is closed under tensor products", and the engine behind Gallagher. -/
theorem IsCharacter.mul {φ ψ : ClassFunction G ℂ} (hφ : IsCharacter φ) (hψ : IsCharacter ψ) :
    IsCharacter (φ * ψ) := by
  obtain ⟨V, _, _, _, ρ, hρ⟩ := hφ
  obtain ⟨W, _, _, _, σ, hσ⟩ := hψ
  refine ⟨TensorProduct ℂ V W, inferInstance, inferInstance, inferInstance,
    Representation.tprod ρ σ, ?_⟩
  funext g
  rw [ClassFunction.mul_apply, Representation.char_tensor, Pi.mul_apply, congrFun hρ g,
    congrFun hσ g]

/-- **Twisting by a unit-norm class function preserves the inner product.**  If `lam` has unit norm
at every element (`lam g · conj (lam g) = 1` — e.g. a linear character, whose values are roots of
unity), then `⟨χ · lam, χ · lam⟩ = ⟨χ, χ⟩` for every class function `χ`.  Pointwise,
`(χ·lam)(g) · conj((χ·lam)(g)) = χ(g)·conj(χ(g)) · (lam g · conj (lam g)) = χ(g)·conj(χ(g))`.

This is the norm-preservation behind Gallagher's theorem: `χ · Inf(β)` has the same norm as `χ`, so
an irreducible `χ` twisted by a linear character `Inf(β)` stays of norm one — hence irreducible. -/
theorem inner_mul_self_eq_of_star_mul_self_eq_one {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (χ : ClassFunction G ℂ) {lam : ClassFunction G ℂ}
    (hlam : ∀ g, lam g * star (lam g) = 1) :
    ClassFunction.inner (χ * lam) (χ * lam) = ClassFunction.inner χ χ := by
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.inner_eq_inv_card_mul_innerSum]
  congr 1
  unfold ClassFunction.innerSum
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [ClassFunction.mul_apply, star_mul']
  rw [show χ g * lam g * (star (χ g) * star (lam g))
        = χ g * star (χ g) * (lam g * star (lam g)) from by ring, hlam g, mul_one]

/-- **An irreducible character has squared norm one** (`⟨χ, χ⟩ = 1`) — the `Prop`-level restatement
of orthonormality (`irreducibleCharacter_inner_eq_ite`) for the bundled `⟨χ, hχ⟩`. -/
theorem IsIrreducibleCharacter.inner_self_eq_one {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {χ : ClassFunction G ℂ} (hχ : IsIrreducibleCharacter χ) :
    ClassFunction.inner χ χ = 1 := by
  simpa using irreducibleCharacter_inner_eq_ite (⟨χ, hχ⟩ : IrreducibleCharacter G) ⟨χ, hχ⟩

/-- **An irreducible character has a positive natural degree** (`χ(1) = d`, `0 < d`), `Prop`-level
restatement of `irreducibleCharacter_apply_one_eq_pos_natCast` for the bundled `⟨χ, hχ⟩`. -/
theorem IsIrreducibleCharacter.exists_apply_one_eq_pos_natCast {G : Type*} [Group G] [Finite G]
    {χ : ClassFunction G ℂ} (hχ : IsIrreducibleCharacter χ) :
    ∃ d : ℕ, 0 < d ∧ (χ : G → ℂ) 1 = (d : ℂ) := by
  obtain ⟨d, hd, h1⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ, hχ⟩ : IrreducibleCharacter G)
  exact ⟨d, hd, by simpa using h1⟩

/-- **Twisting an irreducible character by a unit-norm degree-one character preserves
irreducibility.**  If `χ ∈ Irr G` and `lam` is a genuine character with unit norm everywhere
(`lam g · conj (lam g) = 1`) and degree one (`lam 1 = 1`) — e.g. a linear character — then
`χ · lam ∈ Irr G`.  Indeed `χ · lam` is a virtual character (`IsCharacter.mul` + `mem_ZIrr`) of
squared norm `⟨χ · lam, χ · lam⟩ = ⟨χ, χ⟩ = 1` (`inner_mul_self_eq_of_star_mul_self_eq_one` +
`inner_self_eq_one`) and positive degree `(χ · lam)(1) = χ(1) · 1 = χ(1) > 0`; so it is irreducible
(`isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos`).  This is the irreducibility engine of
Gallagher's theorem: `χ · Inf(β)` (with `Inf(β)` a linear character) is irreducible. -/
theorem isIrreducibleCharacter_mul_of_unit_norm {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {χ lam : ClassFunction G ℂ}
    (hχ : IsIrreducibleCharacter χ) (hlamC : IsCharacter lam)
    (hlamU : ∀ g, lam g * star (lam g) = 1) (hlam1 : (lam : G → ℂ) 1 = 1) :
    IsIrreducibleCharacter (χ * lam) := by
  have hzirr : (χ * lam) ∈ ZIrr G := (hχ.isCharacter.mul hlamC).mem_ZIrr
  have hnorm : ClassFunction.inner (χ * lam) (χ * lam) = 1 := by
    rw [inner_mul_self_eq_of_star_mul_self_eq_one χ hlamU, hχ.inner_self_eq_one]
  have hpos : ∃ d : ℕ, 0 < d ∧ (χ * lam) 1 = (d : ℂ) := by
    obtain ⟨d, hd, h1⟩ := hχ.exists_apply_one_eq_pos_natCast
    refine ⟨d, hd, ?_⟩
    simp only [ClassFunction.mul_apply, hlam1, mul_one, h1]
  exact isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos hzirr hnorm hpos

/-- **A linear character has unit norm at every element.**  For `χ : H →* ℂˣ` on a *finite* group,
the value `(χ h : ℂ)` is a root of unity (`(χ h)^{|H|} = χ(h^{|H|}) = 1`, `pow_card_eq_one'`), so
`‖χ h‖ = 1` (`Complex.norm_eq_one_of_pow_eq_one`), whence `star (χ h) = (χ h)⁻¹`
(`RCLike.inv_eq_conj`) and `(χ h) · star (χ h) = 1`.  This supplies the unit-norm hypothesis of
`isIrreducibleCharacter_mul_of_unit_norm`, so twisting an irreducible character by the linear
character `linearClassFunction χ` (`Inf(β)` in Gallagher) preserves irreducibility. -/
theorem linearClassFunction_mul_star_self_eq_one {H : Type*} [Group H] [Finite H]
    (χ : H →* ℂˣ) (h : H) :
    (linearClassFunction χ) h * star ((linearClassFunction χ) h) = 1 := by
  have hpow : (χ h : ℂ) ^ (Nat.card H) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  have hnorm : ‖(χ h : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow Nat.card_pos.ne'
  have hstar : star (χ h : ℂ) = (χ h : ℂ)⁻¹ := by
    rw [RCLike.inv_eq_conj hnorm, starRingEnd_apply]
  rw [linearClassFunction_apply, hstar]
  exact mul_inv_cancel₀ (Units.ne_zero (χ h))

/-- **Twisting an irreducible character by a linear character preserves irreducibility.**
Specialization of `isIrreducibleCharacter_mul_of_unit_norm` to `lam = linearClassFunction χlin`
(`χlin : G →* ℂˣ`): the linear character is a genuine character of unit norm
(`linearClassFunction_mul_star_self_eq_one`) and degree one, so `χ · linearClassFunction χlin ∈
Irr G` whenever `χ ∈ Irr G`.  This is the form used in Gallagher's theorem (`χlin = Inf(β)`). -/
theorem isIrreducibleCharacter_mul_linearClassFunction {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {χ : ClassFunction G ℂ} (hχ : IsIrreducibleCharacter χ)
    (χlin : G →* ℂˣ) :
    IsIrreducibleCharacter (χ * linearClassFunction χlin) := by
  have hlirr : IsIrreducibleCharacter (linearClassFunction χlin) := by
    have h := (linearIrreducibleCharacter χlin).isIrreducible
    rwa [linearIrreducibleCharacter_coe] at h
  refine isIrreducibleCharacter_mul_of_unit_norm hχ hlirr.isCharacter
    (linearClassFunction_mul_star_self_eq_one χlin) ?_
  simp

/-- **An inflated linear character is `1` on the normal subgroup.**  For `χbar : (G ⧸ H) →* ℂˣ`,
the linear character `Inf(χbar) = linearClassFunction (χbar ∘ mk' H)` of `G` takes the value `1` at
every `x ∈ H` (the quotient map kills `H`).  Combined with
`ClassFunction.restrict_mul_of_apply_eq_one` this gives `Res_H (χ · Inf(χbar)) = Res_H χ`: the
Gallagher twist `χ · Inf(β)` lies over the same
character of `H` as `χ`. -/
theorem linearClassFunction_comp_mk'_apply_eq_one {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    (χbar : (G ⧸ H) →* ℂˣ) {x : G} (hx : x ∈ H) :
    (linearClassFunction (χbar.comp (QuotientGroup.mk' H))) x = 1 := by
  rw [linearClassFunction_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    (QuotientGroup.eq_one_iff x).mpr hx, map_one, Units.val_one]

/-- **Enough multiplicity-one constituents recover a class function.**  If a finite set `S` of
irreducible characters each occurs in `φ` with multiplicity one (`⟨φ, χ⟩ = 1`), and the squared
norm `⟨φ, φ⟩` equals `|S|`, then `φ = ∑_{χ ∈ S} χ` — no other irreducibles occur.

Parseval `⟨φ, φ⟩ = ∑_{χ ∈ Irr} |⟨φ, χ⟩|²` (from the Fourier expansion
`sum_inner_irreducibleCharacter_smul`) plus the hypotheses force `∑_{χ ∉ S} |⟨φ, χ⟩|² = 0`, so every
Fourier coefficient off `S` vanishes; the expansion then collapses to `∑_{χ ∈ S} χ`.  This is the
capstone that turns "`[I:H]` distinct mult-one constituents of `Ind_H^I θ`" into the Gallagher
decomposition `Ind_H^I θ = ∑_β χ·Inf(β)`. -/
theorem eq_sum_of_inner_eq_one_of_inner_self_eq_card {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] [Fintype (IrreducibleCharacter G)] {φ : ClassFunction G ℂ}
    {S : Finset (IrreducibleCharacter G)}
    (h1 : ∀ χ ∈ S, ClassFunction.inner φ (χ : ClassFunction G ℂ) = 1)
    (hnorm : ClassFunction.inner φ φ = (S.card : ℂ)) :
    φ = ∑ χ ∈ S, (χ : ClassFunction G ℂ) := by
  classical
  -- Parseval: `⟨φ, φ⟩ = ∑_χ ⟨φ,χ⟩ · star ⟨φ,χ⟩`.
  have hpars : ClassFunction.inner φ φ
      = ∑ χ : IrreducibleCharacter G, ClassFunction.inner φ (χ : ClassFunction G ℂ)
          * star (ClassFunction.inner φ (χ : ClassFunction G ℂ)) := by
    calc ClassFunction.inner φ φ
        = ClassFunction.inner (∑ χ : IrreducibleCharacter G,
            ClassFunction.inner φ (χ : ClassFunction G ℂ) • (χ : ClassFunction G ℂ)) φ := by
          rw [sum_inner_irreducibleCharacter_smul]
      _ = ∑ χ : IrreducibleCharacter G, ClassFunction.inner
            (ClassFunction.inner φ (χ : ClassFunction G ℂ) • (χ : ClassFunction G ℂ)) φ :=
          inner_sum_left _ _ _
      _ = _ := by
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [ClassFunction.inner_smul_left, inner_conj_symm φ (χ : ClassFunction G ℂ)]
  -- The `S`-terms already account for the full norm, so the complement sum vanishes.
  have hSsum : ∑ χ ∈ S, ClassFunction.inner φ (χ : ClassFunction G ℂ)
      * star (ClassFunction.inner φ (χ : ClassFunction G ℂ)) = (S.card : ℂ) := by
    rw [Finset.sum_congr rfl fun χ hχ => by rw [h1 χ hχ, star_one, mul_one],
      Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcompl : ∑ χ ∈ Finset.univ \ S, ClassFunction.inner φ (χ : ClassFunction G ℂ)
      * star (ClassFunction.inner φ (χ : ClassFunction G ℂ)) = 0 := by
    have key : (∑ χ ∈ Finset.univ \ S, ClassFunction.inner φ (χ : ClassFunction G ℂ)
          * star (ClassFunction.inner φ (χ : ClassFunction G ℂ)))
        + ∑ χ ∈ S, ClassFunction.inner φ (χ : ClassFunction G ℂ)
          * star (ClassFunction.inner φ (χ : ClassFunction G ℂ))
        = ClassFunction.inner φ φ := by
      rw [hpars, ← Finset.sum_union Finset.sdiff_disjoint,
        Finset.sdiff_union_of_subset (Finset.subset_univ S)]
    rw [hSsum, hnorm] at key
    linear_combination key
  -- Each complement term is `↑(normSq ⟨φ,χ⟩) ≥ 0`, so the vanishing sum forces `⟨φ,χ⟩ = 0`.
  have hzero : ∀ χ : IrreducibleCharacter G, χ ∉ S →
      ClassFunction.inner φ (χ : ClassFunction G ℂ) = 0 := by
    intro χ hχ
    have hmem : χ ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ χ, hχ⟩
    have hcast : ∑ ψ ∈ Finset.univ \ S,
        ((Complex.normSq (ClassFunction.inner φ (ψ : ClassFunction G ℂ)) : ℝ) : ℂ) = 0 := by
      rw [← hcompl]
      refine Finset.sum_congr rfl fun ψ _ => ?_
      rw [← starRingEnd_apply]
      exact (Complex.mul_conj _).symm
    rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero] at hcast
    have hnn : ∀ ψ ∈ Finset.univ \ S,
        0 ≤ Complex.normSq (ClassFunction.inner φ (ψ : ClassFunction G ℂ)) :=
      fun ψ _ => Complex.normSq_nonneg _
    exact Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp hcast χ hmem)
  -- Collapse the Fourier expansion to the `S`-sum.
  conv_lhs => rw [← sum_inner_irreducibleCharacter_smul φ]
  rw [← Finset.sum_subset (Finset.subset_univ S)
    (fun χ _ hχ => by rw [hzero χ hχ, zero_smul])]
  exact Finset.sum_congr rfl fun χ hχ => by rw [h1 χ hχ, one_smul]

/-- **A family of irreducible characters whose sum has squared norm equal to the family size is
injective.**  If `η : ι → Irr(G)` (`ι` finite) and the sum `φ = ∑_i η_i` has `⟨φ, φ⟩ = |ι|`, then
`i ↦ η_i` is injective (the summands are pairwise distinct).

Expanding by bilinearity and orthonormality (`irreducibleCharacter_inner_eq_ite`),
`⟨φ, φ⟩ = ∑_{i,j} ⟨η_i, η_j⟩ = |{(i, j) : η_i = η_j}|`.  The diagonal `{(i, i)}` already contributes
`|ι|` elements to that "equal-value" set, so `⟨φ, φ⟩ = |ι|` forces the set to be *exactly* the
diagonal — i.e. `η_a = η_b ⟹ a = b`.

This is the multiplicity-one/distinctness core behind the constructive Clifford decomposition: the
`[T:H]` induced summands `Ind_T^L(χ·Inf β)` of `Ind_H^L θ` are pairwise distinct because their sum
has squared norm `[T:H] = [I_L(θ):H]` (`card_mul_inner_self_induce_eq_card_inertia`). -/
theorem injective_of_sum_inner_self_eq_card {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {ι : Type*} [Fintype ι] (η : ι → IrreducibleCharacter G)
    (hnorm : ClassFunction.inner (∑ i, (η i : ClassFunction G ℂ))
        (∑ i, (η i : ClassFunction G ℂ)) = (Fintype.card ι : ℂ)) :
    Function.Injective η := by
  classical
  -- the squared norm counts the pairs `(i, j)` with `η i = η j`
  have hcardι : (Finset.univ.filter (fun p : ι × ι => η p.1 = η p.2)).card = Fintype.card ι := by
    have hcount : ((Finset.univ.filter (fun p : ι × ι => η p.1 = η p.2)).card : ℂ)
        = (Fintype.card ι : ℂ) := by
      rw [← hnorm, inner_sum_left]
      simp_rw [inner_sum_right, irreducibleCharacter_inner_eq_ite]
      rw [← Finset.sum_product', Finset.univ_product_univ, Finset.sum_boole]
    exact_mod_cast hcount
  -- the diagonal is contained in the equal-value set and also has `|ι|` elements, so they coincide
  have hDF : Finset.univ.image (fun i : ι => (i, i))
      ⊆ Finset.univ.filter (fun p : ι × ι => η p.1 = η p.2) := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨i, _, rfl⟩ := hp
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hDcard : (Finset.univ.image (fun i : ι => (i, i))).card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ (fun a b h => (Prod.ext_iff.mp h).1), Finset.card_univ]
  have hDF_eq : Finset.univ.image (fun i : ι => (i, i))
      = Finset.univ.filter (fun p : ι × ι => η p.1 = η p.2) :=
    Finset.eq_of_subset_of_card_le hDF (le_of_eq (hcardι.trans hDcard.symm))
  -- injectivity: `η a = η b` puts `(a, b)` in the equal-value set = diagonal, forcing `a = b`
  intro a b hab
  have hmem : (a, b) ∈ Finset.univ.filter (fun p : ι × ι => η p.1 = η p.2) := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hab⟩
  rw [← hDF_eq, Finset.mem_image] at hmem
  obtain ⟨i, _, hi⟩ := hmem
  rw [Prod.ext_iff] at hi
  exact hi.1.symm.trans hi.2

/-- **A norm-saturating decomposition into irreducibles is multiplicity-free.**  If `φ = ∑_i η_i`
(a finite family of irreducible characters) and `⟨φ, φ⟩ = |ι|`, then the family is injective
(`injective_of_sum_inner_self_eq_card`), so `φ` is the sum over the finite set `S = image η` of
`|ι|` **distinct** irreducibles, each of which is one of the `η_i`.

This packages the distinctness core for the constructive Clifford decomposition: given
`Ind_H^L θ = ∑_β Ind_T^L(χ·Inf β)` with `⟨Ind_H^L θ, Ind_H^L θ⟩ = [T:H]`, the `[T:H]` summands are
pairwise distinct and constitute the constituent set of `Ind_H^L θ`. -/
theorem exists_finset_eq_sum_of_sum_inner_self_eq_card {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {ι : Type*} [Fintype ι] {φ : ClassFunction G ℂ}
    (η : ι → IrreducibleCharacter G) (hsum : φ = ∑ i, (η i : ClassFunction G ℂ))
    (hnorm : ClassFunction.inner φ φ = (Fintype.card ι : ℂ)) :
    ∃ S : Finset (IrreducibleCharacter G), S.card = Fintype.card ι ∧
      φ = ∑ χ ∈ S, (χ : ClassFunction G ℂ) ∧ (∀ χ ∈ S, ∃ i, η i = χ) := by
  classical
  rw [hsum] at hnorm
  have hinj := injective_of_sum_inner_self_eq_card η hnorm
  refine ⟨Finset.univ.image η, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  · rw [hsum, Finset.sum_image (fun a _ b _ h => hinj h)]
  · intro χ hχ
    rw [Finset.mem_image] at hχ
    obtain ⟨i, _, rfl⟩ := hχ
    exact ⟨i, rfl⟩

end OddOrder.RepresentationTheory


