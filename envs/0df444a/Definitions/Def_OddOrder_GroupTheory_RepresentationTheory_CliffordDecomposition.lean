-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CliffordDecomposition
-- name    : OddOrder_GroupTheory_RepresentationTheory_CliffordDecomposition
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:46:48.069141+00:00
-- url     : https://prove2.me/theorems/2375e610-ebd6-45b3-b543-fd0b158c2599
-- title:
--   The constructive Clifford decomposition (toward Peterfalvi (1.7)(c))
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, Lemma 1.7(c), constructive form: let $H\trianglelefteq L$ and let $\theta\in\mathrm{Irr}(H)$ have inertia group $T=I_L(\theta)$ with $T/H$ abelian and $\gcd([T:H],o(\theta)\theta(1))=1$. The file's result is the book's (1.7)(c), not (1.7)(b).
--
--   Main results: `exists_extension_induce_eq_sum_induce_mul` (the constructive Clifford decomposition) and its distinct-constituent (multiplicity-free) forms `exists_extension_induce_eq_sum_distinct_irreducible` and `exists_extension_induce_eq_sum_distinct_of_inertia_inf_le`, with supporting lemmas such as `conj_induce` and `conjBy_ne_conj_of_odd`.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CliffordDecomposition.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CliffordDecomposition.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CanonicalCharacterExtension
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_GallagherDecomposition
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CliffordCorrespondence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InertiaAbelianQuotient

namespace OddOrder.RepresentationTheory

variable {L : Type*} [Group L] [Fintype L] [Invertible (Nat.card L : ℂ)]

open scoped commutatorElement in
/-- **The constructive Clifford decomposition (toward Peterfalvi (1.7)(c))**.  Let `H ⊴ L`, let
`θ ∈ Irr(H)` have inertia group exactly `T` with `T/H` abelian (elementwise commutator
hypothesis), degree `d`, and `gcd([T:H], o(θ)·d) = 1`.  Then there is an extension
`χ ∈ Irr(T)` of (the transport of) `θ` such that

  `Ind_H^L θ = ∑_{β ∈ Hom(T/H, ℂˣ)} Ind_T^L (χ·Inf(β))`

with **every summand irreducible**.  Each summand has degree `[L:T]·d` by
`ClassFunction.induce_apply_one`. -/
theorem exists_extension_induce_eq_sum_induce_mul
    {H T : Subgroup L} [H.Normal] [(H.subgroupOf T).Normal] (hHT : H ≤ T)
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥T : ℂ)]
    [Invertible (Nat.card ↥(H.subgroupOf T) : ℂ)]
    [Fintype ((↥T ⧸ H.subgroupOf T) →* ℂˣ)]
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ)
    (hinertia : ClassFunction.inertia (G := L) θ = T)
    (hab : ∀ x y : ↥T, ⁅x, y⁆ ∈ H.subgroupOf T)
    {d : ℕ} (hd : θ 1 = (d : ℂ))
    (hcop : Nat.Coprime (H.subgroupOf T).index (orderOf hθ.determinant * d)) :
    ∃ (χ : ClassFunction ↥T ℂ) (_ : IsIrreducibleCharacter χ),
      ClassFunction.restrict (H.subgroupOf T) χ
          = ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ ∧
        ClassFunction.induce H θ
          = ∑ β : (↥T ⧸ H.subgroupOf T) →* ℂˣ,
              ClassFunction.induce T
                (χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T)))) ∧
        ∀ β : (↥T ⧸ H.subgroupOf T) →* ℂˣ,
          IsIrreducibleCharacter (ClassFunction.induce T
            (χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T))))) := by
  classical
  let : Fintype ↥T := Fintype.ofFinite _
  let : Fintype ↥(H.subgroupOf T) := Fintype.ofFinite _
  -- the transported character `θ'` and its properties
  set θ' : ClassFunction ↥(H.subgroupOf T) ℂ :=
    ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ with hθ'def
  have hθ' : IsIrreducibleCharacter θ' :=
    IsIrreducibleCharacter.compHom_of_surjective
      (Subgroup.subgroupOfEquivOfLe hHT).surjective hθ
  -- `θ'` is `T`-invariant (full inertia)
  have hinvT : ∀ t : ↥T, ClassFunction.conjBy ((t : L)) θ = θ := fun t => by
    have hmem : (t : L) ∈ ClassFunction.inertia (G := L) θ := by
      rw [hinertia]
      exact t.2
    exact (ClassFunction.mem_inertia).mp hmem
  have hinertia' : ClassFunction.inertia (G := ↥T) θ' = ⊤ :=
    inertia_compHom_subgroupOfEquivOfLe_eq_top hHT hinvT
  have hinv' : ∀ y : ↥T, ClassFunction.conjBy y θ' = θ' := fun y => by
    have hmem : y ∈ ClassFunction.inertia (G := ↥T) θ' := by
      rw [hinertia']
      exact Subgroup.mem_top y
    exact (ClassFunction.mem_inertia).mp hmem
  -- degree and determinantal order transport
  have hd' : θ' 1 = (d : ℂ) := by
    rw [hθ'def, ClassFunction.compHom_apply, map_one, hd]
  have hodet : orderOf hθ'.determinant = orderOf hθ.determinant := by
    rw [hθ.determinant_compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom hθ']
    exact orderOf_monoidHom_comp_of_surjective _
      (Subgroup.subgroupOfEquivOfLe hHT).surjective
  -- (G1): extend `θ'` to `χ ∈ Irr(T)`
  obtain ⟨χ, hχ, hres, -⟩ :=
    hθ'.exists_extension_of_forall_conjBy_eq hinv' hab hd'
      (by rw [hodet]; exact hcop)
  refine ⟨χ, hχ, hres, ?_, ?_⟩
  · -- the decomposition, by stages + Gallagher + linearity
    have hstages := induce_induce_subgroupOf (M := L) hHT θ
    -- (G2) at the inertia group
    have hgal := induce_eq_sum_mul_linearClassFunction (K := ↥T) (H := H.subgroupOf T)
      hθ' hinv' hab hχ hres hd'
      (Nat.Coprime.coprime_dvd_right (dvd_mul_left d _) hcop)
    -- push the sum through `Ind_T^L`
    have hindsum : ∀ (s : Finset ((↥T ⧸ H.subgroupOf T) →* ℂˣ))
        (F : ((↥T ⧸ H.subgroupOf T) →* ℂˣ) → ClassFunction ↥T ℂ),
        ClassFunction.induce T (∑ β ∈ s, F β)
          = ∑ β ∈ s, ClassFunction.induce T (F β) := by
      intro s F
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.induce_add, ih]
    calc ClassFunction.induce H θ
        = ClassFunction.induce T (ClassFunction.induce (H.subgroupOf T) θ') := hstages.symm
      _ = ClassFunction.induce T (∑ β : (↥T ⧸ H.subgroupOf T) →* ℂˣ,
            χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T)))) := by
          rw [hgal]
      _ = ∑ β : (↥T ⧸ H.subgroupOf T) →* ℂˣ,
            ClassFunction.induce T
              (χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T)))) :=
          hindsum _ _
  · -- each summand is irreducible, by the Clifford correspondence (G3)
    intro β
    -- the twist is irreducible and restricts to `θ'`
    have hψirr : IsIrreducibleCharacter
        (χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T)))) :=
      isIrreducibleCharacter_mul_linearClassFunction hχ _
    have hψres : ClassFunction.restrict (H.subgroupOf T)
        (χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T)))) = θ' := by
      rw [ClassFunction.restrict_mul_of_apply_eq_one χ _
        (fun x => linearClassFunction_comp_mk'_apply_eq_one β x.2), hres]
    -- apply Isaacs 6.11 with `ψ = χ·Inf(β)`
    have h611 := isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq (G := L) hHT hθ
      hinertia
      (⟨χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T))), hψirr⟩ :
        IrreducibleCharacter ↥T)
      (by
        change ClassFunction.restrictionMultiplicity (H.subgroupOf T)
          (χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T)))) θ' ≠ 0
        rw [ClassFunction.restrictionMultiplicity_def, hψres, hθ'.inner_self_eq_one]
        exact one_ne_zero)
    exact h611

open scoped commutatorElement in
/-- **The constructive Clifford decomposition, distinct-constituent (multiplicity-free) form**
(the mult-one packaging; this is Peterfalvi **(1.7)(c)** up to the shape of the coprimality
hypothesis -- see `exists_induce_eq_sum_distinct_irreducible_of_coprime_card` for the book's own
hypothesis `gcd(|H|, [T:H]) = 1`).  Under the hypotheses of
`exists_extension_induce_eq_sum_induce_mul`, the `[T:H]` induced summands `Ind_T^L(χ·Inf β)` of
`Ind_H^L θ` are **pairwise distinct**: there is an extension `χ ∈ Irr(T)` of `θ` and a finite set
`S` of `[T:H]` distinct irreducible characters of `L` with

  `Ind_H^L θ = ∑_{φ ∈ S} φ`,

each `φ` of degree `[L:T]·θ(1)` and of the form `Ind_T^L(χ·Inf β)` for some `β`.

Distinctness is the norm count: `⟨Ind_H^L θ, Ind_H^L θ⟩ = [I_L(θ):H] = [T:H]`
(`card_mul_inner_self_induce_eq_card_inertia`, since `I_L(θ) = T`), which equals the number
`|Hom(T/H, ℂˣ)|` of summands (`CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`), so the family
`β ↦ Ind_T^L(χ·Inf β)` is injective (`injective_of_sum_inner_self_eq_card`) and its image is `S`.

This is layer (a) of the type-I application `typeI_induced_char_constituents`; the non-reality,
conjugate-distinctness and support (`⊆ A(L) ∪ {1}`) are the §8/type-I bookkeeping (layer (b)) built
on top of the structural witness `φ = Ind_T^L(χ·Inf β)` exposed here. -/
theorem exists_extension_induce_eq_sum_distinct_irreducible
    {H T : Subgroup L} [H.Normal] [(H.subgroupOf T).Normal] (hHT : H ≤ T)
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥T : ℂ)]
    [Invertible (Nat.card ↥(H.subgroupOf T) : ℂ)]
    [Finite ((↥T ⧸ H.subgroupOf T) →* ℂˣ)]
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ)
    (hinertia : ClassFunction.inertia (G := L) θ = T)
    (hab : ∀ x y : ↥T, ⁅x, y⁆ ∈ H.subgroupOf T)
    {d : ℕ} (hd : θ 1 = (d : ℂ))
    (hcop : Nat.Coprime (H.subgroupOf T).index (orderOf hθ.determinant * d)) :
    ∃ (χ : ClassFunction ↥T ℂ) (_ : IsIrreducibleCharacter χ)
      (S : Finset (IrreducibleCharacter L)), S.Nonempty ∧
      S.card = (H.subgroupOf T).index ∧
      ClassFunction.induce H θ = ∑ φ ∈ S, (φ : ClassFunction L ℂ) ∧
      (∀ φ ∈ S, (φ : ClassFunction L ℂ) 1 = (T.index : ℂ) * (d : ℂ)) ∧
      (∀ φ ∈ S, ∃ β : (↥T ⧸ H.subgroupOf T) →* ℂˣ,
        (φ : ClassFunction L ℂ) = ClassFunction.induce T
          (χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T))))) := by
  classical
  have : Fintype ((↥T ⧸ H.subgroupOf T) →* ℂˣ) := Fintype.ofFinite _
  let : Fintype ↥H := Fintype.ofFinite _
  let : Fintype ↥T := Fintype.ofFinite _
  obtain ⟨χ, hχ, hres, hdecomp, hirr⟩ :=
    exists_extension_induce_eq_sum_induce_mul hHT hθ hinertia hab hd hcop
  refine ⟨χ, hχ, ?_⟩
  -- `χ` restricts to `θ`, so `χ(1) = θ(1) = d`
  have hχ1 : χ (1 : ↥T) = (d : ℂ) := by
    have h := congrArg (fun f : ClassFunction ↥(H.subgroupOf T) ℂ => (f : _ → ℂ) 1) hres
    simp only [ClassFunction.restrict_apply, ClassFunction.compHom_apply, OneMemClass.coe_one,
      map_one] at h
    rw [h]; exact hd
  -- each induced summand has degree `[L:T]·d`
  have hdeg : ∀ β : (↥T ⧸ H.subgroupOf T) →* ℂˣ,
      ClassFunction.induce T (χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T))))
          (1 : L) = (T.index : ℂ) * (d : ℂ) := by
    intro β
    have hval : (χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T)))) (1 : ↥T)
        = (d : ℂ) := by
      rw [ClassFunction.mul_apply, hχ1, linearClassFunction_apply, map_one, Units.val_one, mul_one]
    rw [ClassFunction.induce_apply_one, hval]
  -- the quotient `T/H` is a finite abelian group, so it has `[T:H]` linear characters
  let : CommGroup (↥T ⧸ H.subgroupOf T) :=
    { (inferInstance : Group (↥T ⧸ H.subgroupOf T)) with
      mul_comm := fun a b => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        refine (QuotientGroup.eq).mpr ?_
        have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
          rw [commutatorElement_def]; group
        rw [h1]; exact hab y⁻¹ x⁻¹ }
  have : NeZero (Monoid.exponent (↥T ⧸ H.subgroupOf T)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hcardHom : Fintype.card ((↥T ⧸ H.subgroupOf T) →* ℂˣ) = (H.subgroupOf T).index := by
    rw [← Nat.card_eq_fintype_card]
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (↥T ⧸ H.subgroupOf T) ℂ
  -- norm identity `⟨Ind_H θ, Ind_H θ⟩ = [T:H] = |Hom(T/H, ℂˣ)|`
  have hnorm : ClassFunction.inner (ClassFunction.induce H θ) (ClassFunction.induce H θ)
      = (Fintype.card ((↥T ⧸ H.subgroupOf T) →* ℂˣ) : ℂ) := by
    rw [hcardHom]
    have hkey := card_mul_inner_self_induce_eq_card_inertia (G := L)
      (⟨θ, hθ⟩ : IrreducibleCharacter ↥H)
    have hcoeθ : ((⟨θ, hθ⟩ : IrreducibleCharacter ↥H) : ClassFunction ↥H ℂ) = θ := rfl
    rw [hcoeθ, hinertia] at hkey
    have hcardT : (Nat.card ↥T : ℂ) = ((H.subgroupOf T).index : ℂ) * (Nat.card ↥H : ℂ) := by
      have h1 : (H.subgroupOf T).index * Nat.card ↥(H.subgroupOf T) = Nat.card ↥T :=
        Subgroup.index_mul_card (H.subgroupOf T)
      have h2 : Nat.card ↥(H.subgroupOf T) = Nat.card ↥H :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHT).toEquiv
      rw [h2] at h1
      rw [← h1]; push_cast; ring
    rw [hcardT] at hkey
    have hne : (Nat.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    apply mul_left_cancel₀ hne
    rw [hkey]; ring
  -- the irreducible induced summands, indexed by the linear characters of `T/H`
  -- (a transparent `let` so the coercion `↑(η β)` reduces to `Ind_T(χ·Inf β)` per-term, avoiding
  -- a sum-level `induce` whnf explosion)
  let η : ((↥T ⧸ H.subgroupOf T) →* ℂˣ) → IrreducibleCharacter L := fun β =>
    ⟨ClassFunction.induce T (χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T)))),
      hirr β⟩
  have hsum : ClassFunction.induce H θ = ∑ β, (η β : ClassFunction L ℂ) := by
    rw [hdecomp]
  -- distinctness: package the norm-saturating decomposition into a finset of `[T:H]` distinct
  -- irreducibles
  obtain ⟨S, hScard, hSsum, hSwit⟩ := exists_finset_eq_sum_of_sum_inner_self_eq_card η hsum hnorm
  rw [hcardHom] at hScard
  refine ⟨S, ?_, hScard, hSsum, ?_, ?_⟩
  · rw [← Finset.card_pos, hScard]
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  · intro φ hφ
    obtain ⟨β, rfl⟩ := hSwit φ hφ
    exact hdeg β
  · intro φ hφ
    obtain ⟨β, rfl⟩ := hSwit φ hφ
    exact ⟨β, rfl⟩

open scoped commutatorElement in
/-- **The distinct-constituent Clifford decomposition from a type-`F`-style inertia hypothesis**
(Peterfalvi (1.7)(c), packaged for the type-I application).  This replaces the abstract
"`T/H` abelian" hypothesis `hab` of `exists_extension_induce_eq_sum_distinct_irreducible` with the
concrete Peterfalvi (8.2.c) data: a complement `Γ = H U` (`H ⊔ U = ⊤`), the inertia bound
`I(θ) ∩ U ≤ U₁`, and `U₁` abelian.  From these, `I(θ) ∩ U` is abelian
(`inertia_inf_isMulCommutative_of_le`) and hence `⁅I(θ), I(θ)⁆ ≤ H`
(`commutator_inertia_le_of_sup_eq_top`), which is exactly the abelian-quotient hypothesis.

Stated so it can be discharged by the type-`F` consumer (which has (8.2.c) =
`typeF_inertia_inf_le_U1`
and the complement in scope) **without importing the Feit–Thompson `Hypothesis` structure** — the
leaf stays upstream of Peterfalvi §14, so the general `typeI_induced_char_constituents` can cite it
without an import cycle. -/
theorem exists_extension_induce_eq_sum_distinct_of_inertia_inf_le
    {H U U1 T : Subgroup L} [H.Normal] [(H.subgroupOf T).Normal] (hHT : H ≤ T)
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥T : ℂ)]
    [Invertible (Nat.card ↥(H.subgroupOf T) : ℂ)]
    [Finite ((↥T ⧸ H.subgroupOf T) →* ℂˣ)]
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ)
    (hinertia : ClassFunction.inertia (G := L) θ = T)
    (hHU : H ⊔ U = ⊤)
    (hbound : ClassFunction.inertia (G := L) θ ⊓ U ≤ U1)
    (hU1comm : IsMulCommutative ↥U1)
    {d : ℕ} (hd : θ 1 = (d : ℂ))
    (hcop : Nat.Coprime (H.subgroupOf T).index (orderOf hθ.determinant * d)) :
    ∃ (χ : ClassFunction ↥T ℂ) (_ : IsIrreducibleCharacter χ)
      (S : Finset (IrreducibleCharacter L)), S.Nonempty ∧
      S.card = (H.subgroupOf T).index ∧
      ClassFunction.induce H θ = ∑ φ ∈ S, (φ : ClassFunction L ℂ) ∧
      (∀ φ ∈ S, (φ : ClassFunction L ℂ) 1 = (T.index : ℂ) * (d : ℂ)) ∧
      (∀ φ ∈ S, ∃ β : (↥T ⧸ H.subgroupOf T) →* ℂˣ,
        (φ : ClassFunction L ℂ) = ClassFunction.induce T
          (χ * linearClassFunction (β.comp (QuotientGroup.mk' (H.subgroupOf T))))) := by
  -- (8.2.c) + abelian `U₁` ⟹ `I(θ) ∩ U` abelian ⟹ `⁅I(θ), I(θ)⁆ ≤ H` = the abelian-quotient
  -- hypothesis
  have hcomm : IsMulCommutative ↥(ClassFunction.inertia (G := L) θ ⊓ U) :=
    ClassFunction.inertia_inf_isMulCommutative_of_le θ hbound hU1comm
  have hcommle : ⁅ClassFunction.inertia (G := L) θ, ClassFunction.inertia (G := L) θ⁆ ≤ H :=
    ClassFunction.commutator_inertia_le_of_sup_eq_top hHU θ hcomm
  rw [hinertia] at hcommle
  have hab : ∀ x y : ↥T, ⁅x, y⁆ ∈ H.subgroupOf T := by
    intro x y
    rw [Subgroup.mem_subgroupOf]
    have hcoe : ((⁅x, y⁆ : ↥T) : L) = ⁅(x : L), (y : L)⁆ := map_commutatorElement T.subtype x y
    rw [hcoe]
    exact hcommle (Subgroup.commutator_mem_commutator x.2 y.2)
  exact exists_extension_induce_eq_sum_distinct_irreducible hHT hθ hinertia hab hd hcop

omit [Fintype L] [Invertible (Nat.card L : ℂ)] in
/-- **Coprimality of the inertia index with the character order·degree, from a Hall subgroup.**
For `H ⊴ L` with `gcd(|H|, [L:H]) = 1` (`H` Hall) and `θ ∈ Irr(H)` of degree `d`, the index `[T:H]`
of `H` in any intermediate `H ≤ T ≤ L` is coprime to `o(det θ)·d`.  Indeed `[T:H] ∣ [L:H]`
(index tower `relIndex_mul_index`), `d ∣ |H|` (Ito's theorem,
`exists_natDegree_charValue_one_dvd_card`), and `o(det θ) ∣ |H|` (a linear character's order divides
the group order, `det θ ^ |H| = 1`); the Hall coprimality `gcd(|H|, [L:H]) = 1` then separates
`[T:H]` from `o(det θ)·d`.

Supplies the `hcop` hypothesis of `exists_extension_induce_eq_sum_distinct_of_inertia_inf_le` in the
type-I application, where `H = L_F` is a normal Hall subgroup of `L`. -/
theorem coprime_index_orderOf_determinant_mul_of_coprime_index [Finite L]
    {H T : Subgroup L} [H.Normal] (hHT : H ≤ T)
    (hHall : Nat.Coprime (Nat.card ↥H) H.index)
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ) {d : ℕ} (hd : θ 1 = (d : ℂ)) :
    Nat.Coprime (H.subgroupOf T).index (orderOf hθ.determinant * d) := by
  have : Finite ↥H := inferInstance
  -- `d ∣ |H|` (Ito's theorem)
  obtain ⟨n, -, hn_val, hn_dvd⟩ := hθ.exists_natDegree_charValue_one_dvd_card
  have hdn : d = n := by
    have hdc : (d : ℂ) = (n : ℂ) := by rw [← hd, hn_val]
    exact_mod_cast hdc
  have hd_dvd : d ∣ Nat.card ↥H := hdn ▸ hn_dvd
  -- `o(det θ) ∣ |H|` (a linear character has `|H|`-torsion)
  have ho_dvd : orderOf hθ.determinant ∣ Nat.card ↥H := by
    apply orderOf_dvd_of_pow_eq_one
    ext h
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow, pow_card_eq_one', map_one]
  -- `[T:H] ∣ [L:H]` (index tower)
  have hidx_dvd : (H.subgroupOf T).index ∣ H.index :=
    ⟨T.index, (Subgroup.relIndex_mul_index hHT).symm⟩
  -- combine via the Hall coprimality `gcd(|H|, [L:H]) = 1`
  have hcop_Hi : Nat.Coprime H.index (Nat.card ↥H) := hHall.symm
  exact ((hcop_Hi.coprime_dvd_right ho_dvd).mul_right
    (hcop_Hi.coprime_dvd_right hd_dvd)).coprime_dvd_left hidx_dvd

omit [Invertible (Nat.card L : ℂ)] in
/-- **Induction commutes with complex conjugation**: `(Ind_H^L θ)̄ = Ind_H^L (θ̄)`.  Pointwise
`star` distributes over the induction sum `⅟|H| · ∑_x induceTerm θ x g` (`star_sum`, `star_invOf`,
`star_natCast`), and `star (induceTerm θ x g) = induceTerm θ̄ x g` since `θ̄ = star ∘ θ`.  Used to
identify `(Ind_H^L θ)̄` with `Ind_H^L θ̄` in the conjugate-distinctness argument. -/
theorem conj_induce {H : Subgroup L} [Invertible (Nat.card ↥H : ℂ)] (θ : ClassFunction ↥H ℂ) :
    (ClassFunction.induce H θ).conj = ClassFunction.induce H θ.conj := by
  ext g
  have hterm : ∀ x : L, star (ClassFunction.induceTerm H θ x g)
      = ClassFunction.induceTerm H θ.conj x g := by
    intro x
    by_cases hx : x⁻¹ * g * x ∈ H
    · rw [ClassFunction.induceTerm_of_mem θ hx, ClassFunction.induceTerm_of_mem θ.conj hx,
        ClassFunction.conj_apply]
    · rw [ClassFunction.induceTerm_of_not_mem θ hx, ClassFunction.induceTerm_of_not_mem θ.conj hx,
        star_zero]
  simp only [ClassFunction.conj_apply, ClassFunction.induce_apply]
  rw [star_mul', star_sum]
  simp_rw [hterm]
  have hSAbase : IsSelfAdjoint (Nat.card ↥H : ℂ) := star_natCast (Nat.card ↥H)
  have hSA : star (⅟ (Nat.card ↥H : ℂ)) = ⅟ (Nat.card ↥H : ℂ) := hSAbase.invOf.star_eq
  rw [hSA, mul_comm]

omit [Fintype L] in
omit [Invertible (Nat.card L : ℂ)] in
/-- **Conjugation by a group element commutes with complex conjugation** of class functions:
`(θ^g)̄ = (θ̄)^g`.  Both sides evaluate to `star (θ ⟨g h g⁻¹⟩)`. -/
theorem conjBy_conj {H : Subgroup L} [H.Normal] (g : L) (θ : ClassFunction ↥H ℂ) :
    (ClassFunction.conjBy g θ).conj = ClassFunction.conjBy g θ.conj := by
  ext h
  rw [ClassFunction.conj_apply, ClassFunction.conjBy_apply, ClassFunction.conjBy_apply,
    ClassFunction.conj_apply]

omit [Fintype L] [Invertible (Nat.card L : ℂ)] in
/-- **In a group of odd order, no `L`-conjugate of `θ ∈ Irr(H)` (`θ ≠ 1`, `H ⊴ L`) equals its
complex conjugate `θ̄`** (Peterfalvi (1.1)-adjacent).  If `θ^g = θ̄`, apply `^g` again and use
`θ̄̄ = θ`: `θ^{g²} = θ`, so `g² ∈ I_L(θ)`.  Since `g` has odd order (`Odd (Nat.card L)`),
`⟨g⟩ = ⟨g²⟩` (`g = (g²)^{(o+1)/2}`), so `g ∈ I_L(θ)` too — hence `θ^g = θ`, i.e. `θ = θ̄` is real,
forcing `θ = 1_H` (odd order, `not_isReal_of_ne_trivial_of_odd_card'`), a contradiction.  This is
the
`θ̄ ≁_L θ` input that makes the constituents of `Ind_H^L θ` conjugate-distinct. -/
theorem conjBy_ne_conj_of_odd [Finite L] {H : Subgroup L} [H.Normal] [Invertible (Nat.card ↥H : ℂ)]
    (hodd : Odd (Nat.card L)) {θ : ClassFunction ↥H ℂ} (hθirr : IsIrreducibleCharacter θ)
    (hθne : θ ≠ trivialClassFunction ↥H) (g : L) :
    ClassFunction.conjBy g θ ≠ θ.conj := by
  intro hconj
  -- `θ^{g²} = θ`, so `g² ∈ I_L(θ)`
  have hcomm : (ClassFunction.conjBy g θ).conj = ClassFunction.conjBy g θ.conj := conjBy_conj g θ
  have hg2 : ClassFunction.conjBy (g * g) θ = θ := by
    rw [ClassFunction.conjBy_mul, hconj, ← hcomm, hconj, ClassFunction.conj_conj]
  have hg2I : g * g ∈ ClassFunction.inertia θ := ClassFunction.mem_inertia.mpr hg2
  -- odd order: `⟨g⟩ = ⟨g²⟩`, so `g ∈ I_L(θ)`
  have hgI : g ∈ ClassFunction.inertia θ := by
    obtain ⟨m, hm⟩ := hodd.of_dvd_nat (orderOf_dvd_natCard g)
    have hgpow : g = (g * g) ^ (m + 1) := by
      have h1 : (g * g) ^ (m + 1) = g ^ (orderOf g + 1) := by
        rw [← pow_two, ← pow_mul]; congr 1; rw [hm]; ring
      rw [h1, pow_succ, pow_orderOf_eq_one, one_mul]
    rw [hgpow]
    exact (ClassFunction.inertia θ).pow_mem hg2I (m + 1)
  -- `g ∈ I_L(θ)` ⟹ `θ = θ̄` real ⟹ `θ = 1_H`, contradicting `θ ≠ 1_H`
  have hreal : ClassFunction.IsReal θ := by
    change θ.conj = θ
    rw [← hconj]; exact ClassFunction.mem_inertia.mp hgI
  have hoddH : Odd (Nat.card ↥H) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card H)
  have hbne : (⟨θ, hθirr⟩ : IrreducibleCharacter ↥H) ≠ trivialIrreducibleCharacter ↥H :=
    fun heq => hθne (congrArg Subtype.val heq)
  exact not_isReal_of_ne_trivial_of_odd_card' hoddH hbne hreal

/-- **No constituent of `Ind_H^L θ` is the trivial character** (`θ ≠ 1_H`, `H ⊴ L`).  If
`Ind_H^L θ = ∑_{φ ∈ S} φ` decomposes into irreducibles, then every `φ ∈ S` is nontrivial:
Frobenius reciprocity gives `⟨Ind_H^L θ, 1_L⟩ = ⟨θ, 1_H⟩ = 0` (`θ ≠ 1_H`, orthonormality), so the
count of trivial constituents `|{φ ∈ S : φ = 1_L}|` vanishes.  The `1_L ∉ S` step of the type-I
non-reality bookkeeping. -/
theorem forall_mem_ne_trivial_of_induce_eq_sum
    {H : Subgroup L} [H.Normal] [Invertible (Nat.card ↥H : ℂ)]
    (θ : IrreducibleCharacter ↥H) (hθne : θ ≠ trivialIrreducibleCharacter ↥H)
    {S : Finset (IrreducibleCharacter L)}
    (hsum : ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
      = ∑ φ ∈ S, (φ : ClassFunction L ℂ)) :
    ∀ φ ∈ S, φ ≠ trivialIrreducibleCharacter L := by
  classical
  let : Fintype ↥H := Fintype.ofFinite _
  intro φ hφ hφtriv
  have hrestrict : ClassFunction.restrict H (trivialIrreducibleCharacter L : ClassFunction L ℂ)
      = (trivialIrreducibleCharacter ↥H : ClassFunction ↥H ℂ) := by
    ext x
    simp [IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      trivialClassFunction_apply]
  have hzero : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
      (trivialIrreducibleCharacter L : ClassFunction L ℂ) = 0 := by
    rw [ClassFunction.inner_induce_eq_inner_restrict, hrestrict,
      irreducibleCharacter_inner_eq_ite, if_neg hθne]
  rw [hsum, inner_sum_left] at hzero
  simp_rw [irreducibleCharacter_inner_eq_ite] at hzero
  rw [Finset.sum_boole] at hzero
  have hcard : (S.filter (fun φ' => φ' = trivialIrreducibleCharacter L)).card = 0 := by
    exact_mod_cast hzero
  rw [Finset.card_eq_zero] at hcard
  have hmem : φ ∈ S.filter (fun φ' => φ' = trivialIrreducibleCharacter L) :=
    Finset.mem_filter.mpr ⟨hφ, hφtriv⟩
  rw [hcard] at hmem
  exact absurd hmem (Finset.notMem_empty φ)

/-- **Every constituent of `Ind_H^L θ` is non-real**, for `L` of odd order and `θ ≠ 1_H`
(`H ⊴ L`).  Each constituent is nontrivial (`forall_mem_ne_trivial_of_induce_eq_sum`), and in a
group of odd order a nontrivial irreducible character is non-real (Peterfalvi (1.1),
`not_isReal_of_ne_trivial_of_odd_card'`).  This is the non-reality clause of
`typeI_induced_char_constituents`. -/
theorem forall_mem_not_isReal_of_induce_eq_sum_of_odd
    {H : Subgroup L} [H.Normal] [Invertible (Nat.card ↥H : ℂ)] (hodd : Odd (Nat.card L))
    (θ : IrreducibleCharacter ↥H) (hθne : θ ≠ trivialIrreducibleCharacter ↥H)
    {S : Finset (IrreducibleCharacter L)}
    (hsum : ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
      = ∑ φ ∈ S, (φ : ClassFunction L ℂ)) :
    ∀ φ ∈ S, ¬ ClassFunction.IsReal (φ : ClassFunction L ℂ) :=
  fun φ hφ => not_isReal_of_ne_trivial_of_odd_card' hodd
    (forall_mem_ne_trivial_of_induce_eq_sum θ hθne hsum φ hφ)

/-- **The constituents of `Ind_H^L θ` are conjugate-distinct**, for `L` of odd order and `θ ≠ 1_H`
(`H ⊴ L`): no constituent is the complex conjugate of another, `∀ φ φ' ∈ S, φ̄ ≠ φ'`.

Since `θ̄ ≁_L θ` (`conjBy_ne_conj_of_odd`), `⟨Ind_H^L θ, Ind_H^L θ̄⟩ = 0`
(`inner_induce_eq_zero_of_not_conj`); and `Ind_H^L θ̄ = (Ind_H^L θ)̄ = ∑_{φ∈S} φ̄` (`conj_induce`).
Expanding the pairing by orthonormality, `⟨∑ φ, ∑ φ̄⟩` counts the pairs `(φ, φ') ∈ S × S` with
`φ = φ'̄`; that count being `0` means no such pair exists.  This is the conjugate-distinctness
clause
of `typeI_induced_char_constituents`. -/
theorem forall_mem_conj_ne_of_odd
    {H : Subgroup L} [H.Normal] [Invertible (Nat.card ↥H : ℂ)] (hodd : Odd (Nat.card L))
    (θ : IrreducibleCharacter ↥H) (hθne : θ ≠ trivialIrreducibleCharacter ↥H)
    {S : Finset (IrreducibleCharacter L)}
    (hsum : ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
      = ∑ φ ∈ S, (φ : ClassFunction L ℂ)) :
    ∀ φ ∈ S, ∀ φ' ∈ S, (φ : ClassFunction L ℂ).conj ≠ (φ' : ClassFunction L ℂ) := by
  classical
  let : Fintype ↥H := Fintype.ofFinite _
  -- bundled complex conjugate (transparent `let` so `↑(bar ψ)` reduces to `↑ψ.conj`)
  let bar : IrreducibleCharacter L → IrreducibleCharacter L :=
    fun ψ => ⟨(ψ : ClassFunction L ℂ).conj, ψ.isIrreducible.conj⟩
  let θbar : IrreducibleCharacter ↥H := ⟨(θ : ClassFunction ↥H ℂ).conj, θ.isIrreducible.conj⟩
  have hθneCF : (θ : ClassFunction ↥H ℂ) ≠ trivialClassFunction ↥H :=
    fun h => hθne (Subtype.ext h)
  have hnotconj : ∀ g : L, IrreducibleCharacter.conjBy g θ ≠ θbar := fun g hcontra =>
    conjBy_ne_conj_of_odd hodd θ.isIrreducible hθneCF g
      (by rw [← IrreducibleCharacter.coe_conjBy, hcontra])
  -- `⟨∑ φ, ∑ φ̄⟩ = 0`
  have hconjsum : ∀ T : Finset (IrreducibleCharacter L),
      (∑ φ ∈ T, (φ : ClassFunction L ℂ)).conj = ∑ φ ∈ T, (φ : ClassFunction L ℂ).conj := by
    intro T
    induction T using Finset.induction with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, ClassFunction.conj_add, ih, Finset.sum_insert ha]
  have hIθ : ClassFunction.inner (∑ φ ∈ S, (φ : ClassFunction L ℂ))
      (∑ φ ∈ S, ((bar φ : IrreducibleCharacter L) : ClassFunction L ℂ)) = 0 := by
    have h1 := inner_induce_eq_zero_of_not_conj (H := H) θ θbar hnotconj
    have hbc : (θbar : ClassFunction ↥H ℂ) = (θ : ClassFunction ↥H ℂ).conj := rfl
    rw [hbc, ← conj_induce, hsum, hconjsum S] at h1
    exact h1
  -- the pairing counts pairs `(φ, φ') ∈ S × S` with `φ = bar φ'`; that count is `0`
  have hpair : ((S ×ˢ S).filter (fun p => p.1 = bar p.2)).card = 0 := by
    have hcount : ((( S ×ˢ S).filter (fun p => p.1 = bar p.2)).card : ℂ) = 0 := by
      rw [← hIθ, inner_sum_left]
      simp_rw [inner_sum_right, irreducibleCharacter_inner_eq_ite]
      rw [← Finset.sum_product', Finset.sum_boole]
    exact_mod_cast hcount
  rw [Finset.card_eq_zero] at hpair
  -- conclude: `φ̄ = φ'` would put `(φ', φ)` in the (empty) pair set
  intro φ hφ φ' hφ' hcontra
  have hmem : (φ', φ) ∈ (S ×ˢ S).filter (fun p => p.1 = bar p.2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hφ', hφ⟩, Subtype.ext hcontra.symm⟩
  rw [hpair] at hmem
  exact absurd hmem (Finset.notMem_empty _)

end OddOrder.RepresentationTheory


