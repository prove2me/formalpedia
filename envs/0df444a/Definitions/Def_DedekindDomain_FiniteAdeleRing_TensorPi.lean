-- Prove2me | Definitions.Def_DedekindDomain_FiniteAdeleRing_TensorPi
-- name    : DedekindDomain_FiniteAdeleRing_TensorPi
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/531b2971-86ef-5c1a-925a-b7efb5b16874
-- title:
--   Tensor product of a finitely presented module with a product
-- statement:
--   Throughout, $R$ is a commutative ring, $M$ an $R$-module and $(N_i)_{i\in\iota}$ an arbitrary family of $R$-modules. The module constructs the canonical comparison map $M\otimes_R\prod_i N_i\to\prod_i (M\otimes_R N_i)$ as an $R$-linear equivalence, first for $M$ finite and free, then for $M$ finitely presented.
--
--   The auxiliary pieces are: [`Module.FinitePresentation.exists_fin_exact`](../def/DedekindDomain_FiniteAdeleRing_TensorPi.html#L8), which turns a finite presentation of $M$ into data $n,m\in\mathbb N$ and maps $f\colon R^m\to R^n$, $g\colon R^n\to M$ with $f,g$ exact and $g$ surjective, i.e. a presentation $R^m\to R^n\to M\to 0$; [`directSumPi_equiv_piSum`](../def/DedekindDomain_FiniteAdeleRing_TensorPi.html#L35), which for a finite index type $\iota'$ and a doubly indexed family $N_{i,i'}$ gives $\bigoplus_{i'}\prod_i N_{i,i'}\cong\prod_i\bigoplus_{i'}N_{i,i'}$, sending $x$ to $i\mapsto\sum_{i'}\iota_{i'}(x_{i'}(i))$; and [`freeModule_tensorPiEquiv`](../def/DedekindDomain_FiniteAdeleRing_TensorPi.html#L78), [`finsuppLeft_TensorPi_equiv_piTensor`](../def/DedekindDomain_FiniteAdeleRing_TensorPi.html#L82), [`tensorPiEquiv_finitefreeModule`](../def/DedekindDomain_FiniteAdeleRing_TensorPi.html#L95), which respectively replace $M$ by $\mathrm{ChooseBasisIndex}(M)\to_{0}R$ along the chosen basis, establish the comparison for a finitely supported free module on a finite basis index (by passing between $\mathrm{Finsupp}$, direct sums and products), and transport back along the basis. Their composite is [`tensorPi_equiv_piTensor`](../def/DedekindDomain_FiniteAdeleRing_TensorPi.html#L100), for $M$ finite and free, and [`tensorPi_equiv_piTensor_apply`](../def/DedekindDomain_FiniteAdeleRing_TensorPi.html#L109) records that it sends $m\otimes n$ to $i\mapsto m\otimes n_i$.
--
--   For $M$ merely finitely presented, [`piRightHomBil'`](../def/DedekindDomain_FiniteAdeleRing_TensorPi.html#L146) is the $R$-bilinear map $m\mapsto(n\mapsto(i\mapsto m\otimes n_i))$, and [`tensorPi_equiv_piTensor'`](../def/DedekindDomain_FiniteAdeleRing_TensorPi.html#L154) is the equivalence $M\otimes_R\prod_i N_i\cong\prod_i(M\otimes_R N_i)$ obtained by proving that this bilinear map exhibits $\prod_i(M\otimes_R N_i)$ as the tensor product; the proof compares a chosen presentation $R^m\to R^n\to M\to 0$ with the free case by a five-lemma argument, using right-exactness of $-\otimes_R\prod_i N_i$ and of each $-\otimes_R N_i$. Again [`tensorPi_equiv_piTensor'_apply`](../def/DedekindDomain_FiniteAdeleRing_TensorPi.html#L227) gives $m\otimes n\mapsto(i\mapsto m\otimes n_i)$.
--
--   **Relation to Mathlib.** [`Module.FinitePresentation.exists_fin_exact`](../def/DedekindDomain_FiniteAdeleRing_TensorPi.html#L8) refines Mathlib's `Module.FinitePresentation.exists_fin` into the shape of an exact sequence $R^m\to R^n\to M\to 0$. The resulting equivalences show that Mathlib's canonical map `TensorProduct.piRightHom` is bijective for an arbitrary index type once $M$ is finitely presented (Mathlib's corresponding equivalence is for a finite index type).
--
--   **Where it is used.** The commutation of tensor products with arbitrary products is what allows a finitely presented module to be base changed along products, and hence restricted products, over the finite places of a number field; this underlies the treatment of the finite adèle ring and of adelic base change in the project.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/DedekindDomain/FiniteAdeleRing/TensorPi.lean` — © 2025 Madison Crim; authors: Madison Crim). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_DedekindDomain_FiniteAdeleRing_TensorPi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section
open DirectSum Function

section

theorem Module.FinitePresentation.exists_fin_exact (R : Type*) (M : Type*)
  [Ring R] [AddCommGroup M] [Module R M] [fp : Module.FinitePresentation R M] :
  ∃ (n m : ℕ) (f : (Fin m → R) →ₗ[R] (Fin n → R)) (g : (Fin n → R) →ₗ[R] M),
    Exact f g ∧ Surjective g := by
  obtain ⟨n, K, iso, S, hS⟩ := Module.FinitePresentation.exists_fin R M
  let m := S.card
  let gens : Fin m → (Fin n → R) := Subtype.val ∘ (Finset.equivFin S).symm
  let f : (Fin m → R) →ₗ[R] (Fin n → R) := Fintype.linearCombination R gens
  let g : (Fin n → R) →ₗ[R] M := iso.symm.toLinearMap.comp (Submodule.mkQ K)
  have h₁ : LinearMap.range f = K := by
    simp only [← hS, f, Fintype.range_linearCombination, gens, (Surjective.range_comp
    (Finset.equivFin S).symm.surjective Subtype.val), Subtype.range_val_subtype, Finset.setOf_mem]
  have h₂ : LinearMap.ker g = K := by
    simp only [g, LinearEquiv.ker_comp, Submodule.ker_mkQ]
  have exact_fg : Exact f g := LinearMap.exact_iff.mpr (h₂.trans h₁.symm)
  have : Surjective g := by
    simp only [g, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_surjective,
      Submodule.mkQ_surjective]
  exact ⟨n, m, f, g, exact_fg, this⟩
end

section

variable {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {R ι : Type*} [Semiring R]
  {M N : ι → ι' → Type*} [∀ i i', AddCommMonoid (M i i')] [∀ i i', AddCommMonoid (N i i')]
  [∀ i i', Module R (M i i')] [∀ i i', Module R (N i i')]

def directSumPi_equiv_piSum : (⨁ (i' : ι'), (∀ i, N i i')) ≃ₗ[R] (∀ i, (⨁ i', N i i')) where
  toFun nm i := ∑ i', DirectSum.of (fun i' ↦ N i i') i' (nm i' i)
  map_add' x y := by
    simp only [DirectSum.add_apply, Pi.add_apply, map_add]
    ext i
    simp [Finset.sum_add_distrib]
  map_smul' r nm := by
    ext i
    simp only [RingHom.id_apply, Pi.smul_apply]
    rw [Finset.smul_sum, Finset.sum_congr rfl]
    intro i' _
    rw [← DirectSum.of_smul]
    rfl
  invFun nm :=  ∑ i', DirectSum.of (fun j ↦ ∀ i, N i j) i' (fun i ↦ nm i i')
  left_inv nm := by
    simp only
    convert sum_univ_of (x := nm) with j _ i
    conv_rhs => rw [← DirectSum.sum_univ_of nm]
    simp only [DirectSum.sum_apply, Finset.sum_apply]
    congr with k
    obtain rfl | h := eq_or_ne j k
    · simp
    · simp [of_eq_of_ne _ _ _ h]
  right_inv nm := by
    simp only
    refine funext (fun i ↦ ?_)
    convert sum_univ_of (x := nm i) with j _ i
    conv_rhs => rw [← DirectSum.sum_univ_of (nm i)]
    simp only [DirectSum.sum_apply, Finset.sum_apply]
    congr with k
    obtain rfl | h := eq_or_ne j k
    · simp
    · simp [of_eq_of_ne _ _ _ h]

end

section

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M] {ι : Type*} (N : ι → Type*) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

open TensorProduct

noncomputable def freeModule_tensorPiEquiv :
    M ⊗[R] (∀ i, N i) ≃ₗ[R] (Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] (∀ i, N i) :=
  TensorProduct.congr (Module.Free.chooseBasis R M).repr (LinearEquiv.refl R ((i : ι) → N i))

noncomputable def finsuppLeft_TensorPi_equiv_piTensor (B : Type*) [Fintype B] [DecidableEq B] :
    (B →₀ R) ⊗[R] (Π i, N i) ≃ₗ[R] Π i, (B →₀ R) ⊗[R] (N i) :=

  finsuppScalarLeft R (∀i, N i) B ≪≫ₗ

    (finsuppLEquivDirectSum R (∀i, N i) B) ≪≫ₗ

    directSumPi_equiv_piSum  ≪≫ₗ

    LinearEquiv.piCongrRight (fun i ↦(finsuppLEquivDirectSum R (N i) B).symm) ≪≫ₗ

    LinearEquiv.piCongrRight (fun i ↦ (finsuppScalarLeft R (N i) B).symm)

noncomputable def tensorPiEquiv_finitefreeModule :
    (Π i, (Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] N i) ≃ₗ[R] Π i, (M ⊗[R] N i) :=
  LinearEquiv.piCongrRight
    (fun i ↦ (LinearEquiv.rTensor (N i) (Module.Free.chooseBasis R M).repr.symm))

noncomputable def tensorPi_equiv_piTensor :
    M ⊗[R] (Π i, N i) ≃ₗ[R] Π i, (M ⊗[R] N i) :=

  (freeModule_tensorPiEquiv R M N) ≪≫ₗ

    (finsuppLeft_TensorPi_equiv_piTensor R N _) ≪≫ₗ

    (tensorPiEquiv_finitefreeModule R M N)

lemma tensorPi_equiv_piTensor_apply (m : M) (n : ∀ i, N i) :
    tensorPi_equiv_piTensor R M N (m ⊗ₜ n) = fun i ↦ (m ⊗ₜ n i) := by
  unfold tensorPi_equiv_piTensor
  simp only [freeModule_tensorPiEquiv, LinearEquiv.trans_apply, congr_tmul,
    LinearEquiv.refl_apply]
  let m' := (Module.Free.chooseBasis R M).repr m
  have hm' : (Module.Free.chooseBasis R M).repr.symm m' = m := by simp [m']
  rw [← hm', LinearEquiv.apply_symm_apply]
  induction m' using Finsupp.induction_linear
  · ext
    simp
  · ext i
    simp_all [add_tmul]
  · rw [← LinearEquiv.eq_symm_apply]
    simp only [tensorPiEquiv_finitefreeModule, LinearEquiv.piCongrRight_symm]
    ext i
    simp only [LinearEquiv.piCongrRight_apply, LinearEquiv.rTensor_symm_tmul, LinearEquiv.symm_symm,
      LinearEquiv.apply_symm_apply, finsuppLeft_TensorPi_equiv_piTensor, LinearEquiv.trans_apply]
    rw [LinearEquiv.symm_apply_eq, finsuppScalarLeft_apply_tmul, Finsupp.sum_single_index (by simp),
      LinearEquiv.symm_apply_eq, finsuppLEquivDirectSum_single, finsuppScalarLeft_apply_tmul,
      Finsupp.sum_single_index (by simp), finsuppLEquivDirectSum_single, directSumPi_equiv_piSum,
      ← LinearEquiv.toFun_eq_coe]
    ext k
    simp only [DirectSum.lof_eq_of R, of_apply, eq_rec_constant, dite_eq_ite, DirectSum.sum_apply,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [ite_apply, Pi.zero_apply, Pi.smul_apply]

end

section

open TensorProduct

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [h : Module.FinitePresentation R M] {ι : Type*} (N : ι → Type*) [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)]

private noncomputable def piRightHomBil' : M →ₗ[R] (∀ i, N i) →ₗ[R] ∀ i, M ⊗[R] N i where
  toFun m := LinearMap.pi (fun i ↦ TensorProduct.mk R M (N i) m ∘ₗ LinearMap.proj i)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := rfl

@[simp] private lemma piRightHomBil'_apply (m : M) (n : ∀ i, N i) :
    piRightHomBil' R M N m n = fun i ↦ m ⊗ₜ n i := rfl

noncomputable def tensorPi_equiv_piTensor' [Module.FinitePresentation R M] :
    M ⊗[R] (Π i, N i) ≃ₗ[R] Π i, (M ⊗[R] N i) := IsTensorProduct.equiv
    (f := piRightHomBil' R M N) <| by
  obtain ⟨n, m, f, g, exact, surj⟩ := Module.FinitePresentation.exists_fin_exact R M
  set i₁ : (Fin m → R) ⊗[R] (Π i, N i) →ₗ[R] Π i, ((Fin m → R) ⊗[R] N i) :=
    (tensorPi_equiv_piTensor R (Fin m → R) N).toLinearMap
  set i₂ : (Fin n → R) ⊗[R] (Π i, N i) →ₗ[R] Π i, ((Fin n → R) ⊗[R] N i) :=
    (tensorPi_equiv_piTensor R (Fin n → R) N).toLinearMap
  set i₃ : M ⊗[R] (Π i, N i) →ₗ[R] Π i, (M ⊗[R] N i) := TensorProduct.piRightHom R R M N
  set i₄ : (PUnit : Type) →ₗ[R] (PUnit : Type) := LinearMap.id
  set i₅ : (PUnit : Type)  →ₗ[R] (PUnit : Type)  := LinearMap.id
  set f₁ : (Fin m → R) ⊗[R] (Π i, N i) →ₗ[R] (Fin n → R) ⊗[R] (Π i, N i) := f.rTensor (Π i, N i)
  set f₂ : (Fin n → R) ⊗[R] (Π i, N i) →ₗ[R] M ⊗[R] (Π i, N i) := g.rTensor (Π i, N i)
  set f₃ : M ⊗[R] (Π i, N i) →ₗ[R] (PUnit : Type) := 0
  set f₄ : (PUnit : Type) →ₗ[R] (PUnit : Type) := LinearMap.id
  set g₁ : (Π i, ((Fin m → R) ⊗[R] N i)) →ₗ[R] Π i, ((Fin n → R) ⊗[R] N i) :=
    LinearMap.pi (fun i ↦ (LinearMap.rTensor (N i) f)  ∘ₗ LinearMap.proj i)
  set g₂ : (Π i, ((Fin n → R) ⊗[R] N i)) →ₗ[R] Π i, (M ⊗[R] N i) :=
    LinearMap.pi (fun i ↦ (LinearMap.rTensor (N i) g)  ∘ₗ LinearMap.proj i)
  set g₃ : (Π i, (M ⊗[R] N i)) →ₗ[R] (PUnit : Type) := 0
  set g₄ : (PUnit : Type) →ₗ[R] (PUnit : Type) := LinearMap.id
  have hc₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁ := by
    refine ext' fun x y ↦ ?_
    simp only [LinearMap.coe_comp, comp_apply, i₂, i₁, g₁, LinearEquiv.coe_coe]
    rw [LinearMap.rTensor_tmul, tensorPi_equiv_piTensor_apply, tensorPi_equiv_piTensor_apply]
    ext i
    simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply,
      LinearMap.rTensor_tmul]
  have hc₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂ := by
    refine ext' fun x y ↦ ?_
    simp only [LinearMap.coe_comp, comp_apply, i₂, g₂, i₃]
    rw [LinearMap.rTensor_tmul, piRightHom_tmul]
    ext i
    simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply,
      LinearEquiv.coe_coe]
    rw [tensorPi_equiv_piTensor_apply, LinearMap.rTensor_tmul]
  have hc₃ : g₃ ∘ₗ i₃ = i₄ ∘ₗ f₃ := rfl
  have hc₄ : g₄ ∘ₗ i₄ = i₅ ∘ₗ f₄ := rfl
  have hf₁ : Function.Exact f₁ f₂ := rTensor_exact ((i : ι) → N i) exact surj
  have hf₂ : Function.Exact f₂ f₃ :=
    (LinearMap.exact_zero_iff_surjective _ _).mpr (LinearMap.rTensor_surjective _ surj)
  have hf₃ : Function.Exact f₃ f₄ :=
    (LinearMap.exact_zero_iff_injective _ LinearMap.id).mpr fun ⦃a₁ a₂⦄ ↦ congrFun rfl
  have hg₁ : Function.Exact g₁ g₂ := by
    intro y
    rw [Set.mem_range]
    have (i : ι) : Exact (LinearMap.rTensor (N i) f) (LinearMap.rTensor (N i) g) :=
      rTensor_exact (N i) exact surj
    constructor
    · intro h
      refine ⟨fun i ↦ Classical.choose
        (Set.mem_range.mp (((this i) (y i)).mp (congr_fun h i))), funext (fun i ↦ ?_)⟩
      exact (Classical.choose_spec (Set.mem_range.mp (((this i) (y i)).mp (congr_fun h i))))
    · intro h
      ext i
      obtain ⟨y₁, hy₁⟩ := h
      exact ((this i) (y i)).mpr (LinearMap.mem_range.mpr ⟨y₁ i, congr_fun hy₁ i⟩)
  have hg₂ : Function.Exact g₂ g₃ := by
    apply (LinearMap.exact_zero_iff_surjective _ g₂).mpr
    refine fun y ↦ ⟨fun i ↦
        Classical.choose (LinearMap.rTensor_surjective (N i) surj (y i)), funext fun i ↦ ?_⟩
    exact Classical.choose_spec (LinearMap.rTensor_surjective (N i) surj (y i))
  have hg₃ : Function.Exact g₃ g₄ :=
    (LinearMap.exact_zero_iff_injective _ LinearMap.id).mpr fun ⦃a₁ a₂⦄ ↦ congrFun rfl
  have hi₁ : Function.Surjective i₁ := (tensorPi_equiv_piTensor R (Fin m → R) N).surjective
  have hi₂ : Function.Bijective i₂ := ((tensorPi_equiv_piTensor R (Fin n → R) N)).bijective
  have hi₄ : Function.Bijective i₄ := Function.bijective_id
  have hi₅ : Function.Injective i₅ := Function.injective_id
  have := LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄ i₁ i₂ i₃ i₄ i₅
    hc₁ hc₂ hc₃ hc₄ hf₁ hf₂ hf₃ hg₁ hg₂ hg₃ hi₁ hi₂ hi₄ hi₅
  exact this

lemma tensorPi_equiv_piTensor'_apply (m : M) (n : ∀ i, N i) :
    tensorPi_equiv_piTensor' R M N (m ⊗ₜ n) = fun i ↦ (m ⊗ₜ n i) := rfl

end


