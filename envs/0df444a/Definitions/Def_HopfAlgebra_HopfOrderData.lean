-- Prove2me | Definitions.Def_HopfAlgebra_HopfOrderData
-- name    : HopfAlgebra_HopfOrderData
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/91b64930-7acb-515e-ba5c-7382e0a16897
-- title:
--   Descending Hopf algebra structure to a subalgebra order
-- statement:
--   Throughout, $R$ is a commutative ring with a $K$-algebra $A$ in a scalar tower $R \to K \to A$, and $S \subseteq A$ is an $R$-subalgebra. The comparison maps are `tensorSqHom S`, the $R$-algebra map $S \otimes_R S \to A \otimes_K A$ sending $t \otimes t'$ to $t \otimes t'$ (built as the product of the two inclusions $S \to A \to A \otimes_K A$), and `baseChangeHom S`, the $K$-algebra map $K \otimes_R S \to A$ with $k \otimes t \mapsto k\,t$; `doubleEval`, `tripleEval`, `tripleEvalL` and `baseChangeSq` are the corresponding maps on $K \otimes_R (S^{\otimes 2})$, on the two bracketings of $K \otimes_R (S^{\otimes 3})$ and on $(K \otimes_K K) \otimes_R (S \otimes_R S)$, with `doubleCmp`, `tripleCmpR`, `tripleCmpL` their restrictions along $z \mapsto 1 \otimes z$; `range_tensorSqHom_mono`, `doubleCmp_eq_tensorSqHom` and `tripleCmpR_assoc` record monotonicity in $S$, agreement of the two descriptions, and compatibility with the associator. For $R$ a domain with $K$ its fraction field these maps are injective (`baseChangeHom_injective`, and, when $S$ is flat over $R$, `tensorSqHom_injective`, `tripleCmpR_injective`), and $K\,S = A$ gives the isomorphism `baseChangeEquiv` $K \otimes_R S \cong A$.
--
--   Given a Hopf algebra structure on $A$ over $K$ and the three clauses $\Delta(S) \subseteq \operatorname{im}(\mathrm{tensorSqHom}\,S)$, $\varepsilon(S) \subseteq \operatorname{im}(R \to K)$, $\sigma(S) \subseteq S$ — each passed as a separate hypothesis, not bundled into a predicate — the unique $R$-linear lifts `comulS`, `counitS`, `antipodeS` are defined by those equations, characterised by `comulS_eq_iff`, `algebraMap_counitS`, `coe_antipodeS`; the coassociativity, counit, multiplicativity and antipode axioms are proved by injectivity of the comparison maps, and assembled into the reducible definitions `coalgebra`, `bialgebra`, `hopfAlgebra` of $R$-structures on $S$ (no instances being registered). Further declarations give the compatibility squares `val_comul`, `val_counit`, `val_antipode`, the generic-fibre bialgebra isomorphism `baseChangeBialgEquiv` $K \otimes_R S \cong A$, functoriality (`mapBialgHom` along a $K$-bialgebra map carrying $S$ into $T$, its special case `toMap` for the image subalgebra, and `inclusion` for $S \le S'$, each computed on underlying elements), and, over a principal ideal domain, freeness and flatness of a module-finite $S$ together with the wrappers `coalgebraOfFinite`, `bialgebraOfFinite`, `hopfAlgebraOfFinite`, `baseChangeBialgEquivOfFinite`.
--
--   **Relation to Mathlib.** Uses Mathlib's `Coalgebra`, `Bialgebra`, `HopfAlgebra`, `BialgHom`, `BialgEquiv` and tensor-product API; Mathlib has no notion of a Hopf order or of descent of a Hopf structure to a subalgebra, and this descent machinery is the project's own.
--
--   **Where it is used.** Finite flat group schemes over a ring of integers are the spectra of Hopf algebras over that ring whose generic fibre is a given Hopf algebra over the fraction field; this module supplies the descent of comultiplication, counit and antipode to such a subalgebra, together with the identification of the generic fibre, for use in the group-scheme side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HopfAlgebra_HopfOrderData.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000

universe u v w w'

open scoped TensorProduct

namespace HopfOrder

section Comparison

variable {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
variable {A : Type w} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
variable (S : Subalgebra R A)

noncomputable def tensorSqHom : (↥S ⊗[R] ↥S) →ₐ[R] (A ⊗[K] A) :=
  Algebra.TensorProduct.productMap
    (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
    (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)

@[simp]
lemma tensorSqHom_tmul (t t' : ↥S) :
    tensorSqHom S (t ⊗ₜ[R] t') = (t : A) ⊗ₜ[K] (t' : A) := by
  simp [tensorSqHom, Algebra.TensorProduct.productMap_apply_tmul,
    Algebra.TensorProduct.tmul_mul_tmul]

variable {S} in
lemma tmul_mem_range_tensorSqHom {x y : A} (hx : x ∈ S) (hy : y ∈ S) :
    x ⊗ₜ[K] y ∈ (tensorSqHom (K := K) S).range :=
  ((tensorSqHom S).mem_range).mpr ⟨(⟨x, hx⟩ : ↥S) ⊗ₜ[R] (⟨y, hy⟩ : ↥S), by rw [tensorSqHom_tmul]⟩

omit S in
lemma range_tensorSqHom_mono {S S' : Subalgebra R A} (h : S ≤ S') :
    (tensorSqHom (K := K) S).range ≤ (tensorSqHom (K := K) S').range := by
  rintro w hw
  obtain ⟨z, rfl⟩ := ((tensorSqHom (K := K) S).mem_range).mp hw
  clear hw
  induction z with
  | zero => rw [map_zero]; exact Subalgebra.zero_mem _
  | tmul t t' =>
      rw [tensorSqHom_tmul]
      exact tmul_mem_range_tensorSqHom (h t.2) (h t'.2)
  | add z₁ z₂ h₁ h₂ => rw [map_add]; exact Subalgebra.add_mem _ h₁ h₂

noncomputable def baseChangeHom : (K ⊗[R] ↥S) →ₐ[K] A :=
  AlgHom.liftEquiv R K (↥S) A S.val

@[simp]
lemma baseChangeHom_tmul (k : K) (t : ↥S) : baseChangeHom S (k ⊗ₜ[R] t) = k • (t : A) := rfl

lemma baseChangeHom_one_tmul (t : ↥S) : baseChangeHom S ((1 : K) ⊗ₜ[R] t) = (t : A) := by
  rw [baseChangeHom_tmul, one_smul]

theorem baseChangeHom_surjective (hspan : Submodule.span K (S : Set A) = ⊤) :
    Function.Surjective (baseChangeHom (K := K) S) := by
  intro y
  have hle : Submodule.span K (S : Set A) ≤
      Subalgebra.toSubmodule (baseChangeHom (K := K) S).range := by
    rw [Submodule.span_le]
    intro x hx
    simp only [SetLike.mem_coe, Subalgebra.mem_toSubmodule]
    exact ((baseChangeHom (K := K) S).mem_range).mpr
      ⟨(1 : K) ⊗ₜ[R] (⟨x, hx⟩ : ↥S), baseChangeHom_one_tmul S ⟨x, hx⟩⟩
  have hy : y ∈ Subalgebra.toSubmodule (baseChangeHom (K := K) S).range := by
    apply hle
    rw [hspan]
    exact Submodule.mem_top
  exact ((baseChangeHom (K := K) S).mem_range).mp hy

noncomputable def doubleEval : (K ⊗[R] (↥S ⊗[R] ↥S)) →ₗ[K] (A ⊗[K] A) :=
  (TensorProduct.map (baseChangeHom S).toLinearMap (baseChangeHom S).toLinearMap).comp
    (TensorProduct.AlgebraTensorModule.distribBaseChange R K ↥S ↥S).toLinearMap

noncomputable def doubleCmp (z : ↥S ⊗[R] ↥S) : A ⊗[K] A :=
  doubleEval S ((1 : K) ⊗ₜ[R] z)

@[simp]
lemma doubleCmp_tmul (t t' : ↥S) :
    doubleCmp S (t ⊗ₜ[R] t') = (t : A) ⊗ₜ[K] (t' : A) := by
  simp only [doubleCmp, doubleEval, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply]
  rw [baseChangeHom_one_tmul, baseChangeHom_one_tmul]

lemma doubleCmp_zero : doubleCmp (K := K) S 0 = 0 := by
  show doubleEval S ((1 : K) ⊗ₜ[R] (0 : ↥S ⊗[R] ↥S)) = 0
  rw [TensorProduct.tmul_zero, map_zero]

lemma doubleCmp_add (z w : ↥S ⊗[R] ↥S) :
    doubleCmp (K := K) S (z + w) = doubleCmp (K := K) S z + doubleCmp (K := K) S w := by
  show doubleEval S ((1 : K) ⊗ₜ[R] (z + w))
    = doubleEval S ((1 : K) ⊗ₜ[R] z) + doubleEval S ((1 : K) ⊗ₜ[R] w)
  rw [TensorProduct.tmul_add, map_add]

lemma doubleCmp_smul (r : R) (z : ↥S ⊗[R] ↥S) :
    doubleCmp (K := K) S (r • z) = (algebraMap R K r) • doubleCmp (K := K) S z := by
  show doubleEval S ((1 : K) ⊗ₜ[R] (r • z))
    = (algebraMap R K r) • doubleEval S ((1 : K) ⊗ₜ[R] z)
  rw [TensorProduct.tmul_smul,
    ← algebraMap_smul K r ((1 : K) ⊗ₜ[R] z : K ⊗[R] (↥S ⊗[R] ↥S)), map_smul]

theorem doubleCmp_eq_tensorSqHom (z : ↥S ⊗[R] ↥S) :
    doubleCmp (K := K) S z = tensorSqHom (K := K) S z := by
  induction z with
  | zero => rw [doubleCmp_zero, map_zero]
  | tmul t t' => rw [doubleCmp_tmul, tensorSqHom_tmul]
  | add z w hz hw => rw [doubleCmp_add, map_add, hz, hw]

noncomputable def tripleEval :
    (K ⊗[R] (↥S ⊗[R] (↥S ⊗[R] ↥S))) →ₗ[K] (A ⊗[K] (A ⊗[K] A)) :=
  (TensorProduct.map (baseChangeHom S).toLinearMap (doubleEval S)).comp
    (TensorProduct.AlgebraTensorModule.distribBaseChange R K ↥S (↥S ⊗[R] ↥S)).toLinearMap

noncomputable def tripleCmpR (w : ↥S ⊗[R] (↥S ⊗[R] ↥S)) : A ⊗[K] (A ⊗[K] A) :=
  tripleEval S ((1 : K) ⊗ₜ[R] w)

lemma tripleCmpR_zero : tripleCmpR (K := K) S 0 = 0 := by
  show tripleEval S ((1 : K) ⊗ₜ[R] (0 : ↥S ⊗[R] (↥S ⊗[R] ↥S))) = 0
  rw [TensorProduct.tmul_zero, map_zero]

lemma tripleCmpR_add (w w' : ↥S ⊗[R] (↥S ⊗[R] ↥S)) :
    tripleCmpR (K := K) S (w + w') = tripleCmpR (K := K) S w + tripleCmpR (K := K) S w' := by
  show tripleEval S ((1 : K) ⊗ₜ[R] (w + w'))
    = tripleEval S ((1 : K) ⊗ₜ[R] w) + tripleEval S ((1 : K) ⊗ₜ[R] w')
  rw [TensorProduct.tmul_add, map_add]

lemma tripleCmpR_tmul (t : ↥S) (z : ↥S ⊗[R] ↥S) :
    tripleCmpR S (t ⊗ₜ[R] z) = (t : A) ⊗ₜ[K] doubleCmp S z := by
  simp only [tripleCmpR, tripleEval, doubleCmp, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply]
  rw [baseChangeHom_one_tmul]

noncomputable def tripleEvalL :
    (K ⊗[R] ((↥S ⊗[R] ↥S) ⊗[R] ↥S)) →ₗ[K] ((A ⊗[K] A) ⊗[K] A) :=
  (TensorProduct.map (doubleEval S) (baseChangeHom S).toLinearMap).comp
    (TensorProduct.AlgebraTensorModule.distribBaseChange R K (↥S ⊗[R] ↥S) ↥S).toLinearMap

noncomputable def tripleCmpL (w : (↥S ⊗[R] ↥S) ⊗[R] ↥S) : (A ⊗[K] A) ⊗[K] A :=
  tripleEvalL S ((1 : K) ⊗ₜ[R] w)

lemma tripleCmpL_zero : tripleCmpL (K := K) S 0 = 0 := by
  show tripleEvalL S ((1 : K) ⊗ₜ[R] (0 : (↥S ⊗[R] ↥S) ⊗[R] ↥S)) = 0
  rw [TensorProduct.tmul_zero, map_zero]

lemma tripleCmpL_add (w w' : (↥S ⊗[R] ↥S) ⊗[R] ↥S) :
    tripleCmpL (K := K) S (w + w') = tripleCmpL (K := K) S w + tripleCmpL (K := K) S w' := by
  show tripleEvalL S ((1 : K) ⊗ₜ[R] (w + w'))
    = tripleEvalL S ((1 : K) ⊗ₜ[R] w) + tripleEvalL S ((1 : K) ⊗ₜ[R] w')
  rw [TensorProduct.tmul_add, map_add]

lemma tripleCmpL_tmul (z : ↥S ⊗[R] ↥S) (t : ↥S) :
    tripleCmpL S (z ⊗ₜ[R] t) = doubleCmp S z ⊗ₜ[K] (t : A) := by
  simp only [tripleCmpL, tripleEvalL, doubleCmp, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply]
  rw [baseChangeHom_one_tmul]

lemma tripleCmpR_assoc_tmul (z : ↥S ⊗[R] ↥S) (c : ↥S) :
    tripleCmpR S (TensorProduct.assoc R ↥S ↥S ↥S (z ⊗ₜ[R] c))
      = TensorProduct.assoc K A A A (tripleCmpL S (z ⊗ₜ[R] c)) := by
  induction z with
  | zero =>
      rw [TensorProduct.zero_tmul, map_zero, tripleCmpR_zero, tripleCmpL_zero, map_zero]
  | tmul a b =>
      rw [TensorProduct.assoc_tmul, tripleCmpR_tmul, doubleCmp_tmul, tripleCmpL_tmul,
        doubleCmp_tmul, TensorProduct.assoc_tmul]
  | add z₁ z₂ h₁ h₂ =>
      rw [TensorProduct.add_tmul, map_add, tripleCmpR_add, h₁, h₂, tripleCmpL_add, map_add]

lemma tripleCmpR_assoc (w : (↥S ⊗[R] ↥S) ⊗[R] ↥S) :
    tripleCmpR S (TensorProduct.assoc R ↥S ↥S ↥S w)
      = TensorProduct.assoc K A A A (tripleCmpL S w) := by
  induction w with
  | zero => rw [map_zero, tripleCmpR_zero, tripleCmpL_zero, map_zero]
  | tmul z c => exact tripleCmpR_assoc_tmul S z c
  | add w₁ w₂ h₁ h₂ =>
      rw [map_add, tripleCmpR_add, h₁, h₂, tripleCmpL_add, map_add]

noncomputable def baseChangeSq : ((K ⊗[K] K) ⊗[R] (↥S ⊗[R] ↥S)) →ₗ[K] (A ⊗[K] A) :=
  (TensorProduct.map (baseChangeHom S).toLinearMap (baseChangeHom S).toLinearMap).comp
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R K R K K K ↥S ↥S).toLinearMap

lemma baseChangeSq_apply (x : (K ⊗[K] K) ⊗[R] (↥S ⊗[R] ↥S)) :
    baseChangeSq S x = TensorProduct.map (baseChangeHom S).toLinearMap (baseChangeHom S).toLinearMap
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R K R K K K ↥S ↥S x) := rfl

lemma baseChangeSq_one_tmul (z : ↥S ⊗[R] ↥S) :
    baseChangeSq S (((1 : K) ⊗ₜ[K] (1 : K)) ⊗ₜ[R] z) = tensorSqHom S z := by
  induction z with
  | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
  | tmul a b =>
      simp only [baseChangeSq, LinearMap.comp_apply, LinearEquiv.coe_coe,
        TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
        AlgHom.toLinearMap_apply, baseChangeHom_one_tmul, tensorSqHom_tmul]
  | add z₁ z₂ h₁ h₂ => rw [TensorProduct.tmul_add, map_add, map_add, h₁, h₂]

section Domain

variable [IsDomain R] [IsFractionRing R K]

omit S in

theorem exists_nonzero_smul_eq_one_tmul {M : Type*} [AddCommGroup M] [Module R M]
    (x : K ⊗[R] M) :
    ∃ (r : R) (m : M), r ≠ 0 ∧ (algebraMap R K r) • x = (1 : K) ⊗ₜ[R] m := by
  induction x with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul f g =>
      obtain ⟨p, hs⟩ := IsLocalization.surj (nonZeroDivisors R) f
      refine ⟨p.2, p.1 • g, nonZeroDivisors.coe_ne_zero p.2, ?_⟩
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_comm, hs, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
      obtain ⟨r₁, g₁, h₁, e₁⟩ := hx
      obtain ⟨r₂, g₂, h₂, e₂⟩ := hy
      refine ⟨r₁ * r₂, r₂ • g₁ + r₁ • g₂, mul_ne_zero h₁ h₂, ?_⟩
      have hx' : (algebraMap R K (r₁ * r₂)) • x = (1 : K) ⊗ₜ[R] (r₂ • g₁) := by
        rw [map_mul, mul_comm, mul_smul, e₁, TensorProduct.tmul_smul, algebraMap_smul]
      have hy' : (algebraMap R K (r₁ * r₂)) • y = (1 : K) ⊗ₜ[R] (r₁ • g₂) := by
        rw [map_mul, mul_smul, e₂, TensorProduct.tmul_smul, algebraMap_smul]
      rw [smul_add, hx', hy', ← TensorProduct.tmul_add]

omit S [IsDomain R] in

theorem one_tmul_injective {M : Type*} [AddCommGroup M] [Module R M] [Module.Flat R M] :
    Function.Injective (fun m : M => (1 : K) ⊗ₜ[R] m) := by
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hfact : (fun m : M => (1 : K) ⊗ₜ[R] m) =
      (LinearMap.rTensor M (Algebra.linearMap R K)) ∘ (TensorProduct.lid R M).symm := by
    ext m; simp [TensorProduct.lid_symm_apply, Algebra.linearMap_apply]
  rw [hfact]
  exact (Module.Flat.rTensor_preserves_injective_linearMap _ hRK).comp
    (TensorProduct.lid R M).symm.injective

theorem baseChangeHom_injective : Function.Injective (baseChangeHom (K := K) S) := by
  have key : ∀ z : K ⊗[R] ↥S, baseChangeHom S z = 0 → z = 0 := by
    intro z hz
    obtain ⟨r, h, hr, e⟩ := exists_nonzero_smul_eq_one_tmul (R := R) (K := K) z
    have hru : (algebraMap R K r) ≠ 0 := fun hc =>
      hr (IsFractionRing.injective R K (by rw [hc, map_zero]))
    have h1 : baseChangeHom S ((algebraMap R K r) • z) = 0 := by
      rw [map_smul, hz, smul_zero]
    rw [e, baseChangeHom_one_tmul] at h1
    have h2 : h = 0 := Subtype.ext h1
    rw [h2, TensorProduct.tmul_zero] at e
    have h3 := congrArg (fun w => (algebraMap R K r)⁻¹ • w) e
    simpa only [smul_smul, inv_mul_cancel₀ hru, one_smul, smul_zero] using h3
  intro x y hxy
  have hsub : baseChangeHom S (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (key _ hsub)

noncomputable def baseChangeEquiv (hspan : Submodule.span K (S : Set A) = ⊤) :
    (K ⊗[R] ↥S) ≃ₐ[K] A :=
  AlgEquiv.ofBijective (baseChangeHom S)
    ⟨baseChangeHom_injective S, baseChangeHom_surjective S hspan⟩

lemma baseChangeEquiv_apply (hspan : Submodule.span K (S : Set A) = ⊤) (x : K ⊗[R] ↥S) :
    baseChangeEquiv S hspan x = baseChangeHom S x := rfl

lemma baseChangeEquiv_tmul (hspan : Submodule.span K (S : Set A) = ⊤) (k : K) (t : ↥S) :
    baseChangeEquiv S hspan (k ⊗ₜ[R] t) = k • (t : A) := rfl

theorem doubleEval_injective : Function.Injective (doubleEval (K := K) S) := by
  haveI : Module.Free K (K ⊗[R] ↥S) := Module.Free.of_divisionRing K _
  haveI : Module.Flat K (K ⊗[R] ↥S) := Module.Flat.of_free
  haveI : Module.Free K A := Module.Free.of_divisionRing K _
  haveI : Module.Flat K A := Module.Flat.of_free
  have hψ : Function.Injective (baseChangeHom (K := K) S).toLinearMap :=
    baseChangeHom_injective S
  have hmap : Function.Injective
      (TensorProduct.map (baseChangeHom (K := K) S).toLinearMap
        (baseChangeHom (K := K) S).toLinearMap) := by
    rw [← LinearMap.rTensor_comp_lTensor]
    exact (Module.Flat.rTensor_preserves_injective_linearMap _ hψ).comp
      (Module.Flat.lTensor_preserves_injective_linearMap _ hψ)
  intro x y hxy
  apply (TensorProduct.AlgebraTensorModule.distribBaseChange R K ↥S ↥S).injective
  apply hmap
  simpa only [doubleEval, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_toLinearMap] using hxy

theorem doubleCmp_injective [Module.Flat R ↥S] :
    Function.Injective (doubleCmp (K := K) S) := by
  intro x y hxy
  have h1 : Function.Injective (fun z : ↥S ⊗[R] ↥S => (1 : K) ⊗ₜ[R] z) :=
    one_tmul_injective
  exact h1 (doubleEval_injective S hxy)

theorem tensorSqHom_injective [Module.Flat R ↥S] :
    Function.Injective (tensorSqHom (K := K) S) := by
  intro x y h
  apply doubleCmp_injective (K := K) S
  rw [doubleCmp_eq_tensorSqHom, doubleCmp_eq_tensorSqHom, h]

theorem tripleEval_injective : Function.Injective (tripleEval (K := K) S) := by
  haveI : Module.Free K (K ⊗[R] ↥S) := Module.Free.of_divisionRing K _
  haveI : Module.Flat K (K ⊗[R] ↥S) := Module.Flat.of_free
  haveI : Module.Free K (A ⊗[K] A) := Module.Free.of_divisionRing K _
  haveI : Module.Flat K (A ⊗[K] A) := Module.Flat.of_free
  have hψ : Function.Injective (baseChangeHom (K := K) S).toLinearMap :=
    baseChangeHom_injective S
  have hd : Function.Injective (doubleEval (K := K) S) := doubleEval_injective S
  have hmap : Function.Injective
      (TensorProduct.map (baseChangeHom (K := K) S).toLinearMap (doubleEval (K := K) S)) := by
    rw [← LinearMap.rTensor_comp_lTensor]
    exact (Module.Flat.rTensor_preserves_injective_linearMap _ hψ).comp
      (Module.Flat.lTensor_preserves_injective_linearMap _ hd)
  intro x y hxy
  apply (TensorProduct.AlgebraTensorModule.distribBaseChange R K ↥S (↥S ⊗[R] ↥S)).injective
  apply hmap
  simpa only [tripleEval, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_toLinearMap] using hxy

theorem tripleCmpR_injective [Module.Flat R ↥S] :
    Function.Injective (tripleCmpR (K := K) S) := by
  intro x y hxy
  have h1 : Function.Injective
      (fun w : ↥S ⊗[R] (↥S ⊗[R] ↥S) => (1 : K) ⊗ₜ[R] w) :=
    one_tmul_injective
  exact h1 (tripleEval_injective S hxy)

end Domain

end Comparison

section Descent

variable {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
variable {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
variable {S : Subalgebra R A}

noncomputable def antipodeS
    (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) :
    ↥S →ₗ[R] ↥S where
  toFun t := ⟨HopfAlgebra.antipode K (t : A), hantipode (t : A) t.2⟩
  map_add' t t' := by
    apply Subtype.ext
    show HopfAlgebra.antipode K (((t + t') : ↥S) : A)
      = HopfAlgebra.antipode K (t : A) + HopfAlgebra.antipode K (t' : A)
    rw [Subalgebra.coe_add, map_add]
  map_smul' r t := by
    apply Subtype.ext
    show HopfAlgebra.antipode K (r • (t : A)) = r • HopfAlgebra.antipode K (t : A)
    rw [← algebraMap_smul K r (t : A), map_smul, algebraMap_smul]

theorem coe_antipodeS (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) (t : ↥S) :
    ((antipodeS hantipode t : ↥S) : A) = HopfAlgebra.antipode K (t : A) := rfl

lemma exists_doubleCmp_eq_comul
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (t : ↥S) :
    ∃ z : ↥S ⊗[R] ↥S, doubleCmp S z = Coalgebra.comul (R := K) (t : A) := by
  obtain ⟨z, hz⟩ := (tensorSqHom S).mem_range.mp (hcomul (t : A) t.2)
  exact ⟨z, by rw [doubleCmp_eq_tensorSqHom]; exact hz⟩

omit [IsScalarTower R K A] in

lemma exists_algebraMap_eq_counit
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) (t : ↥S) :
    ∃ r : R, algebraMap R K r = Coalgebra.counit (R := K) (t : A) :=
  RingHom.mem_range.mp (hcounit (t : A) t.2)

variable [IsFractionRing R K]

noncomputable def counitS
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    ↥S →ₗ[R] R where
  toFun t := (exists_algebraMap_eq_counit hcounit t).choose
  map_add' t t' := by
    apply IsFractionRing.injective R K
    rw [map_add, (exists_algebraMap_eq_counit hcounit (t + t')).choose_spec,
      (exists_algebraMap_eq_counit hcounit t).choose_spec,
      (exists_algebraMap_eq_counit hcounit t').choose_spec]
    rw [Subalgebra.coe_add, map_add]
  map_smul' r t := by
    apply IsFractionRing.injective R K
    rw [RingHom.id_apply, (exists_algebraMap_eq_counit hcounit (r • t)).choose_spec,
      smul_eq_mul, map_mul, (exists_algebraMap_eq_counit hcounit t).choose_spec,
      Subalgebra.coe_smul, ← algebraMap_smul K r (t : A), map_smul, smul_eq_mul]

theorem algebraMap_counitS
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) (t : ↥S) :
    algebraMap R K (counitS hcounit t) = Coalgebra.counit (R := K) (t : A) :=
  (exists_algebraMap_eq_counit hcounit t).choose_spec

variable [IsDomain R] [Module.Flat R ↥S]

noncomputable def comulS
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range) :
    ↥S →ₗ[R] ↥S ⊗[R] ↥S where
  toFun t := (exists_doubleCmp_eq_comul hcomul t).choose
  map_add' t t' := by
    apply doubleCmp_injective (K := K) S
    rw [doubleCmp_add, (exists_doubleCmp_eq_comul hcomul (t + t')).choose_spec,
      (exists_doubleCmp_eq_comul hcomul t).choose_spec,
      (exists_doubleCmp_eq_comul hcomul t').choose_spec]
    rw [Subalgebra.coe_add, map_add]
  map_smul' r t := by
    apply doubleCmp_injective (K := K) S
    rw [RingHom.id_apply, doubleCmp_smul,
      (exists_doubleCmp_eq_comul hcomul (r • t)).choose_spec,
      (exists_doubleCmp_eq_comul hcomul t).choose_spec]
    rw [Subalgebra.coe_smul, ← algebraMap_smul K r (t : A), map_smul]

lemma doubleCmp_comulS
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (t : ↥S) :
    doubleCmp S (comulS hcomul t) = Coalgebra.comul (R := K) (t : A) :=
  (exists_doubleCmp_eq_comul hcomul t).choose_spec

theorem tensorSqHom_comulS
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (t : ↥S) :
    tensorSqHom S (comulS hcomul t) = Coalgebra.comul (R := K) (t : A) := by
  rw [← doubleCmp_eq_tensorSqHom, doubleCmp_comulS]

theorem comulS_eq_iff
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (t : ↥S) (z : ↥S ⊗[R] ↥S) :
    comulS hcomul t = z ↔ tensorSqHom S z = Coalgebra.comul (R := K) (t : A) := by
  constructor
  · rintro rfl; exact tensorSqHom_comulS hcomul t
  · intro h
    apply tensorSqHom_injective (K := K) S
    rw [tensorSqHom_comulS, h]

omit [IsDomain R] [Module.Flat R ↥S] in
lemma val_lid_rTensor_counitS
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (z : ↥S ⊗[R] ↥S) :
    ((TensorProduct.lid R ↥S ((counitS hcounit).rTensor ↥S z) : ↥S) : A)
      = TensorProduct.lid K A
          ((Coalgebra.counit (R := K) (A := A)).rTensor A (doubleCmp S z)) := by
  induction z with
  | zero =>
      rw [map_zero, map_zero, doubleCmp_zero, map_zero, map_zero, ZeroMemClass.coe_zero]
  | tmul a b =>
      rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, doubleCmp_tmul,
        LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Subalgebra.coe_smul,
        ← algebraMap_counitS hcounit a, algebraMap_smul]
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, map_add, Subalgebra.coe_add, h₁, h₂, doubleCmp_add, map_add, map_add]

omit [IsDomain R] [Module.Flat R ↥S] in
lemma val_rid_lTensor_counitS
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (z : ↥S ⊗[R] ↥S) :
    ((TensorProduct.rid R ↥S ((counitS hcounit).lTensor ↥S z) : ↥S) : A)
      = TensorProduct.rid K A
          ((Coalgebra.counit (R := K) (A := A)).lTensor A (doubleCmp S z)) := by
  induction z with
  | zero =>
      rw [map_zero, map_zero, doubleCmp_zero, map_zero, map_zero, ZeroMemClass.coe_zero]
  | tmul a b =>
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, doubleCmp_tmul,
        LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Subalgebra.coe_smul,
        ← algebraMap_counitS hcounit b, algebraMap_smul]
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, map_add, Subalgebra.coe_add, h₁, h₂, doubleCmp_add, map_add, map_add]

omit [IsDomain R] [Module.Flat R ↥S] in
theorem counitS_one (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    counitS hcounit (1 : ↥S) = 1 := by
  apply IsFractionRing.injective R K
  rw [algebraMap_counitS, OneMemClass.coe_one, Bialgebra.counit_one, map_one]

omit [IsDomain R] [Module.Flat R ↥S] in
theorem counitS_mul (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) (a b : ↥S) :
    counitS hcounit (a * b) = counitS hcounit a * counitS hcounit b := by
  apply IsFractionRing.injective R K
  rw [algebraMap_counitS hcounit (a * b), map_mul, algebraMap_counitS hcounit a,
    algebraMap_counitS hcounit b, MulMemClass.coe_mul, Bialgebra.counit_mul]

omit [IsFractionRing R K] [IsDomain R] [Module.Flat R ↥S] in
lemma val_mul'_rTensor_antipodeS (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) (z : ↥S ⊗[R] ↥S) :
    ((LinearMap.mul' R ↥S ((antipodeS hantipode).rTensor ↥S z) : ↥S) : A)
      = LinearMap.mul' K A ((HopfAlgebra.antipode K (A := A)).rTensor A (doubleCmp S z)) := by
  induction z with
  | zero =>
      rw [map_zero, map_zero, doubleCmp_zero, map_zero, map_zero, ZeroMemClass.coe_zero]
  | tmul a b =>
      rw [LinearMap.rTensor_tmul, LinearMap.mul'_apply, MulMemClass.coe_mul,
        coe_antipodeS, doubleCmp_tmul, LinearMap.rTensor_tmul, LinearMap.mul'_apply]
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, map_add, Subalgebra.coe_add, h₁, h₂, doubleCmp_add, map_add, map_add]

omit [IsFractionRing R K] [IsDomain R] [Module.Flat R ↥S] in
lemma val_mul'_lTensor_antipodeS (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) (z : ↥S ⊗[R] ↥S) :
    ((LinearMap.mul' R ↥S ((antipodeS hantipode).lTensor ↥S z) : ↥S) : A)
      = LinearMap.mul' K A ((HopfAlgebra.antipode K (A := A)).lTensor A (doubleCmp S z)) := by
  induction z with
  | zero =>
      rw [map_zero, map_zero, doubleCmp_zero, map_zero, map_zero, ZeroMemClass.coe_zero]
  | tmul a b =>
      rw [LinearMap.lTensor_tmul, LinearMap.mul'_apply, MulMemClass.coe_mul,
        coe_antipodeS, doubleCmp_tmul, LinearMap.lTensor_tmul, LinearMap.mul'_apply]
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, map_add, Subalgebra.coe_add, h₁, h₂, doubleCmp_add, map_add, map_add]

lemma tripleCmpL_rTensor_comulS
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (z : ↥S ⊗[R] ↥S) :
    tripleCmpL S ((comulS hcomul).rTensor ↥S z)
      = (Coalgebra.comul (R := K) (A := A)).rTensor A (doubleCmp S z) := by
  induction z with
  | zero => rw [map_zero, tripleCmpL_zero, doubleCmp_zero, map_zero]
  | tmul a b =>
      rw [LinearMap.rTensor_tmul, tripleCmpL_tmul, doubleCmp_comulS, doubleCmp_tmul,
        LinearMap.rTensor_tmul]
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, tripleCmpL_add, h₁, h₂, doubleCmp_add, map_add]

lemma tripleCmpR_lTensor_comulS
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (z : ↥S ⊗[R] ↥S) :
    tripleCmpR S ((comulS hcomul).lTensor ↥S z)
      = (Coalgebra.comul (R := K) (A := A)).lTensor A (doubleCmp S z) := by
  induction z with
  | zero => rw [map_zero, tripleCmpR_zero, doubleCmp_zero, map_zero]
  | tmul a b =>
      rw [LinearMap.lTensor_tmul, tripleCmpR_tmul, doubleCmp_comulS, doubleCmp_tmul,
        LinearMap.lTensor_tmul]
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, tripleCmpR_add, h₁, h₂, doubleCmp_add, map_add]

theorem comulS_coassoc
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range) :
    ↑(TensorProduct.assoc R ↥S ↥S ↥S) ∘ₗ
        (comulS hcomul).rTensor ↥S ∘ₗ comulS hcomul
      = (comulS hcomul).lTensor ↥S ∘ₗ comulS hcomul := by
  apply LinearMap.ext
  intro t
  apply tripleCmpR_injective (K := K) S
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [tripleCmpR_assoc, tripleCmpL_rTensor_comulS, doubleCmp_comulS,
    Coalgebra.coassoc_apply, ← doubleCmp_comulS hcomul t, ← tripleCmpR_lTensor_comulS]

theorem counitS_rTensor_comp_comulS
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    (counitS hcounit).rTensor ↥S ∘ₗ comulS hcomul = TensorProduct.mk R R ↥S 1 := by
  apply LinearMap.ext
  intro t
  have hinj : ∀ a b : R ⊗[R] ↥S,
      ((TensorProduct.lid R ↥S a : ↥S) : A) = ((TensorProduct.lid R ↥S b : ↥S) : A) → a = b :=
    fun a b hab => (TensorProduct.lid R ↥S).injective (Subtype.val_injective hab)
  apply hinj
  simp only [LinearMap.comp_apply]
  rw [val_lid_rTensor_counitS hcounit (comulS hcomul t), doubleCmp_comulS,
    Coalgebra.rTensor_counit_comul, TensorProduct.mk_apply, TensorProduct.lid_tmul,
    TensorProduct.lid_tmul, one_smul, one_smul]

theorem counitS_lTensor_comp_comulS
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    (counitS hcounit).lTensor ↥S ∘ₗ comulS hcomul = (TensorProduct.mk R ↥S R).flip 1 := by
  apply LinearMap.ext
  intro t
  have hinj : ∀ a b : ↥S ⊗[R] R,
      ((TensorProduct.rid R ↥S a : ↥S) : A) = ((TensorProduct.rid R ↥S b : ↥S) : A) → a = b :=
    fun a b hab => (TensorProduct.rid R ↥S).injective (Subtype.val_injective hab)
  apply hinj
  simp only [LinearMap.comp_apply, LinearMap.flip_apply]
  rw [val_rid_lTensor_counitS hcounit (comulS hcomul t), doubleCmp_comulS,
    Coalgebra.lTensor_counit_comul, TensorProduct.mk_apply, TensorProduct.rid_tmul,
    TensorProduct.rid_tmul, one_smul, one_smul]

variable (S) in

@[reducible]
noncomputable def coalgebra
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    Coalgebra R ↥S where
  comul := comulS hcomul
  counit := counitS hcounit
  coassoc := comulS_coassoc hcomul
  rTensor_counit_comp_comul := counitS_rTensor_comp_comulS hcomul hcounit
  lTensor_counit_comp_comul := counitS_lTensor_comp_comulS hcomul hcounit

theorem comulS_one
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range) :
    comulS hcomul (1 : ↥S) = 1 := by
  apply tensorSqHom_injective (K := K) S
  rw [tensorSqHom_comulS, OneMemClass.coe_one, Bialgebra.comul_one, map_one]

theorem comulS_mul
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range) (a b : ↥S) :
    comulS hcomul (a * b) = comulS hcomul a * comulS hcomul b := by
  apply tensorSqHom_injective (K := K) S
  rw [tensorSqHom_comulS hcomul (a * b), MulMemClass.coe_mul, Bialgebra.comul_mul,
    map_mul, tensorSqHom_comulS, tensorSqHom_comulS]

variable (S) in

@[reducible]
noncomputable def bialgebra
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    Bialgebra R ↥S :=
  letI : Coalgebra R ↥S := HopfOrder.coalgebra S hcomul hcounit
  Bialgebra.mk' R ↥S (counitS_one hcounit) (fun {a b} => counitS_mul hcounit a b)
    (comulS_one hcomul) (fun {a b} => comulS_mul hcomul a b)

theorem mul_antipodeS_rTensor_comulS
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) :
    LinearMap.mul' R ↥S ∘ₗ (antipodeS hantipode).rTensor ↥S ∘ₗ comulS hcomul
      = (Algebra.linearMap R ↥S) ∘ₗ counitS hcounit := by
  apply LinearMap.ext
  intro t
  apply Subtype.val_injective
  simp only [LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [val_mul'_rTensor_antipodeS hantipode (comulS hcomul t), doubleCmp_comulS,
    HopfAlgebra.mul_antipode_rTensor_comul_apply, ← algebraMap_counitS hcounit t,
    ← IsScalarTower.algebraMap_apply R K A]
  rfl

theorem mul_antipodeS_lTensor_comulS
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) :
    LinearMap.mul' R ↥S ∘ₗ (antipodeS hantipode).lTensor ↥S ∘ₗ comulS hcomul
      = (Algebra.linearMap R ↥S) ∘ₗ counitS hcounit := by
  apply LinearMap.ext
  intro t
  apply Subtype.val_injective
  simp only [LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [val_mul'_lTensor_antipodeS hantipode (comulS hcomul t), doubleCmp_comulS,
    HopfAlgebra.mul_antipode_lTensor_comul_apply, ← algebraMap_counitS hcounit t,
    ← IsScalarTower.algebraMap_apply R K A]
  rfl

variable (S) in

@[reducible]
noncomputable def hopfAlgebra
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) :
    HopfAlgebra R ↥S :=
  letI : Bialgebra R ↥S := HopfOrder.bialgebra S hcomul hcounit
  { antipode := antipodeS hantipode
    mul_antipode_rTensor_comul := mul_antipodeS_rTensor_comulS hcomul hcounit hantipode
    mul_antipode_lTensor_comul := mul_antipodeS_lTensor_comulS hcomul hcounit hantipode }

theorem tensorSqHom_comul_eq
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) (t : ↥S) :
    letI : Coalgebra R ↥S := HopfOrder.coalgebra S hcomul hcounit
    tensorSqHom S (Coalgebra.comul (R := R) t) = Coalgebra.comul (R := K) (t : A) :=
  tensorSqHom_comulS hcomul t

theorem algebraMap_counit_eq
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) (t : ↥S) :
    letI : Coalgebra R ↥S := HopfOrder.coalgebra S hcomul hcounit
    algebraMap R K (Coalgebra.counit (R := R) t) = Coalgebra.counit (R := K) (t : A) :=
  algebraMap_counitS hcounit t

theorem coe_antipode_eq
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) (t : ↥S) :
    letI : HopfAlgebra R ↥S := HopfOrder.hopfAlgebra S hcomul hcounit hantipode
    ((HopfAlgebra.antipode R t : ↥S) : A) = HopfAlgebra.antipode K (t : A) :=
  rfl

theorem val_comul
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) (h : ↥S) :
    letI : HopfAlgebra R ↥S := HopfOrder.hopfAlgebra S hcomul hcounit hantipode
    Coalgebra.comul (R := K) (S.val h) =
      Algebra.TensorProduct.productMap
        (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
        (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
        (Coalgebra.comul (R := R) h) :=
  (tensorSqHom_comulS hcomul h).symm

theorem val_counit
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) (h : ↥S) :
    letI : HopfAlgebra R ↥S := HopfOrder.hopfAlgebra S hcomul hcounit hantipode
    algebraMap R K (Coalgebra.counit (R := R) h) = Coalgebra.counit (R := K) (S.val h) :=
  algebraMap_counitS hcounit h

theorem val_antipode
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) (h : ↥S) :
    letI : HopfAlgebra R ↥S := HopfOrder.hopfAlgebra S hcomul hcounit hantipode
    S.val (HopfAlgebra.antipode R h) = HopfAlgebra.antipode K (S.val h) :=
  rfl

end Descent

section GenericFibre

variable {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
variable {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
variable [IsDomain R] [IsFractionRing R K]
variable {S : Subalgebra R A} [Module.Flat R ↥S]

theorem comul_baseChangeHom
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) (x : K ⊗[R] ↥S) :
    letI : Bialgebra R ↥S := HopfOrder.bialgebra S hcomul hcounit
    Coalgebra.comul (R := K) (baseChangeHom S x)
      = TensorProduct.map (baseChangeHom S).toLinearMap (baseChangeHom S).toLinearMap
          (Coalgebra.comul (R := K) x) := by
  letI : Bialgebra R ↥S := HopfOrder.bialgebra S hcomul hcounit
  induction x with
  | zero => simp only [map_zero]
  | tmul k h =>
      have h1 : (k ⊗ₜ[R] h : K ⊗[R] ↥S) = k • ((1 : K) ⊗ₜ[R] h) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, map_smul, map_smul, map_smul, map_smul]
      congr 1
      rw [baseChangeHom_one_tmul, TensorProduct.comul_tmul, CommSemiring.comul_apply,
        ← tensorSqHom_comulS hcomul h]
      exact (baseChangeSq_one_tmul (K := K) S (comulS hcomul h)).symm
  | add x y hx hy => simp only [map_add, hx, hy]

theorem counit_baseChangeHom
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) (x : K ⊗[R] ↥S) :
    letI : Bialgebra R ↥S := HopfOrder.bialgebra S hcomul hcounit
    Coalgebra.counit (R := K) (baseChangeHom S x) = Coalgebra.counit (R := K) x := by
  letI : Bialgebra R ↥S := HopfOrder.bialgebra S hcomul hcounit
  induction x with
  | zero => simp only [map_zero]
  | tmul k h =>
      rw [baseChangeHom_tmul, map_smul, TensorProduct.counit_tmul, CommSemiring.counit_apply,
        ← algebraMap_counitS hcounit h]
      show k • algebraMap R K (counitS hcounit h) = (counitS hcounit h) • k
      rw [Algebra.smul_def, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem antipode_baseChangeHom
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) (x : K ⊗[R] ↥S) :
    letI : HopfAlgebra R ↥S := HopfOrder.hopfAlgebra S hcomul hcounit hantipode
    HopfAlgebra.antipode K (baseChangeHom S x) = baseChangeHom S (HopfAlgebra.antipode K x) := by
  letI : HopfAlgebra R ↥S := HopfOrder.hopfAlgebra S hcomul hcounit hantipode
  induction x with
  | zero => simp only [map_zero]
  | tmul k h =>
      rw [TensorProduct.antipode_def, TensorProduct.AlgebraTensorModule.map_tmul,
        CommSemiring.antipode_eq_id, LinearMap.id_apply, baseChangeHom_tmul, baseChangeHom_tmul,
        map_smul]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable (S) in

noncomputable def baseChangeBialgEquiv
    (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    letI : Bialgebra R ↥S := HopfOrder.bialgebra S hcomul hcounit
    (K ⊗[R] ↥S) ≃ₐc[K] A :=
  letI : Bialgebra R ↥S := HopfOrder.bialgebra S hcomul hcounit
  BialgEquiv.ofAlgEquiv (baseChangeEquiv S hspan)
    (by
      apply AlgHom.ext
      intro x
      exact counit_baseChangeHom hcomul hcounit x)
    (by
      apply AlgHom.ext
      intro x
      show Algebra.TensorProduct.map (baseChangeEquiv S hspan : K ⊗[R] ↥S →ₐ[K] A)
          (baseChangeEquiv S hspan : K ⊗[R] ↥S →ₐ[K] A) (Coalgebra.comul (R := K) x)
        = Coalgebra.comul (R := K) (baseChangeHom S x)
      rw [comul_baseChangeHom hcomul hcounit x]
      rfl)

theorem baseChangeBialgEquiv_apply
    (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) (x : K ⊗[R] ↥S) :
    baseChangeBialgEquiv S hspan hcomul hcounit x = baseChangeHom S x := rfl

end GenericFibre

section Functorial

variable {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
variable {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
variable {B : Type w'} [CommRing B] [HopfAlgebra K B] [Algebra R B] [IsScalarTower R K B]
variable [IsDomain R] [IsFractionRing R K]

omit [IsDomain R] [IsFractionRing R K] in

lemma map_tensorSqHom {S : Subalgebra R A} {T : Subalgebra R B}
    (π : A →ₗ[K] B) (f : ↥S →ₐ[R] ↥T) (hf : ∀ s : ↥S, ((f s : ↥T) : B) = π (s : A))
    (z : ↥S ⊗[R] ↥S) :
    TensorProduct.map π π (tensorSqHom S z)
      = tensorSqHom T (Algebra.TensorProduct.map f f z) := by
  induction z with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a b =>
      rw [tensorSqHom_tmul, TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
        tensorSqHom_tmul, hf, hf]
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]

noncomputable def mapBialgHom
    {S : Subalgebra R A} [Module.Flat R ↥S] {T : Subalgebra R B} [Module.Flat R ↥T]
    (π : A →ₐc[K] B) (hπ : ∀ x ∈ S, π x ∈ T)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hcomul' : ∀ x ∈ T, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : B →ₐ[K] B ⊗[K] B).restrictScalars R).comp T.val)
          (((Algebra.TensorProduct.includeRight : B →ₐ[K] B ⊗[K] B).restrictScalars R).comp T.val)).range)
    (hcounit' : ∀ x ∈ T, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    letI : Bialgebra R ↥S := HopfOrder.bialgebra S hcomul hcounit
    letI : Bialgebra R ↥T := HopfOrder.bialgebra T hcomul' hcounit'
    ↥S →ₐc[R] ↥T :=
  letI : Bialgebra R ↥S := HopfOrder.bialgebra S hcomul hcounit
  letI : Bialgebra R ↥T := HopfOrder.bialgebra T hcomul' hcounit'
  let f : ↥S →ₐ[R] ↥T :=
    (((π : A →ₐ[K] B).restrictScalars R).comp S.val).codRestrict T (fun s => hπ (s : A) s.2)
  have hf : ∀ s : ↥S, ((f s : ↥T) : B) = (π : A →ₗ[K] B) (s : A) := fun _ => rfl
  BialgHom.ofAlgHom f
    (by
      apply AlgHom.ext
      intro s
      apply IsFractionRing.injective R K
      show algebraMap R K (counitS hcounit' (f s)) = algebraMap R K (counitS hcounit s)
      rw [algebraMap_counitS, algebraMap_counitS, hf]
      exact CoalgHomClass.counit_comp_apply π (s : A))
    (by
      apply AlgHom.ext
      intro s
      apply tensorSqHom_injective (K := K) T
      show tensorSqHom T (Algebra.TensorProduct.map f f (comulS hcomul s))
        = tensorSqHom T (comulS hcomul' (f s))
      rw [← map_tensorSqHom (π : A →ₗ[K] B) f hf, tensorSqHom_comulS, tensorSqHom_comulS, hf]
      exact CoalgHomClass.map_comp_comul_apply π (s : A))

theorem coe_mapBialgHom
    {S : Subalgebra R A} [Module.Flat R ↥S] {T : Subalgebra R B} [Module.Flat R ↥T]
    (π : A →ₐc[K] B) (hπ : ∀ x ∈ S, π x ∈ T)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hcomul' : ∀ x ∈ T, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : B →ₐ[K] B ⊗[K] B).restrictScalars R).comp T.val)
          (((Algebra.TensorProduct.includeRight : B →ₐ[K] B ⊗[K] B).restrictScalars R).comp T.val)).range)
    (hcounit' : ∀ x ∈ T, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) (s : ↥S) :
    ((mapBialgHom π hπ hcomul hcounit hcomul' hcounit' s : ↥T) : B) = π (s : A) := rfl

noncomputable def toMap
    {S : Subalgebra R A} [Module.Flat R ↥S] (π : A →ₐc[K] B)
    [Module.Flat R ↥(S.map ((π : A →ₐ[K] B).restrictScalars R))]
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hcomul' : ∀ x ∈ (S.map ((π : A →ₐ[K] B).restrictScalars R)), Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : B →ₐ[K] B ⊗[K] B).restrictScalars R).comp (S.map ((π : A →ₐ[K] B).restrictScalars R)).val)
          (((Algebra.TensorProduct.includeRight : B →ₐ[K] B ⊗[K] B).restrictScalars R).comp (S.map ((π : A →ₐ[K] B).restrictScalars R)).val)).range)
    (hcounit' : ∀ x ∈ (S.map ((π : A →ₐ[K] B).restrictScalars R)), Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    letI : Bialgebra R ↥S := HopfOrder.bialgebra S hcomul hcounit
    letI : Bialgebra R ↥(S.map ((π : A →ₐ[K] B).restrictScalars R)) := HopfOrder.bialgebra (S.map ((π : A →ₐ[K] B).restrictScalars R)) hcomul' hcounit'
    ↥S →ₐc[R] ↥(S.map ((π : A →ₐ[K] B).restrictScalars R)) :=
  mapBialgHom π (fun x hx => Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩) hcomul hcounit hcomul' hcounit'

theorem coe_toMap
    {S : Subalgebra R A} [Module.Flat R ↥S] (π : A →ₐc[K] B)
    [Module.Flat R ↥(S.map ((π : A →ₐ[K] B).restrictScalars R))]
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hcomul' : ∀ x ∈ (S.map ((π : A →ₐ[K] B).restrictScalars R)), Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : B →ₐ[K] B ⊗[K] B).restrictScalars R).comp (S.map ((π : A →ₐ[K] B).restrictScalars R)).val)
          (((Algebra.TensorProduct.includeRight : B →ₐ[K] B ⊗[K] B).restrictScalars R).comp (S.map ((π : A →ₐ[K] B).restrictScalars R)).val)).range)
    (hcounit' : ∀ x ∈ (S.map ((π : A →ₐ[K] B).restrictScalars R)), Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) (s : ↥S) :
    (S.map ((π : A →ₐ[K] B).restrictScalars R)).val (toMap π hcomul hcounit hcomul' hcounit' s) = π (S.val s) := rfl

noncomputable def inclusion
    {S S' : Subalgebra R A} [Module.Flat R ↥S] [Module.Flat R ↥S'] (h : S ≤ S')
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hcomul' : ∀ x ∈ S', Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)).range)
    (hcounit' : ∀ x ∈ S', Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    letI : Bialgebra R ↥S := HopfOrder.bialgebra S hcomul hcounit
    letI : Bialgebra R ↥S' := HopfOrder.bialgebra S' hcomul' hcounit'
    ↥S →ₐc[R] ↥S' :=
  letI : Bialgebra R ↥S := HopfOrder.bialgebra S hcomul hcounit
  letI : Bialgebra R ↥S' := HopfOrder.bialgebra S' hcomul' hcounit'
  have hf : ∀ s : ↥S, ((Subalgebra.inclusion h s : ↥S') : A) = (LinearMap.id : A →ₗ[K] A) (s : A) :=
    fun _ => rfl
  BialgHom.ofAlgHom (Subalgebra.inclusion h)
    (by
      apply AlgHom.ext
      intro s
      apply IsFractionRing.injective R K
      show algebraMap R K (counitS hcounit' (Subalgebra.inclusion h s))
        = algebraMap R K (counitS hcounit s)
      rw [algebraMap_counitS, algebraMap_counitS]
      rfl)
    (by
      apply AlgHom.ext
      intro s
      apply tensorSqHom_injective (K := K) S'
      show tensorSqHom S' (Algebra.TensorProduct.map (Subalgebra.inclusion h) (Subalgebra.inclusion h)
          (comulS hcomul s)) = tensorSqHom S' (comulS hcomul' (Subalgebra.inclusion h s))
      rw [← map_tensorSqHom (LinearMap.id : A →ₗ[K] A) (Subalgebra.inclusion h) hf,
        tensorSqHom_comulS, tensorSqHom_comulS, TensorProduct.map_id, LinearMap.id_apply]
      rfl)

theorem coe_inclusion
    {S S' : Subalgebra R A} [Module.Flat R ↥S] [Module.Flat R ↥S'] (h : S ≤ S')
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hcomul' : ∀ x ∈ S', Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)).range)
    (hcounit' : ∀ x ∈ S', Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) (s : ↥S) :
    ((inclusion h hcomul hcounit hcomul' hcounit' s : ↥S') : A) = (s : A) := rfl

end Functorial

section PID

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
variable {A : Type w} [CommRing A]

theorem moduleFree_of_finite [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (S : Subalgebra R A) [Module.Finite R ↥S] : Module.Free R ↥S := by
  haveI : Module.IsTorsionFree R A := by
    refine Module.IsTorsionFree.mk fun r hr => ?_
    have hr0 : r ≠ 0 := hr.left.ne_zero
    have hK : algebraMap R K r ≠ 0 := fun h =>
      hr0 ((injective_iff_map_eq_zero (algebraMap R K)).mp (IsFractionRing.injective R K) r h)
    intro a b hab
    have hab' : algebraMap R K r • a = algebraMap R K r • b := by
      simpa [IsScalarTower.algebraMap_smul] using hab
    exact smul_right_injective A hK hab'
  haveI : Module.IsTorsionFree R ↥S :=
    Function.Injective.moduleIsTorsionFree (fun s : ↥S => (s : A)) Subtype.coe_injective
      (fun _ _ => rfl)
  exact Module.free_of_finite_type_torsion_free'

theorem moduleFlat_of_finite [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (S : Subalgebra R A) [Module.Finite R ↥S] : Module.Flat R ↥S := by
  haveI := moduleFree_of_finite (K := K) S
  exact Module.Flat.of_free

variable [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
variable (S : Subalgebra R A) [Module.Finite R ↥S]

@[reducible]
noncomputable def coalgebraOfFinite
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    Coalgebra R ↥S :=
  haveI := moduleFlat_of_finite (K := K) S
  HopfOrder.coalgebra S hcomul hcounit

@[reducible]
noncomputable def bialgebraOfFinite
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    Bialgebra R ↥S :=
  haveI := moduleFlat_of_finite (K := K) S
  HopfOrder.bialgebra S hcomul hcounit

@[reducible]
noncomputable def hopfAlgebraOfFinite
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hantipode : ∀ x ∈ S, HopfAlgebra.antipode K x ∈ S) :
    HopfAlgebra R ↥S :=
  haveI := moduleFlat_of_finite (K := K) S
  HopfOrder.hopfAlgebra S hcomul hcounit hantipode

noncomputable def baseChangeBialgEquivOfFinite
    (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    letI : Bialgebra R ↥S := bialgebraOfFinite S hcomul hcounit
    (K ⊗[R] ↥S) ≃ₐc[K] A :=
  haveI := moduleFlat_of_finite (K := K) S
  baseChangeBialgEquiv S hspan hcomul hcounit

end PID

end HopfOrder


