-- Prove2me | solution 1 for AutomorphicForm.exists_isArchFactorBiFinite_of_forall_eq_integral_snoc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2c525472-c407-56b5-8c67-a89fc06c7a2f

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_of_forall_eq_integral_snoc

set_option autoImplicit false

open NumberField MeasureTheory

private noncomputable def typePiece_sliceMap {H G : Type*} [Group H] [Group G] (ι : H →* G) (z : G) :
    (G → ℂ) →ₗ[ℂ] (H → ℂ) where
  toFun u := fun k => u (z * ι k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def typePiece_matrixCoeff {H : Type*} [Group H] {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ H W) : Module.Dual ℂ W →ₗ[ℂ] W →ₗ[ℂ] (H → ℂ) :=
  LinearMap.mk₂ ℂ (fun φ w => fun k => φ (ρ k w))
    (fun φ₁ φ₂ w => by funext k; simp)
    (fun c φ w => by funext k; simp)
    (fun φ w₁ w₂ => by funext k; simp)
    (fun c φ w => by funext k; simp)

private theorem typePiece_matrixCoeff_apply {H : Type*} [Group H] {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ H W) (φ : Module.Dual ℂ W) (w : W) (k : H) :
    typePiece_matrixCoeff ρ φ w k = φ (ρ k w) := rfl

private theorem typePiece_exists_fd_slices {H G : Type*} [Group H] [Group G] (ι : H →* G) {m : ℕ}
    (W : Fin m → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [∀ i, FiniteDimensional ℂ (W i)] (ρ : ∀ i, Representation ℂ H (W i)) :
    ∃ M : Submodule ℂ (H → ℂ), FiniteDimensional ℂ M ∧
      ∀ s ∈ ⨆ i, AutomorphicForm.typeSubmodule ι (ρ i), ∀ z : G, (fun k => s (z * ι k)) ∈ M := by
  classical
  let b := fun i => Module.finBasis ℂ (W i)
  let gen : ∀ i, Fin (Module.finrank ℂ (W i)) × Fin (Module.finrank ℂ (W i)) → (H → ℂ) :=
    fun i p => typePiece_matrixCoeff (ρ i) ((b i).coord p.1) (b i p.2)
  let M : Submodule ℂ (H → ℂ) := Submodule.span ℂ (⋃ i, Set.range (gen i))
  have hMfd : FiniteDimensional ℂ M :=
    Module.Finite.span_of_finite ℂ (Set.finite_iUnion fun i => Set.finite_range (gen i))

  have hcoef : ∀ (i : Fin m) (φ : Module.Dual ℂ (W i)) (w : W i), typePiece_matrixCoeff (ρ i) φ w ∈ M := by
    intro i φ w
    have hw : typePiece_matrixCoeff (ρ i) φ w = ∑ l, (b i).repr w l • typePiece_matrixCoeff (ρ i) φ (b i l) := by
      conv_lhs => rw [← (b i).sum_repr w]
      simp only [map_sum, map_smul]
    rw [hw]
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
    have hφ : typePiece_matrixCoeff (ρ i) φ (b i l) =
        ∑ a, φ (b i a) • typePiece_matrixCoeff (ρ i) ((b i).coord a) (b i l) := by
      conv_lhs => rw [← (b i).sum_dual_apply_smul_coord φ]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [hφ]
    refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span (Set.mem_iUnion.2 ⟨i, ⟨(a, l), rfl⟩⟩)
  refine ⟨M, hMfd, ?_⟩

  have hle : (⨆ i, AutomorphicForm.typeSubmodule ι (ρ i)) ≤
      ⨅ z : G, M.comap (typePiece_sliceMap ι z) := by
    refine iSup_le fun i => Submodule.span_le.2 ?_
    rintro _ ⟨T, hT, w, rfl⟩
    show T w ∈ ⨅ z : G, M.comap (typePiece_sliceMap ι z)
    refine (Submodule.mem_iInf _).2 fun z => ?_
    rw [Submodule.mem_comap]
    have h : typePiece_sliceMap ι z (T w) = typePiece_matrixCoeff (ρ i) (LinearMap.proj z ∘ₗ T) w := by
      funext k
      show T w (z * ι k) = T (ρ i k w) z
      exact (hT k w z).symm
    rw [h]
    exact hcoef i _ w
  intro s hs z
  exact Submodule.mem_comap.1 ((Submodule.mem_iInf _).1 (hle hs) z)

private theorem typePiece_le_of_equiv {H G : Type*} [Group H] [Group G] (ι : H →* G)
    {W₁ W₂ : Type*} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    (ρ₁ : Representation ℂ H W₁) (ρ₂ : Representation ℂ H W₂) (e : W₁ ≃ₗ[ℂ] W₂)
    (he : ∀ (k : H) (w : W₁), e (ρ₁ k w) = ρ₂ k (e w)) :
    AutomorphicForm.typeSubmodule ι ρ₁ ≤ AutomorphicForm.typeSubmodule ι ρ₂ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨T, hT, w, rfl⟩
  have h1 : ∀ (k : H) (v : W₂), e.symm (ρ₂ k v) = ρ₁ k (e.symm v) := by
    intro k v
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
  have hT₂ : AutomorphicForm.IsRightEquivariant ι ρ₂ (T ∘ₗ e.symm.toLinearMap) := by
    intro k v x
    show T (e.symm (ρ₂ k v)) x = T (e.symm v) (x * ι k)
    rw [h1]
    exact hT k (e.symm v) x
  have h2 : (T ∘ₗ e.symm.toLinearMap) (e w) = T w := by
    show T (e.symm (e w)) = T w
    rw [LinearEquiv.symm_apply_apply]
  have h3 := AutomorphicForm.mem_typeSubmodule_of_isRightEquivariant hT₂ (e w)
  rw [h2] at h3
  exact h3

private noncomputable def typePiece_transportRep {H : Type*} [Group H] {W₁ W₂ : Type*} [AddCommGroup W₁] [Module ℂ W₁]
    [AddCommGroup W₂] [Module ℂ W₂] (ρ : Representation ℂ H W₁) (e : W₁ ≃ₗ[ℂ] W₂) :
    Representation ℂ H W₂ where
  toFun k := e.conj (ρ k)
  map_one' := by
    ext
    simp [LinearEquiv.conj_apply_apply]
  map_mul' k₁ k₂ := by
    ext
    simp [LinearEquiv.conj_apply_apply]

private theorem typePiece_transportRep_apply' {H : Type*} [Group H] {W₁ W₂ : Type*} [AddCommGroup W₁]
    [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂] (ρ : Representation ℂ H W₁) (e : W₁ ≃ₗ[ℂ] W₂)
    (k : H) (y : W₂) : typePiece_transportRep ρ e k y = e (ρ k (e.symm y)) := by
  show e.conj (ρ k) y = e (ρ k (e.symm y))
  exact LinearEquiv.conj_apply_apply e (ρ k) y

private theorem typePiece_transportRep_apply {H : Type*} [Group H] {W₁ W₂ : Type*} [AddCommGroup W₁]
    [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂] (ρ : Representation ℂ H W₁) (e : W₁ ≃ₗ[ℂ] W₂)
    (k : H) (w : W₁) : typePiece_transportRep ρ e k (e w) = e (ρ k w) := by
  rw [typePiece_transportRep_apply', LinearEquiv.symm_apply_apply]

private theorem typePiece_evalEquiv_equivariant {H : Type*} [Group H] {W : Type*} [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ H W) (k : H) (w : W) :
    Module.evalEquiv ℂ W (ρ k w) = ρ.dual.dual k (Module.evalEquiv ℂ W w) := by
  apply LinearMap.ext
  intro φ
  simp [Representation.dual_apply, Module.Dual.transpose_apply]

private theorem typePiece_dualMap_equivariant {H : Type*} [Group H] {W₁ W₂ : Type*}
    [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂] (ρ : Representation ℂ H W₁)
    (e : W₁ ≃ₗ[ℂ] W₂) (k : H) (ξ : Module.Dual ℂ W₁) :
    e.symm.dualMap (ρ.dual k ξ) = (typePiece_transportRep ρ e).dual k (e.symm.dualMap ξ) := by
  apply LinearMap.ext
  intro y
  simp [Representation.dual_apply, Module.Dual.transpose_apply, LinearEquiv.dualMap_apply,
    typePiece_transportRep_apply']

private noncomputable def typePiece_transSpan {H G : Type*} [Group H] [Group G] (ι : H →* G) (u : G → ℂ) :
    Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range fun k : H => fun x : G => u (x * ι k))

private theorem typePiece_mem_transSpan_self {H G : Type*} [Group H] [Group G] (ι : H →* G) (u : G → ℂ) :
    u ∈ typePiece_transSpan ι u := by
  refine Submodule.subset_span ⟨1, ?_⟩
  funext x
  show u (x * ι 1) = u x
  rw [map_one, mul_one]

private theorem typePiece_transSpan_stable {H G : Type*} [Group H] [Group G] (ι : H →* G) (u : G → ℂ)
    (k : H) : ∀ v ∈ typePiece_transSpan ι u, (fun x : G => v (x * ι k)) ∈ typePiece_transSpan ι u := by
  intro v hv
  refine Submodule.span_induction (p := fun v _ => (fun x : G => v (x * ι k)) ∈ typePiece_transSpan ι u)
    ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨k', rfl⟩
    refine Submodule.subset_span ⟨k * k', ?_⟩
    funext x
    show u (x * ι (k * k')) = u (x * ι k * ι k')
    rw [map_mul, mul_assoc]
  · exact (typePiece_transSpan ι u).zero_mem
  · exact fun _ _ _ _ ha hb => (typePiece_transSpan ι u).add_mem ha hb
  · exact fun c _ _ ha => (typePiece_transSpan ι u).smul_mem c ha

private noncomputable def typePiece_transRep {H G : Type*} [Group H] [Group G] (ι : H →* G) (u : G → ℂ) :
    Representation ℂ H (typePiece_transSpan ι u) where
  toFun k :=
    { toFun := fun v => ⟨fun x => (v : G → ℂ) (x * ι k), typePiece_transSpan_stable ι u k (v : G → ℂ) v.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext
    simp
  map_mul' k₁ k₂ := by
    ext
    simp [mul_assoc]

private theorem typePiece_isRightEquivariant_subtype {H G : Type*} [Group H] [Group G] (ι : H →* G)
    (u : G → ℂ) :
    AutomorphicForm.IsRightEquivariant ι (typePiece_transRep ι u) (typePiece_transSpan ι u).subtype := by
  intro _ _ _
  rfl

private theorem typePiece_exists_rep_of_fd {H G : Type*} [Group H] [Group G] (ι : H →* G) (u : G → ℂ)
    (hu : FiniteDimensional ℂ
      ↥(Submodule.span ℂ (Set.range fun k : H => fun x : G => u (x * ι k)))) :
    ∃ (N : ℕ) (ρ : Representation ℂ H (Fin N → ℂ)), u ∈ AutomorphicForm.typeSubmodule ι ρ := by
  haveI : FiniteDimensional ℂ ↥(typePiece_transSpan ι u) := hu
  let e := (Module.finBasis ℂ ↥(typePiece_transSpan ι u)).equivFun
  refine ⟨_, typePiece_transportRep (typePiece_transRep ι u) e, ?_⟩
  refine typePiece_le_of_equiv ι (typePiece_transRep ι u) (typePiece_transportRep (typePiece_transRep ι u) e)
    e (fun k w => (typePiece_transportRep_apply (typePiece_transRep ι u) e k w).symm) ?_
  exact AutomorphicForm.mem_typeSubmodule_of_isRightEquivariant (typePiece_isRightEquivariant_subtype ι u)
    ⟨u, typePiece_mem_transSpan_self ι u⟩

private theorem typePiece_exists_dual_rep_of_fd {H G : Type*} [Group H] [Group G] (ι : H →* G) (u : G → ℂ)
    (hu : FiniteDimensional ℂ
      ↥(Submodule.span ℂ (Set.range fun k : H => fun x : G => u (x * ι k)))) :
    ∃ (N : ℕ) (ρ : Representation ℂ H (Fin N → ℂ)), u ∈ AutomorphicForm.typeSubmodule ι ρ.dual := by
  haveI : FiniteDimensional ℂ ↥(typePiece_transSpan ι u) := hu
  let e' := (Module.finBasis ℂ (Module.Dual ℂ ↥(typePiece_transSpan ι u))).equivFun
  refine ⟨_, typePiece_transportRep (typePiece_transRep ι u).dual e', ?_⟩
  refine typePiece_le_of_equiv ι (typePiece_transRep ι u).dual.dual
    (typePiece_transportRep (typePiece_transRep ι u).dual e').dual e'.symm.dualMap
    (typePiece_dualMap_equivariant (typePiece_transRep ι u).dual e') ?_
  refine typePiece_le_of_equiv ι (typePiece_transRep ι u) (typePiece_transRep ι u).dual.dual
    (Module.evalEquiv ℂ ↥(typePiece_transSpan ι u)) (typePiece_evalEquiv_equivariant (typePiece_transRep ι u)) ?_
  exact AutomorphicForm.mem_typeSubmodule_of_isRightEquivariant (typePiece_isRightEquivariant_subtype ι u)
    ⟨u, typePiece_mem_transSpan_self ι u⟩

private theorem secondCountableTopology_gl (A : Type) [CommRing A] [TopologicalSpace A]
    [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

private theorem locallyCompactSpace_gl (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

private theorem sigmaCompactSpace_gl (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A]
    [SecondCountableTopology A] : SigmaCompactSpace (GL (Fin 2) A) := by
  haveI := locallyCompactSpace_gl A
  haveI := secondCountableTopology_gl A
  exact sigmaCompactSpace_of_locallyCompact_secondCountable

private theorem secondCountableTopology_infiniteAdeleRing (K : Type) [Field K] [NumberField K] :
    SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ w : InfinitePlace K, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((w : InfinitePlace K) → w.Completion))

private theorem secondCountableTopology_archGL (K : Type) [Field K] [NumberField K] :
    SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing K)) := by
  haveI := secondCountableTopology_infiniteAdeleRing K
  exact secondCountableTopology_gl (InfiniteAdeleRing K)

private theorem continuous_ofFn_prod {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (n : ℕ) : Continuous fun c : Fin n → G => (List.ofFn c).prod := by
  simp only [List.ofFn_eq_map]
  exact continuous_list_prod _ fun i _ => continuous_apply i

private theorem continuous_fibrePoint {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (n : ℕ) (h : G) :
    Continuous fun c : Fin n → G => (Fin.snoc c ((List.ofFn c).prod⁻¹ * h) : Fin (n + 1) → G) := by
  refine continuous_pi fun j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.snoc_last]
    exact ((continuous_ofFn_prod n).inv).mul continuous_const
  · simp only [Fin.snoc_castSucc]
    exact continuous_apply i

private theorem sigmaCompactSpace_archGL (K : Type) [Field K] [NumberField K] :
    SigmaCompactSpace (GL (Fin 2) (InfiniteAdeleRing K)) := by
  haveI := secondCountableTopology_infiniteAdeleRing K
  exact sigmaCompactSpace_gl (InfiniteAdeleRing K)

private theorem fibreInt_exists_fd_transpose {X H : Type*} {M : Submodule ℂ (H → ℂ)}
    [FiniteDimensional ℂ M] (θ : X → H → ℂ) (hθ : ∀ x, θ x ∈ M) :
    ∃ W : Submodule ℂ (X → ℂ), FiniteDimensional ℂ W ∧ ∀ k : H, (fun x => θ x k) ∈ W := by
  classical
  let b := Module.finBasis ℂ M
  let Ψ : Fin (Module.finrank ℂ M) → X → ℂ := fun J x => b.repr ⟨θ x, hθ x⟩ J
  refine ⟨Submodule.span ℂ (Set.range Ψ), FiniteDimensional.span_of_finite ℂ (Set.finite_range Ψ),
    fun k => ?_⟩
  have hexp : (fun x => θ x k) = ∑ J, ((b J : H → ℂ) k) • Ψ J := by
    funext x
    have h1 : θ x k = ((∑ J, b.repr ⟨θ x, hθ x⟩ J • b J : M) : H → ℂ) k := by
      rw [b.sum_repr ⟨θ x, hθ x⟩]
    rw [h1, Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun J _ => ?_
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Ψ]
    ring
  rw [hexp]
  exact Submodule.sum_mem _ fun J _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨J, rfl⟩)

private theorem fibreInt_fd_span_range {X Y H : Type*} {S : Submodule ℂ (X → ℂ)}
    (I : S →ₗ[ℂ] (Y → ℂ)) {W : Submodule ℂ (X → ℂ)} [FiniteDimensional ℂ W]
    (Φ : H → X → ℂ) (hS : ∀ k, Φ k ∈ S) (hW : ∀ k, Φ k ∈ W) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => I ⟨Φ k, hS k⟩)) := by
  haveI : FiniteDimensional ℂ (S ⊓ W : Submodule ℂ (X → ℂ)) :=
    Submodule.finiteDimensional_of_le inf_le_right
  let J : (S ⊓ W : Submodule ℂ (X → ℂ)) →ₗ[ℂ] (Y → ℂ) := I ∘ₗ Submodule.inclusion inf_le_left
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range J) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  exact ⟨⟨Φ k, hS k, hW k⟩, rfl⟩

private def fibreInt_integrableSubmodule {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) (n : ℕ) :
    Submodule ℂ ((Fin (n + 1) → G) → ℂ) where
  carrier := {Ψ | ∀ h : G,
    Integrable (fun c : Fin n → G => Ψ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)))
      (Measure.pi fun _ => μ)}
  zero_mem' := fun _ => integrable_zero _ _ _
  add_mem' := fun ha hb h => (ha h).add (hb h)
  smul_mem' := fun r _ ha h => (ha h).smul r

private theorem fibreInt_mem_integrableSubmodule {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G} {n : ℕ}
    {Ψ : (Fin (n + 1) → G) → ℂ} :
    Ψ ∈ fibreInt_integrableSubmodule μ n ↔ ∀ h : G,
      Integrable (fun c : Fin n → G => Ψ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)))
        (Measure.pi fun _ => μ) :=
  Iff.rfl

private theorem fibreInt_integrable_slice {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G} {n : ℕ}
    (Ψ : fibreInt_integrableSubmodule μ n) (h : G) :
    Integrable
      (fun c : Fin n → G => (Ψ : (Fin (n + 1) → G) → ℂ) (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)))
      (Measure.pi fun _ => μ) :=
  fibreInt_mem_integrableSubmodule.1 Ψ.2 h

private noncomputable def fibreInt_linearMap {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) (n : ℕ) :
    fibreInt_integrableSubmodule μ n →ₗ[ℂ] (G → ℂ) where
  toFun := fun Ψ h =>
    ∫ c : Fin n → G, (Ψ : (Fin (n + 1) → G) → ℂ) (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h))
      ∂(Measure.pi fun _ => μ)
  map_add' := fun Ψ₁ Ψ₂ => funext fun h => by
    simp only [Submodule.coe_add, Pi.add_apply]
    exact integral_add (fibreInt_integrable_slice Ψ₁ h) (fibreInt_integrable_slice Ψ₂ h)
  map_smul' := fun r Ψ => funext fun h => by
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    exact integral_smul r _

private def fibreInt_slotHomeomorph {G : Type} [TopologicalSpace G] (n : ℕ) (i : Fin (n + 1)) (φ : G ≃ₜ G) :
    (Fin (n + 1) → G) ≃ₜ (Fin (n + 1) → G) where
  toFun x := Function.update x i (φ (x i))
  invFun x := Function.update x i (φ.symm (x i))
  left_inv := fun x => by simp
  right_inv := fun x => by simp
  continuous_toFun := continuous_id.update i (φ.continuous.comp (continuous_apply i))
  continuous_invFun := continuous_id.update i (φ.symm.continuous.comp (continuous_apply i))

private theorem fibreInt_mem_of_continuous {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ] {n : ℕ}
    {Ψ : (Fin (n + 1) → G) → ℂ} (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    Ψ ∈ fibreInt_integrableSubmodule μ n := by
  refine fibreInt_mem_integrableSubmodule.2 fun h => ?_
  have hcont : Continuous fun c : Fin n → G => Ψ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)) :=
    hΨ.comp (continuous_fibrePoint n h)
  have hinit : Continuous fun y : Fin (n + 1) → G => Fin.init y :=
    continuous_pi fun i => continuous_apply (Fin.castSucc i)

  have hsub : tsupport (fun c : Fin n → G => Ψ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h))) ⊆
      Fin.init '' tsupport Ψ := by
    refine (closure_minimal ?_
      ((isClosed_tsupport Ψ).preimage (continuous_fibrePoint n h))).trans ?_
    · intro c hc
      exact subset_tsupport Ψ hc
    · intro c hc
      exact ⟨Fin.snoc c (((List.ofFn c).prod)⁻¹ * h), hc, Fin.init_snoc _ _⟩
  have hsupp : HasCompactSupport fun c : Fin n → G =>
      Ψ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)) :=
    IsCompact.of_isClosed_subset (IsCompact.image hΨc hinit) (isClosed_tsupport _) hsub
  exact hcont.integrable_of_hasCompactSupport hsupp

private theorem fibreInt_slot_mem {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [SigmaFinite μ]
    [IsFiniteMeasureOnCompacts μ] {n : ℕ} {Φ : (Fin (n + 1) → G) → ℂ} (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) (i : Fin (n + 1)) (φ : G ≃ₜ G) :
    (fun x => Φ (Function.update x i (φ (x i)))) ∈ fibreInt_integrableSubmodule μ n :=
  fibreInt_mem_of_continuous μ (hΦ.comp (fibreInt_slotHomeomorph n i φ).continuous)
    (hΦc.comp_homeomorph (fibreInt_slotHomeomorph n i φ))

private theorem fibreInt_mul_left {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [SigmaFinite μ]
    [μ.IsMulLeftInvariant] {n : ℕ} (Φ : (Fin (n + 1) → G) → ℂ) (e h : G) :
    ∫ c : Fin n → G, Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * (e * h))) ∂(Measure.pi fun _ => μ) =
      ∫ c : Fin n → G,
        Φ (Function.update (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h) : Fin (n + 1) → G) 0
          (e * (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h) : Fin (n + 1) → G) 0))
        ∂(Measure.pi fun _ => μ) := by
  cases n with
  | zero =>
    congr 1
    funext c
    show Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * (e * h))) =
      Φ (Function.update (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h) : Fin (0 + 1) → G) (Fin.last 0)
        (e * (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h) : Fin (0 + 1) → G) (Fin.last 0)))
    have hp : (List.ofFn c).prod = 1 := by simp
    rw [Fin.snoc_last, Fin.update_snoc_last, hp, inv_one, one_mul, one_mul]
  | succ m =>
    have key : ∀ c : Fin (m + 1) → G,
        Φ (Function.update (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h) : Fin (m + 1 + 1) → G) 0
          (e * (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h) : Fin (m + 1 + 1) → G) 0)) =
        Φ (Fin.snoc (Pi.mulSingle (0 : Fin (m + 1)) e * c)
          (((List.ofFn (Pi.mulSingle (0 : Fin (m + 1)) e * c)).prod)⁻¹ * (e * h))) := by
      intro c
      congr 1
      have htail :
          (fun i : Fin m => (Pi.mulSingle (0 : Fin (m + 1)) e * c : Fin (m + 1) → G) i.succ) =
            fun i : Fin m => c i.succ := by
        funext i
        rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero i), one_mul]
      have hprod : (List.ofFn (Pi.mulSingle (0 : Fin (m + 1)) e * c)).prod =
          e * (List.ofFn c).prod := by
        rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Pi.mul_apply,
          Pi.mulSingle_eq_same, htail, mul_assoc]
      have hz : (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h) : Fin (m + 1 + 1) → G) 0 = c 0 := by
        show (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h) : Fin (m + 1 + 1) → G)
          (Fin.castSucc (0 : Fin (m + 1))) = c 0
        exact Fin.snoc_castSucc _ _ _
      have hl : (Fin.last (m + 1) : Fin (m + 1 + 1)) ≠ 0 := Fin.succ_ne_zero (Fin.last m)
      rw [hprod, mul_inv_rev, mul_assoc, inv_mul_cancel_left, hz]
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Function.update_of_ne hl, Fin.snoc_last, Fin.snoc_last]
      · rw [Fin.snoc_castSucc, Pi.mul_apply]
        rcases eq_or_ne i 0 with rfl | hi
        · rw [show (Fin.castSucc (0 : Fin (m + 1)) : Fin (m + 1 + 1)) = 0 from rfl,
            Function.update_self, Pi.mulSingle_eq_same]
        · have hci : (Fin.castSucc i : Fin (m + 1 + 1)) ≠ 0 := fun hc =>
            hi (Fin.ext (by simpa using congrArg Fin.val hc))
          rw [Function.update_of_ne hci, Fin.snoc_castSucc, Pi.mulSingle_eq_of_ne hi, one_mul]
    simp only [key]
    exact (integral_mul_left_eq_self
      (fun c' : Fin (m + 1) → G => Φ (Fin.snoc c' (((List.ofFn c').prod)⁻¹ * (e * h))))
      (Pi.mulSingle (0 : Fin (m + 1)) e)).symm

private theorem fibreInt_fd_rightTranslates {H : Type} {G : Type} [Group H] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ] {n : ℕ} (ι : H →* G)
    {Φ : (Fin (n + 1) → G) → ℂ} (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    {M : Submodule ℂ (H → ℂ)} [FiniteDimensional ℂ M]
    (hM : ∀ (x : Fin (n + 1) → G) (z : G),
      (fun k => Φ (Function.update x (Fin.last n) (z * ι k))) ∈ M)
    (f : G → ℂ)
    (hf : ∀ h, f h = ∫ c : Fin n → G, Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h))
      ∂(Measure.pi fun _ => μ)) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : H => fun x : G => f (x * ι k))) := by
  obtain ⟨W, hWfd, hW⟩ := fibreInt_exists_fd_transpose (M := M)
    (fun (x : Fin (n + 1) → G) (k : H) => Φ (Function.update x (Fin.last n) (x (Fin.last n) * ι k)))
    (fun x => hM x (x (Fin.last n)))
  have hgen : ∀ k : H,
      (fun x : Fin (n + 1) → G => Φ (Function.update x (Fin.last n) (x (Fin.last n) * ι k))) =
        fun x =>
          Φ (Function.update x (Fin.last n) (Homeomorph.mulRight (ι k) (x (Fin.last n)))) := by
    intro k
    simp only [Homeomorph.coe_mulRight]
  have hW' : ∀ k : H,
      (fun x : Fin (n + 1) → G =>
        Φ (Function.update x (Fin.last n) (Homeomorph.mulRight (ι k) (x (Fin.last n))))) ∈ W :=
    fun k => hgen k ▸ hW k
  have hS : ∀ k : H,
      (fun x : Fin (n + 1) → G =>
        Φ (Function.update x (Fin.last n) (Homeomorph.mulRight (ι k) (x (Fin.last n))))) ∈
          fibreInt_integrableSubmodule μ n :=
    fun k => fibreInt_slot_mem μ hΦ hΦc (Fin.last n) (Homeomorph.mulRight (ι k))
  haveI := hWfd
  have hfd := fibreInt_fd_span_range (fibreInt_linearMap μ n) (W := W) _ hS hW'
  have hfam : (fun k : H => fun x : G => f (x * ι k)) = fun k => fibreInt_linearMap μ n ⟨_, hS k⟩ := by
    funext k x
    change f (x * ι k) = ∫ c : Fin n → G,
      Φ (Function.update (Fin.snoc c (((List.ofFn c).prod)⁻¹ * x) : Fin (n + 1) → G) (Fin.last n)
        ((Fin.snoc c (((List.ofFn c).prod)⁻¹ * x) : Fin (n + 1) → G) (Fin.last n) * ι k))
        ∂(Measure.pi fun _ => μ)
    rw [hf]
    congr 1
    funext c
    rw [Fin.snoc_last, Fin.update_snoc_last, mul_assoc]
  rw [hfam]
  exact hfd

private theorem fibreInt_fd_rightTranslates_inv {H : Type} {G : Type} [Group H] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant] {n : ℕ}
    (ι : H →* G) {Φ : (Fin (n + 1) → G) → ℂ} (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    {M : Submodule ℂ (H → ℂ)} [FiniteDimensional ℂ M]
    (hM : ∀ (x : Fin (n + 1) → G) (z : G),
      (fun k => Φ (Function.update x 0 (z * ι k)⁻¹)) ∈ M)
    (f : G → ℂ)
    (hf : ∀ h, f h = ∫ c : Fin n → G, Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h))
      ∂(Measure.pi fun _ => μ)) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : H => fun x : G => f (x * ι k)⁻¹)) := by
  obtain ⟨W, hWfd, hW⟩ := fibreInt_exists_fd_transpose (M := M)
    (fun (x : Fin (n + 1) → G) (k : H) => Φ (Function.update x 0 ((x 0)⁻¹ * ι k)⁻¹))
    (fun x => hM x (x 0)⁻¹)
  have hgen : ∀ k : H,
      (fun x : Fin (n + 1) → G => Φ (Function.update x 0 ((x 0)⁻¹ * ι k)⁻¹)) =
        fun x => Φ (Function.update x 0 (Homeomorph.mulLeft (ι k)⁻¹ (x 0))) := by
    intro k
    simp only [mul_inv_rev, inv_inv, Homeomorph.coe_mulLeft]
  have hW' : ∀ k : H,
      (fun x : Fin (n + 1) → G => Φ (Function.update x 0 (Homeomorph.mulLeft (ι k)⁻¹ (x 0)))) ∈ W :=
    fun k => hgen k ▸ hW k
  have hS : ∀ k : H,
      (fun x : Fin (n + 1) → G => Φ (Function.update x 0 (Homeomorph.mulLeft (ι k)⁻¹ (x 0)))) ∈
        fibreInt_integrableSubmodule μ n :=
    fun k => fibreInt_slot_mem μ hΦ hΦc 0 (Homeomorph.mulLeft (ι k)⁻¹)
  haveI := hWfd
  have hfd :=
    fibreInt_fd_span_range (LinearMap.funLeft ℂ ℂ (fun x : G => x⁻¹) ∘ₗ fibreInt_linearMap μ n) (W := W) _ hS hW'
  have hfam : (fun k : H => fun x : G => f (x * ι k)⁻¹) =
      fun k => (LinearMap.funLeft ℂ ℂ (fun x : G => x⁻¹) ∘ₗ fibreInt_linearMap μ n) ⟨_, hS k⟩ := by
    funext k x
    change f (x * ι k)⁻¹ = ∫ c : Fin n → G,
      Φ (Function.update (Fin.snoc c (((List.ofFn c).prod)⁻¹ * x⁻¹) : Fin (n + 1) → G) 0
        ((ι k)⁻¹ * (Fin.snoc c (((List.ofFn c).prod)⁻¹ * x⁻¹) : Fin (n + 1) → G) 0))
        ∂(Measure.pi fun _ => μ)
    rw [mul_inv_rev, hf, fibreInt_mul_left μ Φ (ι k)⁻¹ x⁻¹]
  rw [hfam]
  exact hfd

private theorem fibreInt_archFactor_right
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    [BorelSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    (μ : Measure (GL (Fin 2) (InfiniteAdeleRing K))) [IsFiniteMeasureOnCompacts μ] {n : ℕ}
    (Φ : (Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K)) → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) (tys : AutomorphicForm.ArchTypeFamily K)
    (hn : ∀ x : Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K),
      (fun g => Φ (Function.update x (Fin.last n) g)) ∈
        AutomorphicForm.archFactorDualCutSubmodule K tys)
    (f : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (hf : ∀ h, f h = ∫ c : Fin n → GL (Fin 2) (InfiniteAdeleRing K),
      Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)) ∂(Measure.pi fun _ => μ))
    (w : InfinitePlace K) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      fun k : AutomorphicForm.rowIsometrySubgroup₀ w.Completion =>
        fun x : GL (Fin 2) (InfiniteAdeleRing K) =>
          f (x * AutomorphicForm.archRowIsometryInclAt₀ K w k))) := by
  haveI : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing K)) :=
    secondCountableTopology_archGL K
  haveI : SigmaCompactSpace (GL (Fin 2) (InfiniteAdeleRing K)) := sigmaCompactSpace_archGL K
  obtain ⟨M, hMfd, hM⟩ := typePiece_exists_fd_slices (AutomorphicForm.archRowIsometryInclAt₀ K w)
    (fun i : Fin (tys.card w) => Module.Dual ℂ (Fin (tys.rep w i).n → ℂ))
    (fun i => (tys.rep w i).ρ.dual)
  haveI := hMfd
  refine fibreInt_fd_rightTranslates μ (AutomorphicForm.archRowIsometryInclAt₀ K w) hΦ hΦc (M := M) ?_ f hf
  intro x z
  refine hM (fun g => Φ (Function.update x (Fin.last n) g)) ?_ z
  have hx := hn x
  rw [AutomorphicForm.archFactorDualCutSubmodule, Submodule.mem_iInf] at hx
  exact hx w

private theorem fibreInt_archFactor_left
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    [BorelSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    (μ : Measure (GL (Fin 2) (InfiniteAdeleRing K))) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] {n : ℕ}
    (Φ : (Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K)) → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) (tys : AutomorphicForm.ArchTypeFamily K)
    (h0 : ∀ x : Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K),
      (fun g => Φ (Function.update x 0 g⁻¹)) ∈ AutomorphicForm.archFactorCutSubmodule K tys)
    (f : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (hf : ∀ h, f h = ∫ c : Fin n → GL (Fin 2) (InfiniteAdeleRing K),
      Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)) ∂(Measure.pi fun _ => μ))
    (w : InfinitePlace K) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      fun k : AutomorphicForm.rowIsometrySubgroup₀ w.Completion =>
        fun x : GL (Fin 2) (InfiniteAdeleRing K) =>
          f (x * AutomorphicForm.archRowIsometryInclAt₀ K w k)⁻¹)) := by
  haveI : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing K)) :=
    secondCountableTopology_archGL K
  haveI : SigmaCompactSpace (GL (Fin 2) (InfiniteAdeleRing K)) := sigmaCompactSpace_archGL K
  obtain ⟨M, hMfd, hM⟩ := typePiece_exists_fd_slices (AutomorphicForm.archRowIsometryInclAt₀ K w)
    (fun i : Fin (tys.card w) => Fin (tys.rep w i).n → ℂ)
    (fun i => (tys.rep w i).ρ)
  haveI := hMfd
  refine fibreInt_fd_rightTranslates_inv μ (AutomorphicForm.archRowIsometryInclAt₀ K w) hΦ hΦc (M := M) ?_ f hf
  intro x z
  refine hM (fun g => Φ (Function.update x 0 g⁻¹)) ?_ z
  have hx := h0 x
  rw [AutomorphicForm.archFactorCutSubmodule, Submodule.mem_iInf] at hx
  exact hx w

theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    [BorelSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    (μ : Measure (GL (Fin 2) (InfiniteAdeleRing K))) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] {n : ℕ}
    (Φ : (Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K)) → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) (tys : AutomorphicForm.ArchTypeFamily K)
    (h0 : ∀ x : Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K),
      (fun g => Φ (Function.update x 0 g⁻¹)) ∈ AutomorphicForm.archFactorCutSubmodule K tys)
    (hn : ∀ x : Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K),
      (fun g => Φ (Function.update x (Fin.last n) g)) ∈
        AutomorphicForm.archFactorDualCutSubmodule K tys)
    (f : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (hf : ∀ h, f h = ∫ c : Fin n → GL (Fin 2) (InfiniteAdeleRing K),
      Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)) ∂(Measure.pi fun _ => μ)) :
    ∃ tysK : AutomorphicForm.ArchTypeFamily K, AutomorphicForm.IsArchFactorBiFinite K tysK f := by

  have hL : ∀ w : InfinitePlace K, ∃ (N : ℕ)
      (ρ : Representation ℂ (AutomorphicForm.rowIsometrySubgroup₀ w.Completion) (Fin N → ℂ)),
      (fun x => f x⁻¹) ∈
        AutomorphicForm.typeSubmodule (AutomorphicForm.archRowIsometryInclAt₀ K w) ρ :=
    fun w => typePiece_exists_rep_of_fd (AutomorphicForm.archRowIsometryInclAt₀ K w) (fun x => f x⁻¹)
      (fibreInt_archFactor_left K μ Φ hΦ hΦc tys h0 f hf w)

  have hR : ∀ w : InfinitePlace K, ∃ (N : ℕ)
      (ρ : Representation ℂ (AutomorphicForm.rowIsometrySubgroup₀ w.Completion) (Fin N → ℂ)),
      f ∈ AutomorphicForm.typeSubmodule (AutomorphicForm.archRowIsometryInclAt₀ K w) ρ.dual :=
    fun w => typePiece_exists_dual_rep_of_fd (AutomorphicForm.archRowIsometryInclAt₀ K w) f
      (fibreInt_archFactor_right K μ Φ hΦ hΦc tys hn f hf w)
  choose NL ρL hρL using hL
  choose NR ρR hρR using hR

  refine ⟨⟨fun _ => 2, fun w => ![⟨NL w, ρL w⟩, ⟨NR w, ρR w⟩]⟩, ?_, ?_⟩
  ·
    refine (Submodule.mem_iInf _).2 fun w => ?_
    show (fun x => f x⁻¹) ∈ ⨆ i : Fin 2, AutomorphicForm.archFactorTypeSubmoduleAt K w
      ((![⟨NL w, ρL w⟩, ⟨NR w, ρR w⟩] : Fin 2 → AutomorphicForm.ArchRepAt K w) i)
    exact Submodule.mem_iSup_of_mem (0 : Fin 2) (hρL w)
  ·
    refine (Submodule.mem_iInf _).2 fun w => ?_
    show f ∈ ⨆ i : Fin 2, AutomorphicForm.archFactorDualTypeSubmoduleAt K w
      ((![⟨NL w, ρL w⟩, ⟨NR w, ρR w⟩] : Fin 2 → AutomorphicForm.ArchRepAt K w) i)
    exact Submodule.mem_iSup_of_mem (1 : Fin 2) (hρR w)

end S_AutomorphicForm_exists_isArchFactorBiFinite_of_forall_eq_integral_snoc
end P2MW
export P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_of_forall_eq_integral_snoc (solution)
