-- Prove2me | solution 1 for AutomorphicForm.star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/4de9b7f4-e724-5c15-ae87-606ffef608c6

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_matrixCoeff_mem_iSup_typeSubmodule_and_matrixCoeff_inv_mem_iSup_typeSubmodule_dual_of_forall_mem_iSup_typeSubmodule_comp
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Matrix AutomorphicForm
open scoped ComplexConjugate

namespace KcConjType

namespace Alg

section TypePiece

variable {H G : Type*} [Group H] [Group G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem exists_out_mul_eq (ι : H →* G) (x : G) :
    ∃ k : H, (QuotientGroup.mk x : G ⧸ ι.range).out * ι k = x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ι.range x
  obtain ⟨k, hk⟩ := h.2
  exact ⟨k⁻¹, by rw [map_inv, hh, ← hk, mul_inv_cancel_right]⟩

noncomputable def cosetCoord (ι : H →* G) (x : G) : H :=
  (exists_out_mul_eq ι x).choose

theorem out_mul_cosetCoord (ι : H →* G) (x : G) :
    (QuotientGroup.mk x : G ⧸ ι.range).out * ι (cosetCoord ι x) = x :=
  (exists_out_mul_eq ι x).choose_spec

theorem cosetCoord_unique {ι : H →* G} (hι : Function.Injective ι) {x : G} {k : H}
    (hk : (QuotientGroup.mk x : G ⧸ ι.range).out * ι k = x) : k = cosetCoord ι x :=
  hι (mul_left_cancel (hk.trans (out_mul_cosetCoord ι x).symm))

theorem mk_mul_eq (ι : H →* G) (x : G) (k : H) :
    (QuotientGroup.mk (x * ι k) : G ⧸ ι.range) = QuotientGroup.mk x := by
  rw [QuotientGroup.eq]
  exact ⟨k⁻¹, by rw [map_inv, _root_.mul_inv_rev, inv_mul_cancel_right]⟩

theorem cosetCoord_mul {ι : H →* G} (hι : Function.Injective ι) (x : G) (k : H) :
    cosetCoord ι (x * ι k) = cosetCoord ι x * k := by
  symm
  apply cosetCoord_unique hι
  rw [mk_mul_eq, map_mul, ← mul_assoc, out_mul_cosetCoord]

theorem mem_typeSubmodule_of_isRightEquivariantOn {ι : H →* G} (hι : Function.Injective ι)
    (ρ : Representation ℂ H W) (P : Submodule ℂ W) (hP : ∀ (k : H), ∀ v ∈ P, ρ k v ∈ P)
    (S : P →ₗ[ℂ] (G → ℂ))
    (hS : ∀ (k : H) (v : P) (x : G), S ⟨ρ k v, hP k v v.2⟩ x = S v (x * ι k)) (v : P) :
    S v ∈ AutomorphicForm.typeSubmodule ι ρ := by
  classical
  let ℓ : G ⧸ ι.range → (P →ₗ[ℂ] ℂ) := fun c =>
    { toFun := fun p => S p c.out
      map_add' := fun p q => by rw [map_add]; rfl
      map_smul' := fun a p => by rw [map_smul]; rfl }
  have hext : ∀ c, ∃ g : W →ₗ[ℂ] ℂ, g.comp P.subtype = ℓ c := fun c => LinearMap.exists_extend (ℓ c)
  let ℓ' : G ⧸ ι.range → (W →ₗ[ℂ] ℂ) := fun c => (hext c).choose
  have hℓ' : ∀ c (p : P), ℓ' c (p : W) = S p c.out := fun c p => by
    have := LinearMap.congr_fun (hext c).choose_spec p
    simpa [ℓ] using this
  let T : W →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun w x => ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) w)
      map_add' := fun w₁ w₂ => funext fun x => by simp only [map_add, Pi.add_apply]
      map_smul' := fun a w => funext fun x => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }
  have hT : AutomorphicForm.IsRightEquivariant ι ρ T := by
    intro k w x
    show ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) (ρ k w)) =
      ℓ' (QuotientGroup.mk (x * ι k)) (ρ (cosetCoord ι (x * ι k)) w)
    rw [mk_mul_eq, cosetCoord_mul hι, map_mul]
    rfl
  have hTS : T (v : W) = S v := by
    funext x
    show ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) (v : W)) = S v x
    have hmem : ρ (cosetCoord ι x) (v : W) ∈ P := hP _ _ v.2
    have h1 := hℓ' (QuotientGroup.mk x) ⟨_, hmem⟩
    simp only at h1
    rw [h1, hS (cosetCoord ι x) v, out_mul_cosetCoord]
  rw [← hTS]
  exact AutomorphicForm.mem_typeSubmodule_of_isRightEquivariant hT _

end TypePiece

section PiRep

variable {H : Type*} [Group H]
variable {A : Type*} {W : A → Type*} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)]

def piRep (ρ : ∀ a, Representation ℂ H (W a)) : Representation ℂ H (∀ a, W a) where
  toFun k := LinearMap.pi fun a => (ρ a k).comp (LinearMap.proj a)
  map_one' := by
    ext v a
    simp
  map_mul' k₁ k₂ := by
    ext v a
    simp

theorem piRep_apply (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (v : ∀ a, W a) (a : A) :
    piRep ρ k v a = ρ a k (v a) :=
  rfl

theorem piRep_single [DecidableEq A] (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (a : A)
    (v : W a) : piRep ρ k (Pi.single a v) = Pi.single a (ρ a k v) := by
  funext b
  rw [piRep_apply]
  by_cases hb : b = a
  · subst hb
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne hb, map_zero]

end PiRep

section Transport

variable {H G : Type*} [Group H] [Group G]

theorem typeSubmodule_piRep_le {A : Type*} [Fintype A] [DecidableEq A] {W : A → Type*}
    [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)] (ι : H →* G)
    (ρ : ∀ a, Representation ℂ H (W a)) :
    typeSubmodule ι (piRep ρ) ≤ ⨆ a, typeSubmodule ι (ρ a) := by
  refine Submodule.span_le.mpr ?_
  rintro f ⟨T, hT, v, rfl⟩
  show T v ∈ ⨆ a, typeSubmodule ι (ρ a)
  rw [← Finset.univ_sum_single v, map_sum]
  refine Submodule.sum_mem _ fun a _ => Submodule.mem_iSup_of_mem a ?_
  have hTa : IsRightEquivariant ι (ρ a) (T.comp (LinearMap.single ℂ W a)) := by
    intro k w x
    show T (Pi.single a (ρ a k w)) x = T (Pi.single a w) (x * ι k)
    rw [← piRep_single]
    exact hT k (Pi.single a w) x
  exact mem_typeSubmodule_of_isRightEquivariant hTa (v a)

theorem mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi {A : Type*} [Fintype A] [DecidableEq A]
    {W : A → Type*} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)] {ι : H →* G}
    (hι : Function.Injective ι) (ρ : ∀ a, Representation ℂ H (W a)) (Q : Submodule ℂ (∀ a, W a))
    (hQ : ∀ (k : H), ∀ v ∈ Q, piRep ρ k v ∈ Q) (S : Q →ₗ[ℂ] (G → ℂ))
    (hS : ∀ (k : H) (v : Q) (x : G), S ⟨piRep ρ k v, hQ k v v.2⟩ x = S v (x * ι k)) (v : Q) :
    S v ∈ ⨆ a, typeSubmodule ι (ρ a) :=
  typeSubmodule_piRep_le ι ρ (mem_typeSubmodule_of_isRightEquivariantOn hι (piRep ρ) Q hQ S hS v)

theorem exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule {J : Type*} {W : J → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)] (ι : H →* G)
    (ρ : ∀ j, Representation ℂ H (W j)) {θ : G → ℂ} (hθ : θ ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    ∃ (t : Finset (G → ℂ)) (i : t → J) (Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ)),
      IsRightEquivariant ι (piRep fun a => ρ (i a)) Φ ∧ θ ∈ LinearMap.range Φ := by
  classical
  have h1 : θ ∈ Submodule.span ℂ
      (⋃ j, {f : G → ℂ | ∃ T : W j →ₗ[ℂ] (G → ℂ),
        IsRightEquivariant ι (ρ j) T ∧ f ∈ LinearMap.range T}) := by
    rw [Submodule.span_iUnion]
    exact hθ
  obtain ⟨t, ht, hθt⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hgen : ∀ f : t, ∃ j : J, ∃ T : W j →ₗ[ℂ] (G → ℂ),
      IsRightEquivariant ι (ρ j) T ∧ (f : G → ℂ) ∈ LinearMap.range T := fun f => by
    have hf := ht f.2
    rw [Set.mem_iUnion] at hf
    obtain ⟨j, T, hT, hfT⟩ := hf
    exact ⟨j, T, hT, hfT⟩
  choose i T hT hfT using hgen
  let Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ) := ∑ a : t, (T a).comp (LinearMap.proj a)
  have hΦ : ∀ w : ∀ a : t, W (i a), Φ w = ∑ a : t, T a (w a) := fun w => by
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  refine ⟨t, i, Φ, ?_, ?_⟩
  · intro k w x
    rw [hΦ, hΦ, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => hT a k (w a) x
  · refine (Submodule.span_le.mpr ?_) hθt
    intro f hf
    obtain ⟨v, hv⟩ := hfT ⟨f, hf⟩
    refine ⟨Pi.single (⟨f, hf⟩ : t) v, ?_⟩
    rw [hΦ, Finset.sum_eq_single (⟨f, hf⟩ : t)]
    · rw [Pi.single_eq_same]
      exact hv
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, map_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem mem_iSup_typeSubmodule_of_intertwines {G' : Type*} [Group G'] {J : Type*} {W : J → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)] (ι : H →* G) {ι' : H →* G'}
    (hι' : Function.Injective ι') (ρ : ∀ j, Representation ℂ H (W j)) (P₀ : Submodule ℂ (G → ℂ))
    (hP₀ : ∀ (k : H), ∀ θ ∈ P₀, (fun x => θ (x * ι k)) ∈ P₀) (A : P₀ →ₗ[ℂ] (G' → ℂ))
    (hA : ∀ (k : H) (θ : P₀) (y : G'), A ⟨fun x => (θ : G → ℂ) (x * ι k), hP₀ k θ θ.2⟩ y =
      A θ (y * ι' k))
    (θ : P₀) (hθ : (θ : G → ℂ) ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    A θ ∈ ⨆ j, typeSubmodule ι' (ρ j) := by
  classical
  obtain ⟨t, i, Φ, hΦ, v, hv⟩ :=
    exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule ι ρ hθ
  have hQ : ∀ (k : H), ∀ w ∈ P₀.comap Φ, piRep (fun a => ρ (i a)) k w ∈ P₀.comap Φ := by
    intro k w hw
    rw [Submodule.mem_comap] at hw ⊢
    have hw' : Φ (piRep (fun a => ρ (i a)) k w) = fun x => Φ w (x * ι k) :=
      funext fun x => hΦ k w x
    rw [hw']
    exact hP₀ k _ hw
  let ΦQ : P₀.comap Φ →ₗ[ℂ] P₀ :=
    LinearMap.codRestrict P₀ (Φ.comp (P₀.comap Φ).subtype) fun w => w.2
  let S : P₀.comap Φ →ₗ[ℂ] (G' → ℂ) := A.comp ΦQ
  have hS : ∀ (k : H) (w : P₀.comap Φ) (y : G'),
      S ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ y = S w (y * ι' k) := by
    intro k w y
    have h1 : ΦQ ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ =
        ⟨fun x => ((ΦQ w : P₀) : G → ℂ) (x * ι k), hP₀ k _ (ΦQ w).2⟩ := by
      apply Subtype.ext
      funext x
      exact hΦ k w x
    show A (ΦQ ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩) y = A (ΦQ w) (y * ι' k)
    rw [h1]
    exact hA k (ΦQ w) y
  have hv' : v ∈ P₀.comap Φ := by
    rw [Submodule.mem_comap, hv]
    exact θ.2
  have hmem := mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi hι' (fun a => ρ (i a)) (P₀.comap Φ)
    hQ S hS ⟨v, hv'⟩
  have hSv : S ⟨v, hv'⟩ = A θ := by
    show A (ΦQ ⟨v, hv'⟩) = A θ
    congr 1
    exact Subtype.ext hv
  rw [hSv] at hmem
  exact (iSup_le fun a => le_iSup (fun j => typeSubmodule ι' (ρ j)) (i a)) hmem

end Transport

end Alg

section Delta

variable {G : Type*} [Group G]
variable {Kc : Type*} [Group Kc] [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc]
  [MeasurableSpace Kc] [BorelSpace Kc]
variable (μ : Measure Kc) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] [μ.IsMulRightInvariant]
variable (ι : Kc →* G) (E : Submodule ℂ (G → ℂ))
variable (hE : ∀ (κ : Kc), ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E)

def piE (κ : Kc) : E →ₗ[ℂ] E where
  toFun v := ⟨fun x => (v : G → ℂ) (x * ι κ), hE κ v v.2⟩
  map_add' v w := by ext x; rfl
  map_smul' c v := by ext x; rfl

theorem piE_apply (κ : Kc) (v : E) (x : G) : (piE ι E hE κ v : G → ℂ) x = (v : G → ℂ) (x * ι κ) := rfl

theorem piE_one : piE ι E hE 1 = LinearMap.id := by
  ext v x
  show (v : G → ℂ) (x * ι 1) = (v : G → ℂ) x
  rw [map_one, mul_one]

theorem piE_mul (κ κ' : Kc) : piE ι E hE (κ * κ') = piE ι E hE κ ∘ₗ piE ι E hE κ' := by
  ext v x
  show (v : G → ℂ) (x * ι (κ * κ')) = (v : G → ℂ) (x * ι κ * ι κ')
  rw [map_mul, mul_assoc]

variable [FiniteDimensional ℂ E]

def Pm (κ : Kc) : Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ :=
  LinearMap.toMatrix (Module.finBasis ℂ E) (Module.finBasis ℂ E) (piE ι E hE κ)

theorem Pm_one : Pm ι E hE 1 = 1 := by
  rw [Pm, piE_one, LinearMap.toMatrix_id]

theorem Pm_mul (κ κ' : Kc) : Pm ι E hE (κ * κ') = Pm ι E hE κ * Pm ι E hE κ' := by
  rw [Pm, piE_mul, LinearMap.toMatrix_comp (Module.finBasis ℂ E) (Module.finBasis ℂ E)]
  rfl

theorem Pm_inv_mul (κ : Kc) : Pm ι E hE κ⁻¹ * Pm ι E hE κ = 1 := by
  rw [← Pm_mul, inv_mul_cancel, Pm_one]

theorem Pm_mul_inv (κ : Kc) : Pm ι E hE κ * Pm ι E hE κ⁻¹ = 1 := by
  rw [← Pm_mul, mul_inv_cancel, Pm_one]

theorem continuous_Pm_apply (hcont : ∀ v ∈ E, ∀ x : G, Continuous fun κ : Kc => v (x * ι κ))
    (i j : Fin (Module.finrank ℂ E)) : Continuous fun κ => Pm ι E hE κ i j := by
  let b := Module.finBasis ℂ E
  have h1 : Continuous fun κ : Kc => (piE ι E hE κ (b j) : E) := by
    refine continuous_induced_rng.mpr ?_
    refine continuous_pi fun x => ?_
    exact hcont _ (b j).2 x
  have h2 : Continuous (b.coord i : E →ₗ[ℂ] ℂ) := LinearMap.continuous_of_finiteDimensional _
  have h3 : (fun κ => Pm ι E hE κ i j) = fun κ => b.coord i (piE ι E hE κ (b j)) := by
    funext κ
    rw [Pm, LinearMap.toMatrix_apply]
    rfl
  rw [h3]
  exact h2.comp h1

theorem continuous_Pm (hcont : ∀ v ∈ E, ∀ x : G, Continuous fun κ : Kc => v (x * ι κ)) :
    Continuous fun κ => Pm ι E hE κ :=
  continuous_pi fun i => continuous_pi fun j => continuous_Pm_apply ι E hE hcont i j

section Mint

variable {m : Type*} [Fintype m] [DecidableEq m]

def Mint (Φ : Kc → Matrix m m ℂ) : Matrix m m ℂ := Matrix.of fun i j => ∫ κ, Φ κ i j ∂μ

theorem Mint_apply (Φ : Kc → Matrix m m ℂ) (i j : m) : Mint μ Φ i j = ∫ κ, Φ κ i j ∂μ := rfl

theorem hasCompactSupport_of_compactSpace {α : Type*} [Zero α] [TopologicalSpace α] (h : Kc → α) :
    HasCompactSupport h :=
  IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport h) (Set.subset_univ _)

theorem integrable_of_continuous {h : Kc → ℂ} (hh : Continuous h) : Integrable h μ :=
  hh.integrable_of_hasCompactSupport (hasCompactSupport_of_compactSpace h)

theorem continuous_apply_apply_of_continuous {Φ : Kc → Matrix m m ℂ} (hΦ : Continuous Φ) (i j : m) :
    Continuous fun κ => Φ κ i j :=
  (continuous_apply j).comp ((continuous_apply i).comp hΦ)

theorem Mint_const_mul (A : Matrix m m ℂ) {Φ : Kc → Matrix m m ℂ} (hΦ : Continuous Φ) :
    Mint μ (fun κ => A * Φ κ) = A * Mint μ Φ := by
  ext i j
  rw [Mint_apply, Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Mint_apply]
  rw [integral_finsetSum _ fun k _ => (integrable_of_continuous μ
    (continuous_apply_apply_of_continuous hΦ k j)).const_mul (A i k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact integral_const_mul _ _

theorem Mint_mul_const (A : Matrix m m ℂ) {Φ : Kc → Matrix m m ℂ} (hΦ : Continuous Φ) :
    Mint μ (fun κ => Φ κ * A) = Mint μ Φ * A := by
  ext i j
  rw [Mint_apply, Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Mint_apply]
  rw [integral_finsetSum _ fun k _ => (integrable_of_continuous μ
    (continuous_apply_apply_of_continuous hΦ i k)).mul_const (A k j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact integral_mul_const _ _

theorem Mint_mul_right (Φ : Kc → Matrix m m ℂ) (k : Kc) :
    Mint μ (fun κ => Φ (κ * k)) = Mint μ Φ := by
  ext i j
  rw [Mint_apply, Mint_apply]
  exact integral_mul_right_eq_self (fun κ => Φ κ i j) k

theorem dotProduct_Mint_mulVec (x y : m → ℂ) {Φ : Kc → Matrix m m ℂ} (hΦ : Continuous Φ) :
    x ⬝ᵥ (Mint μ Φ *ᵥ y) = ∫ κ, x ⬝ᵥ (Φ κ *ᵥ y) ∂μ := by
  have hI : ∀ i j, Integrable (fun κ => Φ κ i j) μ := fun i j =>
    integrable_of_continuous μ (continuous_apply_apply_of_continuous hΦ i j)
  simp only [dotProduct, Matrix.mulVec, Mint_apply, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((hI i j).mul_const _).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => ((hI i j).mul_const _).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc x i * ((∫ κ, Φ κ i j ∂μ) * y j) = x i * ∫ κ, Φ κ i j * y j ∂μ := by
        rw [show (∫ κ, Φ κ i j * y j ∂μ) = (∫ κ, Φ κ i j ∂μ) * y j from integral_mul_const _ _]
    _ = ∫ κ, x i * (Φ κ i j * y j) ∂μ := (integral_const_mul _ _).symm

end Mint

variable (hcont : ∀ v ∈ E, ∀ x : G, Continuous fun κ : Kc => v (x * ι κ))

def Hm : Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ :=
  Mint μ fun κ => (Pm ι E hE κ)ᴴ * Pm ι E hE κ

include hcont in
theorem continuous_PHP : Continuous fun κ => (Pm ι E hE κ)ᴴ * Pm ι E hE κ :=
  ((continuous_Pm ι E hE hcont).matrix_conjTranspose).mul (continuous_Pm ι E hE hcont)

include hcont in
theorem conjTranspose_mul_Hm_mul (k : Kc) :
    (Pm ι E hE k)ᴴ * Hm μ ι E hE * Pm ι E hE k = Hm μ ι E hE := by
  have hΦ := continuous_PHP ι E hE hcont
  have e1 : (Pm ι E hE k)ᴴ * Hm μ ι E hE = Mint μ (fun κ => (Pm ι E hE k)ᴴ * ((Pm ι E hE κ)ᴴ * Pm ι E hE κ)) :=
    (Mint_const_mul μ _ hΦ).symm
  have e2 : Mint μ (fun κ => (Pm ι E hE k)ᴴ * ((Pm ι E hE κ)ᴴ * Pm ι E hE κ)) * Pm ι E hE k =
      Mint μ (fun κ => (Pm ι E hE k)ᴴ * ((Pm ι E hE κ)ᴴ * Pm ι E hE κ) * Pm ι E hE k) :=
    (Mint_mul_const μ _ (continuous_const.mul hΦ)).symm
  have e3 : (fun κ => (Pm ι E hE k)ᴴ * ((Pm ι E hE κ)ᴴ * Pm ι E hE κ) * Pm ι E hE k) =
      fun κ => (Pm ι E hE (κ * k))ᴴ * Pm ι E hE (κ * k) := by
    funext κ
    rw [Pm_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [e1, e2, e3, Mint_mul_right μ (fun κ => (Pm ι E hE κ)ᴴ * Pm ι E hE κ) k, Hm]

theorem star_dotProduct_conjTranspose_mul_mulVec {m : Type*} [Fintype m] (A : Matrix m m ℂ) (x : m → ℂ) :
    star x ⬝ᵥ ((Aᴴ * A) *ᵥ x) = ∑ i, (Complex.normSq ((A *ᵥ x) i) : ℂ) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
  rw [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.normSq_eq_conj_mul_self]

include hcont in
theorem Hm_mulVec_injective : Function.Injective (Hm μ ι E hE).mulVec := by
  intro x y hxy
  rw [← sub_eq_zero]
  set z := x - y with hz
  have hz0 : (Hm μ ι E hE) *ᵥ z = 0 := by rw [hz, Matrix.mulVec_sub, hxy, sub_self]
  by_contra hne

  let q : Kc → ℝ := fun κ => ∑ i, Complex.normSq ((Pm ι E hE κ *ᵥ z) i)
  have hq_cont : Continuous q := by
    refine continuous_finsetSum _ fun i _ => Complex.continuous_normSq.comp ?_
    exact (continuous_apply i).comp
      ((continuous_Pm ι E hE hcont).matrix_mulVec continuous_const)
  have hq_nonneg : ∀ κ, 0 ≤ q κ := fun κ => Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hq_one : q 1 ≠ 0 := by
    intro h0
    apply hne
    have h1 : ∀ i, Complex.normSq ((Pm ι E hE 1 *ᵥ z) i) = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).mp h0 i (Finset.mem_univ i)
    funext i
    have := h1 i
    rw [Pm_one, Matrix.one_mulVec, Complex.normSq_eq_zero] at this
    exact this
  have hpos : 0 < ∫ κ, q κ ∂μ :=
    hq_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero (hasCompactSupport_of_compactSpace q)
      hq_nonneg hq_one

  have hform : star z ⬝ᵥ ((Hm μ ι E hE) *ᵥ z) = ((∫ κ, q κ ∂μ : ℝ) : ℂ) := by
    rw [Hm, dotProduct_Mint_mulVec μ _ _ (continuous_PHP ι E hE hcont), ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    show star z ⬝ᵥ (((Pm ι E hE κ)ᴴ * Pm ι E hE κ) *ᵥ z) = ((q κ : ℝ) : ℂ)
    rw [star_dotProduct_conjTranspose_mul_mulVec]
    show _ = ((∑ i, Complex.normSq ((Pm ι E hE κ *ᵥ z) i) : ℝ) : ℂ)
    rw [Complex.ofReal_sum]
  rw [hz0, dotProduct_zero] at hform
  have : (∫ κ, q κ ∂μ) = 0 := by exact_mod_cast hform.symm
  exact (lt_irrefl _) (this ▸ hpos)

include hcont in
theorem isUnit_Hm_det : IsUnit (Hm μ ι E hE).det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  exact Matrix.mulVec_injective_iff_isUnit.mp (Hm_mulVec_injective μ ι E hE hcont)

include hcont in
theorem conjTranspose_Pm (k : Kc) :
    (Pm ι E hE k)ᴴ = Hm μ ι E hE * Pm ι E hE k⁻¹ * (Hm μ ι E hE)⁻¹ := by
  have h1 : (Pm ι E hE k)ᴴ * Hm μ ι E hE = Hm μ ι E hE * Pm ι E hE k⁻¹ := by
    have h := conjTranspose_mul_Hm_mul μ ι E hE hcont k
    calc (Pm ι E hE k)ᴴ * Hm μ ι E hE
        = (Pm ι E hE k)ᴴ * Hm μ ι E hE * (Pm ι E hE k * Pm ι E hE k⁻¹) := by
          rw [Pm_mul_inv, Matrix.mul_one]
      _ = Hm μ ι E hE * Pm ι E hE k⁻¹ := by rw [← Matrix.mul_assoc, h]
  rw [← h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_Hm_det μ ι E hE hcont), Matrix.mul_one]

end Delta

section Coeff

variable {G : Type*} [Group G] {Kw Kc : Type*} [Group Kw] [Group Kc]
variable (ι : Kc →* G) (E : Submodule ℂ (G → ℂ))
variable (hE : ∀ (κ : Kc), ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E) [FiniteDimensional ℂ E]

theorem Pm_apply_eq_coord (κ : Kc) (i j : Fin (Module.finrank ℂ E)) :
    Pm ι E hE κ i j =
      (Module.finBasis ℂ E).coord i
        ⟨fun x => (((Module.finBasis ℂ E) j : E) : G → ℂ) (x * ι κ), hE κ _ ((Module.finBasis ℂ E) j).2⟩ := by
  rw [Pm, LinearMap.toMatrix_apply]
  rfl

variable {J : Type*} {W : J → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
variable {incl : Kw →* Kc} (hincl : Function.Injective incl) (ρ : ∀ j, Representation ℂ Kw (W j))
variable (hEcut : ∀ v ∈ E, v ∈ ⨆ j, typeSubmodule (ι.comp incl) (ρ j))

include hincl hEcut in
theorem Pm_inv_entry_mem_iSup (i j : Fin (Module.finrank ℂ E)) :
    (fun κ => Pm ι E hE κ⁻¹ i j) ∈ ⨆ j', typeSubmodule incl (ρ j').dual := by
  have h : (fun κ => Pm ι E hE κ⁻¹ i j) = fun κ => (Module.finBasis ℂ E).coord i
      ⟨fun x => (((Module.finBasis ℂ E) j : E) : G → ℂ) (x * ι κ⁻¹), hE κ⁻¹ _ ((Module.finBasis ℂ E) j).2⟩ :=
    funext fun κ => Pm_apply_eq_coord ι E hE κ⁻¹ i j
  rw [h]
  exact (matrixCoeff_mem_iSup_typeSubmodule_and_matrixCoeff_inv_mem_iSup_typeSubmodule_dual_of_forall_mem_iSup_typeSubmodule_comp
    ι incl hincl E hE ρ hEcut ((Module.finBasis ℂ E).coord i) ((Module.finBasis ℂ E) j)).2

end Coeff

section DualDual

variable {H G : Type*} [Group H] [Group G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem dual_dual_apply_eval (ρ : Representation ℂ H W) (k : H) (w : W) :
    ρ.dual.dual k (Module.Dual.eval ℂ W w) = Module.Dual.eval ℂ W (ρ k w) := by
  apply LinearMap.ext
  intro φ
  simp only [Representation.dual_apply, inv_inv]
  rfl

theorem typeSubmodule_dual_dual_le (ι : H →* G) (ρ : Representation ℂ H W) :
    typeSubmodule ι ρ.dual.dual ≤ typeSubmodule ι ρ := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨T, hT, Φ, rfl⟩
  let T' : W →ₗ[ℂ] (G → ℂ) := T ∘ₗ (Module.evalEquiv ℂ W : W →ₗ[ℂ] Module.Dual ℂ (Module.Dual ℂ W))
  have hT' : IsRightEquivariant ι ρ T' := by
    intro k v x
    show T (Module.evalEquiv ℂ W (ρ k v)) x = T (Module.evalEquiv ℂ W v) (x * ι k)
    rw [Module.evalEquiv_apply, Module.evalEquiv_apply, ← dual_dual_apply_eval]
    exact hT k _ x
  have h : T Φ = T' ((Module.evalEquiv ℂ W).symm Φ) := by
    show T Φ = T (Module.evalEquiv ℂ W ((Module.evalEquiv ℂ W).symm Φ))
    rw [LinearEquiv.apply_symm_apply]
  show T Φ ∈ typeSubmodule ι ρ
  rw [h]
  exact mem_typeSubmodule_of_isRightEquivariant hT' _

end DualDual

section Engine

variable {G : Type*} [Group G]
variable {Kc : Type*} [Group Kc] [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc]
  [MeasurableSpace Kc] [BorelSpace Kc]

theorem star_mem_iSup_typeSubmodule_dual
    (μ : Measure Kc) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] [μ.IsMulRightInvariant]
    (ι : Kc →* G) (hι : Function.Injective ι)
    {J : Type*} {W : J → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    [∀ j, FiniteDimensional ℂ (W j)]
    (ρ : ∀ j, Representation ℂ Kc (W j))
    (f : G → ℂ) (hfc : ∀ x : G, Continuous fun κ : Kc => f (x * ι κ))
    (hf : f ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    (fun x => conj (f x)) ∈ ⨆ j, typeSubmodule ι (ρ j).dual := by
  classical

  let gen : Kc → (G → ℂ) := fun κ x => f (x * ι κ)
  let E : Submodule ℂ (G → ℂ) := Submodule.span ℂ (Set.range gen)
  let Rt : Kc → (G → ℂ) →ₗ[ℂ] (G → ℂ) := fun κ =>
    { toFun := fun g x => g (x * ι κ)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hRgen : ∀ κ κ', Rt κ (gen κ') = gen (κ * κ') := by
    intro κ κ'
    funext x
    show f (x * ι κ * ι κ') = f (x * ι (κ * κ'))
    rw [map_mul, mul_assoc]
  have hE : ∀ (κ : Kc), ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E := by
    intro κ v hv
    have hle : Submodule.map (Rt κ) E ≤ E := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨_, ⟨κ', rfl⟩, rfl⟩
      exact ⟨κ * κ', (hRgen κ κ').symm⟩
    exact hle (Submodule.mem_map_of_mem hv)
  have hEc : ∀ v ∈ E, ∀ x : G, Continuous fun κ : Kc => v (x * ι κ) := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => ∀ x : G, Continuous fun κ : Kc => v (x * ι κ))
      ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨κ', rfl⟩ x
      have h : (fun κ : Kc => gen κ' (x * ι κ)) = fun κ => f (x * ι (κ * κ')) := by
        funext κ
        show f (x * ι κ * ι κ') = f (x * ι (κ * κ'))
        rw [map_mul, mul_assoc]
      rw [h]
      exact (hfc x).comp (continuous_id.mul continuous_const)
    · intro x
      exact continuous_const
    · intro u w _ _ hu hw x
      exact (hu x).add (hw x)
    · intro c u _ hu x
      exact (hu x).const_smul c

  obtain ⟨t, i, Φ, hΦ, v₀, hv₀⟩ := Alg.exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule ι ρ hf
  have hEle : E ≤ LinearMap.range Φ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨κ, rfl⟩
    refine ⟨Alg.piRep (fun a => ρ (i a)) κ v₀, ?_⟩
    funext x
    rw [hΦ κ v₀ x, hv₀]
  haveI : FiniteDimensional ℂ (LinearMap.range Φ) := LinearMap.finiteDimensional_range Φ
  haveI : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le hEle
  have hrange_le : LinearMap.range Φ ≤ ⨆ j, typeSubmodule ι (ρ j) := by
    rintro _ ⟨w, rfl⟩
    have h1 : Φ w ∈ typeSubmodule ι (Alg.piRep fun a => ρ (i a)) := mem_typeSubmodule_of_isRightEquivariant hΦ w
    have h2 := Alg.typeSubmodule_piRep_le ι (fun a => ρ (i a)) h1
    exact (iSup_le fun a => le_iSup (fun j => typeSubmodule ι (ρ j)) (i a)) h2
  have hEcut : ∀ v ∈ E, v ∈ ⨆ j, typeSubmodule (ι.comp (MonoidHom.id Kc)) (ρ j) := by
    intro v hv
    rw [MonoidHom.comp_id]
    exact hrange_le (hEle hv)
  have hid : Function.Injective (MonoidHom.id Kc) := fun _ _ h => h

  let Bs := Module.finBasis ℂ E
  let e : Fin (Module.finrank ℂ E) → (G → ℂ) := fun p => ((Bs p : E) : G → ℂ)
  let P : Kc → Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ := fun κ => Pm ι E hE κ
  have hexp : ∀ (κ : Kc) (q : Fin (Module.finrank ℂ E)) (x : G),
      e q (x * ι κ) = ∑ p, P κ p q * e p x := by
    intro κ q x
    have hsum : piE ι E hE κ (Bs q) = ∑ p, P κ p q • Bs p := by
      conv_lhs => rw [← Bs.sum_repr (piE ι E hE κ (Bs q))]
      refine Finset.sum_congr rfl fun p _ => ?_
      congr 1
      show Bs.repr (piE ι E hE κ (Bs q)) p = LinearMap.toMatrix Bs Bs (piE ι E hE κ) p q
      rw [LinearMap.toMatrix_apply]
    have h := congrArg (fun v : E => (v : G → ℂ) x) hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h

  set Hm₀ := Hm μ ι E hE with hHm₀
  have hconjP : ∀ (κ : Kc) (p q : Fin (Module.finrank ℂ E)),
      conj (P κ p q) = ∑ b, ∑ a, Hm₀ q a * P κ⁻¹ a b * Hm₀⁻¹ b p := by
    intro κ p q
    have h1 : conj (P κ p q) = (P κ)ᴴ q p := by
      rw [Matrix.conjTranspose_apply, Complex.star_def]
    rw [h1, show (P κ)ᴴ = Hm₀ * P κ⁻¹ * Hm₀⁻¹ from conjTranspose_Pm μ ι E hE hEc κ, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]

  have hcoef : ∀ a b : Fin (Module.finrank ℂ E),
      (fun κ => P κ⁻¹ a b) ∈ ⨆ j, typeSubmodule (MonoidHom.id Kc) (ρ j).dual :=
    fun a b => Pm_inv_entry_mem_iSup ι E hE hid ρ hEcut a b
  have hc : ∀ p q : Fin (Module.finrank ℂ E),
      (fun κ => conj (P κ p q)) ∈ ⨆ j, typeSubmodule (MonoidHom.id Kc) (ρ j).dual := by
    intro p q
    have h : (fun κ => conj (P κ p q)) =
        ∑ b, ∑ a, (Hm₀ q a * Hm₀⁻¹ b p) • fun κ => P κ⁻¹ a b := by
      funext κ
      rw [hconjP κ p q, Finset.sum_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [h]
    exact Submodule.sum_mem _ fun b _ => Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hcoef a b)

  let rep : G → G := fun g => (QuotientGroup.mk g : G ⧸ ι.range).out
  let crd : G → Kc := Alg.cosetCoord ι
  have hdec : ∀ g, rep g * ι (crd g) = g := Alg.out_mul_cosetCoord ι
  have hrep : ∀ (g : G) (k : Kc), rep (g * ι k) = rep g := fun g k =>
    congrArg Quotient.out (Alg.mk_mul_eq ι g k)
  have hcrd : ∀ (g : G) (k : Kc), crd (g * ι k) = crd g * k := Alg.cosetCoord_mul hι
  let Ω : Fin (Module.finrank ℂ E) → (Kc → ℂ) →ₗ[ℂ] (G → ℂ) := fun p =>
    { toFun := fun c g => conj (e p (rep g)) * c (crd g)
      map_add' := fun c c' => funext fun g => by simp only [Pi.add_apply, mul_add]
      map_smul' := fun a c => funext fun g => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  let Ω' : Fin (Module.finrank ℂ E) → (⊤ : Submodule ℂ (Kc → ℂ)) →ₗ[ℂ] (G → ℂ) := fun p =>
    (Ω p).comp (Submodule.subtype ⊤)
  have hP₀ : ∀ (k : Kc), ∀ θ ∈ (⊤ : Submodule ℂ (Kc → ℂ)),
      (fun x => θ (x * (MonoidHom.id Kc) k)) ∈ (⊤ : Submodule ℂ (Kc → ℂ)) := fun _ _ _ => Submodule.mem_top
  have hΩA : ∀ (p : Fin (Module.finrank ℂ E)) (k : Kc) (θ : (⊤ : Submodule ℂ (Kc → ℂ))) (y : G),
      Ω' p ⟨fun x => (θ : Kc → ℂ) (x * (MonoidHom.id Kc) k), hP₀ k θ θ.2⟩ y = Ω' p θ (y * ι k) := by
    intro p k θ y
    show conj (e p (rep y)) * (θ : Kc → ℂ) (crd y * k) = conj (e p (rep (y * ι k))) * (θ : Kc → ℂ) (crd (y * ι k))
    rw [hrep, hcrd]
  have hΩmem : ∀ p q : Fin (Module.finrank ℂ E),
      Ω p (fun κ => conj (P κ p q)) ∈ ⨆ j, typeSubmodule ι (ρ j).dual := fun p q =>
    Alg.mem_iSup_typeSubmodule_of_intertwines (MonoidHom.id Kc) hι (fun j => (ρ j).dual) ⊤ hP₀ (Ω' p)
      (hΩA p) ⟨_, Submodule.mem_top⟩ (hc p q)

  have hconj_e : ∀ q : Fin (Module.finrank ℂ E),
      (fun g => conj (e q g)) = ∑ p, Ω p (fun κ => conj (P κ p q)) := by
    intro q
    funext g
    rw [Finset.sum_apply]
    show conj (e q g) = ∑ p, conj (e p (rep g)) * conj (P (crd g) p q)
    conv_lhs => rw [← hdec g]
    rw [hexp (crd g) q (rep g), map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, mul_comm]
  have hconj_e_mem : ∀ q : Fin (Module.finrank ℂ E),
      (fun g => conj (e q g)) ∈ ⨆ j, typeSubmodule ι (ρ j).dual := by
    intro q
    rw [hconj_e q]
    exact Submodule.sum_mem _ fun p _ => hΩmem p q

  have hfE : f ∈ E := Submodule.subset_span ⟨1, funext fun x => by
    show f (x * ι 1) = f x
    rw [map_one, mul_one]⟩
  have hfexp : f = ∑ q, Bs.repr ⟨f, hfE⟩ q • e q := by
    have h := Bs.sum_repr ⟨f, hfE⟩
    have h' := congrArg (Subtype.val : E → G → ℂ) h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
    exact h'.symm
  have hconj_f : (fun x => conj (f x)) = ∑ q, conj (Bs.repr ⟨f, hfE⟩ q) • fun x => conj (e q x) := by
    funext x
    conv_lhs => rw [hfexp]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  rw [hconj_f]
  exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (hconj_e_mem q)

end Engine

end KcConjType

end

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped ComplexConjugate

namespace KcConjType

section Compact

variable (K : Type*) [NormedField K]

def rowIsoSet : Set (Matrix (Fin 2) (Fin 2) K) :=
  {m | m.det = 1} ∩ ({m | ‖m.det‖ = 1} ∩ ⋂ x : K, ⋂ y : K,
    {m | ‖x * m 0 0 + y * m 1 0‖ ^ 2 + ‖x * m 0 1 + y * m 1 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2})

theorem mem_rowIsoSet_iff (k : GL (Fin 2) K) :
    (k : Matrix (Fin 2) (Fin 2) K) ∈ rowIsoSet K ↔ k ∈ rowIsometrySubgroup₀ K := by
  simp only [rowIsoSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq,
    mem_rowIsometrySubgroup₀_iff, IsRowIsometry]

theorem continuous_entry (i j : Fin 2) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) K => m i j :=
  continuous_id.matrix_elem i j

theorem isClosed_rowIsoSet : IsClosed (rowIsoSet K) := by
  have hdet : Continuous fun m : Matrix (Fin 2) (Fin 2) K => m.det := continuous_id.matrix_det
  refine (isClosed_eq hdet continuous_const).inter
    ((isClosed_eq hdet.norm continuous_const).inter ?_)
  refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ continuous_const
  have h0 : Continuous fun m : Matrix (Fin 2) (Fin 2) K => x * m 0 0 + y * m 1 0 :=
    (continuous_const.mul (continuous_entry K 0 0)).add
      (continuous_const.mul (continuous_entry K 1 0))
  have h1 : Continuous fun m : Matrix (Fin 2) (Fin 2) K => x * m 0 1 + y * m 1 1 :=
    (continuous_const.mul (continuous_entry K 0 1)).add
      (continuous_const.mul (continuous_entry K 1 1))
  exact (h0.norm.pow 2).add (h1.norm.pow 2)

theorem norm_entry_le_one {m : Matrix (Fin 2) (Fin 2) K} (hm : m ∈ rowIsoSet K) (i j : Fin 2) :
    ‖m i j‖ ≤ 1 := by
  have hrow : ∀ x y : K,
      ‖x * m 0 0 + y * m 1 0‖ ^ 2 + ‖x * m 0 1 + y * m 1 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    have h := hm.2.2
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at h
    exact h
  have hr0 : ‖m 0 0‖ ^ 2 + ‖m 0 1‖ ^ 2 = 1 := by
    have h := hrow 1 0
    simpa using h
  have hr1 : ‖m 1 0‖ ^ 2 + ‖m 1 1‖ ^ 2 = 1 := by
    have h := hrow 0 1
    simpa using h
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ^ 2 + b ^ 2 = 1 → a ≤ 1 := by
    intro a b ha hb h
    nlinarith [sq_nonneg b, sq_nonneg (a - 1)]
  fin_cases i <;> fin_cases j
  · exact key _ _ (norm_nonneg _) (norm_nonneg _) hr0
  · exact key _ _ (norm_nonneg _) (norm_nonneg _) (by rw [add_comm]; exact hr0)
  · exact key _ _ (norm_nonneg _) (norm_nonneg _) hr1
  · exact key _ _ (norm_nonneg _) (norm_nonneg _) (by rw [add_comm]; exact hr1)

theorem isCompact_rowIsoSet [ProperSpace K] : IsCompact (rowIsoSet K) := by
  have hbox : IsCompact ((Set.pi Set.univ fun _ : Fin 2 =>
      Set.pi Set.univ fun _ : Fin 2 => Metric.closedBall (0 : K) 1) :
        Set (Matrix (Fin 2) (Fin 2) K)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hbox.of_isClosed_subset (isClosed_rowIsoSet K) fun m hm => ?_
  exact Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j =>
    mem_closedBall_zero_iff.mpr (norm_entry_le_one K hm i j)

def toUnit (m : rowIsoSet K) : GL (Fin 2) K where
  val := m.1
  inv := m.1.adjugate
  val_inv := by
    have hd : m.1.det = 1 := m.2.1
    rw [Matrix.mul_adjugate, hd, one_smul]
  inv_val := by
    have hd : m.1.det = 1 := m.2.1
    rw [Matrix.adjugate_mul, hd, one_smul]

theorem continuous_toUnit : Continuous (toUnit K) :=
  Units.continuous_iff.mpr ⟨continuous_subtype_val, continuous_subtype_val.matrix_adjugate⟩

theorem range_toUnit :
    Set.range (toUnit K) = (rowIsometrySubgroup₀ K : Set (GL (Fin 2) K)) := by
  ext k
  constructor
  · rintro ⟨m, rfl⟩
    exact (mem_rowIsoSet_iff K (toUnit K m)).mp m.2
  · intro hk
    exact ⟨⟨(k : Matrix (Fin 2) (Fin 2) K), (mem_rowIsoSet_iff K k).mpr hk⟩, Units.ext rfl⟩

theorem isCompact_rowIsometrySubgroup₀ [ProperSpace K] :
    IsCompact (rowIsometrySubgroup₀ K : Set (GL (Fin 2) K)) := by
  rw [← range_toUnit]
  haveI : CompactSpace (rowIsoSet K) := isCompact_iff_compactSpace.mp (isCompact_rowIsoSet K)
  exact isCompact_range (continuous_toUnit K)

end Compact

section Arch

variable (F : Type) [Field F] [NumberField F]

scoped instance compactSpace_Kw (w : InfinitePlace F) : CompactSpace (rowIsometrySubgroup₀ w.Completion) :=
  haveI : ProperSpace w.Completion := NumberField.AdelicBox.properSpace_completion (K := F) w
  isCompact_iff_compactSpace.mp (isCompact_rowIsometrySubgroup₀ w.Completion)

variable {F}

theorem continuous_archMatrixUpdate (w : InfinitePlace F) : Continuous (archMatrixUpdate F w) := by
  refine continuous_matrix fun i j => ?_
  refine continuous_pi fun v => ?_
  by_cases hv : v = w
  · subst hv
    simp_rw [archMatrixUpdate_apply_self]
    exact continuous_id.matrix_elem i j
  · simp_rw [archMatrixUpdate_apply_of_ne F w _ i j hv]
    exact continuous_const

theorem continuous_archGLIncl (w : InfinitePlace F) : Continuous (archGLIncl F w) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_archMatrixUpdate w).comp Units.continuous_val
  · exact (continuous_archMatrixUpdate w).comp Units.continuous_coe_inv

theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl F) := by
  have hval : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      ((adelicArchGLIncl F g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      (((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :
          InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

theorem continuous_rowIsometryInclAt₀ (w : InfinitePlace F) : Continuous (rowIsometryInclAt₀ F w) := by
  show Continuous fun k : rowIsometrySubgroup₀ w.Completion =>
    adelicArchGLIncl F (archGLIncl F w (k : GL (Fin 2) w.Completion))
  exact continuous_adelicArchGLIncl.comp ((continuous_archGLIncl w).comp continuous_subtype_val)

theorem rowIsometryInclAt₀_injective (w : InfinitePlace F) :
    Function.Injective (rowIsometryInclAt₀ F w) := by
  intro k k' h
  apply Subtype.ext
  have h1 : archGLIncl F w (k : GL (Fin 2) w.Completion) = archGLIncl F w (k' : GL (Fin 2) w.Completion) := by
    have h2 := congrArg (glArch (𝓞 F) F) h
    rw [rowIsometryInclAt₀_apply, rowIsometryInclAt₀_apply] at h2
    change glArch (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w _)) =
      glArch (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w _)) at h2
    rwa [glArch_adelicArchGLIncl, glArch_adelicArchGLIncl] at h2
  have h3 := congrArg (archComponent F w) h1
  rwa [archComponent_archGLIncl_self, archComponent_archGLIncl_self] at h3

theorem star_mem_iSup_archTypeSubmodule (w : InfinitePlace F)
    {J : Type*} {W : J → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    [∀ j, FiniteDimensional ℂ (W j)]
    (ρ : ∀ j, Representation ℂ (rowIsometrySubgroup₀ w.Completion) (W j))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f)
    (hfmem : f ∈ ⨆ j, typeSubmodule (rowIsometryInclAt₀ F w) (ρ j)) :
    (fun x => conj (f x)) ∈ ⨆ j, typeSubmodule (rowIsometryInclAt₀ F w) (ρ j).dual := by
  letI : MeasurableSpace (rowIsometrySubgroup₀ w.Completion) := borel _
  haveI : BorelSpace (rowIsometrySubgroup₀ w.Completion) := ⟨rfl⟩

  let K₀ : TopologicalSpace.PositiveCompacts (rowIsometrySubgroup₀ w.Completion) :=
    ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  let μ₀ : Measure (rowIsometrySubgroup₀ w.Completion) := Measure.haarMeasure K₀
  let μ : Measure (rowIsometrySubgroup₀ w.Completion) := μ₀.inv
  haveI : IsFiniteMeasure μ := by
    show IsFiniteMeasure (Measure.map _ μ₀)
    infer_instance
  haveI : μ.IsOpenPosMeasure := Measure.IsOpenPosMeasure.inv
  haveI : μ.IsMulRightInvariant := Measure.inv.instIsMulRightInvariant
  have hfc : ∀ x : AdelicGL2 (𝓞 F) F, Continuous fun κ : rowIsometrySubgroup₀ w.Completion =>
      f (x * rowIsometryInclAt₀ F w κ) :=
    fun x => hf.comp (continuous_const.mul (continuous_rowIsometryInclAt₀ w))
  exact star_mem_iSup_typeSubmodule_dual μ (rowIsometryInclAt₀ F w) (rowIsometryInclAt₀_injective w) ρ f hfc hfmem

end Arch

end KcConjType
p2m_reactivate "P2MW.S_AutomorphicForm_star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support.KcConjType"

end
p2m_reactivate "P2MW.S_AutomorphicForm_star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support.KcConjType"

set_option autoImplicit false

open scoped ComplexConjugate
open NumberField AutomorphicForm

open MeasureTheory KcConjType KcConjType.Alg

theorem solution
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (S : Subgroup (AdelicGL2 (𝓞 F) F))
    (hS : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), rowIsometryInclAt₀ F w k ∈ S)
    (E : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hEfd : FiniteDimensional ℂ E)
    (hER : ∀ s ∈ S, ∀ v ∈ E, (fun x => v (x * s)) ∈ E)
    (hsupp : ∀ v ∈ E, ∀ x : AdelicGL2 (𝓞 F) F, v x ≠ 0 → x ∈ S)
    (hcont : ∀ v ∈ E, ∀ (w : InfinitePlace F) (x : AdelicGL2 (𝓞 F) F),
      Continuous fun k : rowIsometrySubgroup₀ w.Completion => v (x * rowIsometryInclAt₀ F w k))
    (hEt : E ≤ archCutSubmodule F tys) :
    ∀ v ∈ E, (fun x => conj (v x⁻¹)) ∈ archCutSubmodule F tys := by
  classical
  intro v hv
  haveI : FiniteDimensional ℂ E := hEfd
  rw [mem_archCutSubmodule_iff]
  intro w

  have hιinj : Function.Injective (rowIsometryInclAt₀ F w) := rowIsometryInclAt₀_injective w
  have hE : ∀ (κ : rowIsometrySubgroup₀ w.Completion), ∀ u ∈ E, (fun x => u (x * rowIsometryInclAt₀ F w κ)) ∈ E :=
    fun κ u hu => hER _ (hS w κ) u hu
  have hid : Function.Injective (MonoidHom.id (rowIsometrySubgroup₀ w.Completion)) := fun _ _ h => h
  have hEcut : ∀ u ∈ E, u ∈ ⨆ i : Fin (tys.card w),
      typeSubmodule ((rowIsometryInclAt₀ F w).comp (MonoidHom.id (rowIsometrySubgroup₀ w.Completion))) (tys.rep w i).ρ := by
    intro u hu
    rw [MonoidHom.comp_id]
    exact (mem_archCutSubmodule_iff F tys u).1 (hEt hu) w
  have hsupp' : ∀ x : AdelicGL2 (𝓞 F) F, x ∉ S → v x = 0 := fun x hx => by
    by_contra h
    exact hx (hsupp v hv x h)

  let Bs := Module.finBasis ℂ E
  let e : Fin (Module.finrank ℂ E) → (AdelicGL2 (𝓞 F) F → ℂ) := fun p => ((Bs p : E) : AdelicGL2 (𝓞 F) F → ℂ)
  let P : rowIsometrySubgroup₀ w.Completion → Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ :=
    fun κ => Pm (rowIsometryInclAt₀ F w) E hE κ
  have hexp : ∀ (κ : rowIsometrySubgroup₀ w.Completion) (q : Fin (Module.finrank ℂ E)) (x : AdelicGL2 (𝓞 F) F),
      e q (x * rowIsometryInclAt₀ F w κ) = ∑ p, P κ p q * e p x := by
    intro κ q x
    have hsum : piE (rowIsometryInclAt₀ F w) E hE κ (Bs q) = ∑ p, P κ p q • Bs p := by
      conv_lhs => rw [← Bs.sum_repr (piE (rowIsometryInclAt₀ F w) E hE κ (Bs q))]
      refine Finset.sum_congr rfl fun p _ => ?_
      congr 1
      show Bs.repr (piE (rowIsometryInclAt₀ F w) E hE κ (Bs q)) p =
        LinearMap.toMatrix Bs Bs (piE (rowIsometryInclAt₀ F w) E hE κ) p q
      rw [LinearMap.toMatrix_apply]
    have h := congrArg (fun u : E => (u : AdelicGL2 (𝓞 F) F → ℂ) x) hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h
  have hcoef : ∀ a b : Fin (Module.finrank ℂ E),
      (fun κ : rowIsometrySubgroup₀ w.Completion => P κ⁻¹ a b) ∈ ⨆ j : Fin (tys.card w), typeSubmodule (MonoidHom.id (rowIsometrySubgroup₀ w.Completion)) (tys.rep w j).ρ.dual :=
    fun a b => Pm_inv_entry_mem_iSup (rowIsometryInclAt₀ F w) E hE hid (fun j => (tys.rep w j).ρ) hEcut a b

  let rep : AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F := fun g => (QuotientGroup.mk g : AdelicGL2 (𝓞 F) F ⧸ (rowIsometryInclAt₀ F w).range).out
  let crd : AdelicGL2 (𝓞 F) F → rowIsometrySubgroup₀ w.Completion := cosetCoord (rowIsometryInclAt₀ F w)
  have hdec : ∀ g, rep g * rowIsometryInclAt₀ F w (crd g) = g := out_mul_cosetCoord (rowIsometryInclAt₀ F w)
  have hrep : ∀ (g : AdelicGL2 (𝓞 F) F) (k : rowIsometrySubgroup₀ w.Completion), rep (g * rowIsometryInclAt₀ F w k) = rep g := fun g k =>
    congrArg Quotient.out (mk_mul_eq (rowIsometryInclAt₀ F w) g k)
  have hcrd : ∀ (g : AdelicGL2 (𝓞 F) F) (k : rowIsometrySubgroup₀ w.Completion), crd (g * rowIsometryInclAt₀ F w k) = crd g * k := cosetCoord_mul hιinj

  let c : Fin (Module.finrank ℂ E) → AdelicGL2 (𝓞 F) F → ℂ := fun q y =>
    if h : y⁻¹ ∈ S then Bs.repr ⟨fun z => v (z * y⁻¹), hER _ h v hv⟩ q else 0
  let Ω : Fin (Module.finrank ℂ E) → (rowIsometrySubgroup₀ w.Completion → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) := fun q =>
    { toFun := fun c' g => c q (rep g) * c' (crd g)
      map_add' := fun c₁ c₂ => funext fun g => by simp only [Pi.add_apply, mul_add]
      map_smul' := fun a c₁ => funext fun g => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  let Ω' : Fin (Module.finrank ℂ E) → (⊤ : Submodule ℂ (rowIsometrySubgroup₀ w.Completion → ℂ)) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) := fun q =>
    (Ω q).comp (Submodule.subtype ⊤)
  have hP₀ : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ θ ∈ (⊤ : Submodule ℂ (rowIsometrySubgroup₀ w.Completion → ℂ)),
      (fun x => θ (x * (MonoidHom.id (rowIsometrySubgroup₀ w.Completion)) k)) ∈ (⊤ : Submodule ℂ (rowIsometrySubgroup₀ w.Completion → ℂ)) := fun _ _ _ => Submodule.mem_top
  have hΩA : ∀ (q : Fin (Module.finrank ℂ E)) (k : rowIsometrySubgroup₀ w.Completion) (θ : (⊤ : Submodule ℂ (rowIsometrySubgroup₀ w.Completion → ℂ))) (y : AdelicGL2 (𝓞 F) F),
      Ω' q ⟨fun x => (θ : rowIsometrySubgroup₀ w.Completion → ℂ) (x * (MonoidHom.id (rowIsometrySubgroup₀ w.Completion)) k), hP₀ k θ θ.2⟩ y = Ω' q θ (y * rowIsometryInclAt₀ F w k) := by
    intro q k θ y
    show c q (rep y) * (θ : rowIsometrySubgroup₀ w.Completion → ℂ) (crd y * k) = c q (rep (y * rowIsometryInclAt₀ F w k)) * (θ : rowIsometrySubgroup₀ w.Completion → ℂ) (crd (y * rowIsometryInclAt₀ F w k))
    rw [hrep, hcrd]
  have hΩmem : ∀ p q : Fin (Module.finrank ℂ E),
      Ω q (fun κ => P κ⁻¹ p q) ∈ ⨆ j : Fin (tys.card w), typeSubmodule (rowIsometryInclAt₀ F w) (tys.rep w j).ρ.dual :=
    fun p q => mem_iSup_typeSubmodule_of_intertwines (MonoidHom.id (rowIsometrySubgroup₀ w.Completion)) hιinj (fun j => (tys.rep w j).ρ.dual) ⊤ hP₀ (Ω' q)
      (hΩA q) ⟨_, Submodule.mem_top⟩ (hcoef p q)

  have hvt : (fun x : AdelicGL2 (𝓞 F) F => v x⁻¹) = ∑ q, ∑ p, (e p 1) • Ω q (fun κ => P κ⁻¹ p q) := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    show v g⁻¹ = ∑ q, ∑ p, e p 1 * (c q (rep g) * P (crd g)⁻¹ p q)
    have hr : rep g = g * (rowIsometryInclAt₀ F w (crd g))⁻¹ := eq_mul_inv_of_mul_eq (hdec g)
    have hg : g⁻¹ = rowIsometryInclAt₀ F w (crd g)⁻¹ * (rep g)⁻¹ := by
      rw [hr, mul_inv_rev, inv_inv, map_inv, ← mul_assoc, inv_mul_cancel, one_mul]
    by_cases hS' : (rep g)⁻¹ ∈ S
    · have hu : (fun z => v (z * (rep g)⁻¹)) ∈ E := hER _ hS' v hv
      have hcq : ∀ q, c q (rep g) = Bs.repr ⟨fun z => v (z * (rep g)⁻¹), hu⟩ q := fun q => by
        simp only [c, dif_pos hS']
      have hux : ∀ y : AdelicGL2 (𝓞 F) F, v (y * (rep g)⁻¹) = ∑ q, c q (rep g) * e q y := by
        intro y
        have h := Bs.sum_repr ⟨fun z => v (z * (rep g)⁻¹), hu⟩
        have h' := congrArg (fun u : E => (u : AdelicGL2 (𝓞 F) F → ℂ) y) h
        simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h'
        rw [← h']
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hcq q]
      rw [hg, ← one_mul (rowIsometryInclAt₀ F w (crd g)⁻¹ * (rep g)⁻¹), ← mul_assoc, hux]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hexp (crd g)⁻¹ q 1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    · have hzero : v g⁻¹ = 0 := by
        apply hsupp'
        intro hg'
        apply hS'
        have : (rep g)⁻¹ = rowIsometryInclAt₀ F w (crd g) * g⁻¹ := by
          rw [hr, mul_inv_rev, inv_inv]
        rw [this]
        exact S.mul_mem (hS w _) hg'
      rw [hzero]
      symm
      refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun p _ => ?_
      simp only [c, dif_neg hS', zero_mul, mul_zero]
  have hvtmem : (fun x : AdelicGL2 (𝓞 F) F => v x⁻¹) ∈ ⨆ j : Fin (tys.card w), typeSubmodule (rowIsometryInclAt₀ F w) (tys.rep w j).ρ.dual := by
    rw [hvt]
    exact Submodule.sum_mem _ fun q _ => Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (hΩmem p q)

  have hvtc : ∀ x : AdelicGL2 (𝓞 F) F, Continuous fun κ : rowIsometrySubgroup₀ w.Completion => (fun y : AdelicGL2 (𝓞 F) F => v y⁻¹) (x * rowIsometryInclAt₀ F w κ) := by
    intro x
    by_cases hx : x⁻¹ ∈ S
    · have hc := hcont (fun z => v (z * x⁻¹)) (hER _ hx v hv) w 1
      have h2 : (fun κ : rowIsometrySubgroup₀ w.Completion => (fun y : AdelicGL2 (𝓞 F) F => v y⁻¹) (x * rowIsometryInclAt₀ F w κ)) =
          (fun κ : rowIsometrySubgroup₀ w.Completion => v (1 * rowIsometryInclAt₀ F w κ * x⁻¹)) ∘ (fun κ => κ⁻¹) := by
        funext κ
        show v (x * rowIsometryInclAt₀ F w κ)⁻¹ = v (1 * rowIsometryInclAt₀ F w κ⁻¹ * x⁻¹)
        rw [mul_inv_rev, map_inv, one_mul]
      rw [h2]
      exact hc.comp continuous_inv
    · have h2 : (fun κ : rowIsometrySubgroup₀ w.Completion => (fun y : AdelicGL2 (𝓞 F) F => v y⁻¹) (x * rowIsometryInclAt₀ F w κ)) = fun _ => 0 := by
        funext κ
        show v (x * rowIsometryInclAt₀ F w κ)⁻¹ = 0
        apply hsupp'
        intro hmem
        apply hx
        have : x⁻¹ = rowIsometryInclAt₀ F w κ * (x * rowIsometryInclAt₀ F w κ)⁻¹ := by
          rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
        rw [this]
        exact S.mul_mem (hS w κ) hmem
      rw [h2]
      exact continuous_const

  letI : MeasurableSpace (rowIsometrySubgroup₀ w.Completion) := borel _
  haveI : BorelSpace (rowIsometrySubgroup₀ w.Completion) := ⟨rfl⟩
  let K₀ : TopologicalSpace.PositiveCompacts (rowIsometrySubgroup₀ w.Completion) := ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  let μ₀ : Measure (rowIsometrySubgroup₀ w.Completion) := Measure.haarMeasure K₀
  let μ : Measure (rowIsometrySubgroup₀ w.Completion) := μ₀.inv
  haveI : IsFiniteMeasure μ := by
    show IsFiniteMeasure (Measure.map _ μ₀)
    infer_instance
  haveI : μ.IsOpenPosMeasure := Measure.IsOpenPosMeasure.inv
  haveI : μ.IsMulRightInvariant := Measure.inv.instIsMulRightInvariant
  have h := star_mem_iSup_typeSubmodule_dual μ (rowIsometryInclAt₀ F w) hιinj
    (fun i : Fin (tys.card w) => (tys.rep w i).ρ.dual) (fun y : AdelicGL2 (𝓞 F) F => v y⁻¹) hvtc hvtmem
  exact (iSup_mono fun i => typeSubmodule_dual_dual_le (rowIsometryInclAt₀ F w) (tys.rep w i).ρ) h

end S_AutomorphicForm_star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support
end P2MW
export P2MW.S_AutomorphicForm_star_mem_archCutSubmodule_of_finiteDimensional_of_forall_comp_mul_mem_of_support (solution)
