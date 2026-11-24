-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:41.923478+00:00
-- url     : https://prove2.me/theorems/744f5584-a26c-408c-bd92-9bf0c10c7c7c
-- title:
--   PSerre Onto
-- statement:
--   Definitions and structural lemmas for PSerre Onto, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w w'
section Grading
theorem isInternal_of_proj {R : Type*} {A : Type*} {ι : Type*} [Ring R] [AddCommGroup A] [Module R A]
    [DecidableEq ι]     (p : ι → Submodule R A) (π : ι → A →ₗ[R] A) (h1 : ∀ i a, a ∈ p i → π i a = a)
    (h2 : ∀ i j a, i ≠ j → a ∈ p j → π i a = 0) (h3 : ⨆ i, p i = ⊤) : DirectSum.IsInternal p := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨fun i => ?_, h3⟩
  rw [Submodule.disjoint_def]
  intro a ha ha'
  have hle : (⨆ (j) (_ : j ≠ i), p j) ≤ LinearMap.ker (π i) :=
    iSup_le fun j => iSup_le fun hj b hb => h2 i j b (Ne.symm hj) hb
  rw [← h1 i a ha]
  exact hle ha'
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
def GradedPMod.transport (𝓜 : GradedPMod S N M) (e : M ≃ₗ[Poly S N] M') : GradedPMod S N M' where
  piece c := (𝓜.piece c).map ((e.restrictScalars S : M ≃ₗ[S] M') : M →ₗ[S] M')
  isInternal := by
    have hi := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp 𝓜.isInternal
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨hi.1.map_orderIso (Submodule.orderIsoMapComap (e.restrictScalars S)), ?_⟩
    rw [← Submodule.map_iSup, hi.2, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (e.restrictScalars S).surjective
  smul_mem d c p m hp hm := by
    obtain ⟨m0, hm0, rfl⟩ := hm
    exact ⟨p • m0, 𝓜.smul_mem d c p m0 hp hm0, by simp⟩
def GradedPMod.toTransport (𝓜 : GradedPMod S N M) (e : M ≃ₗ[Poly S N] M') :
    GradedHom 𝓜 (𝓜.transport e) where
  toLin := e.toLinearMap
  map_piece _ m hm := ⟨m, hm, rfl⟩
def GradedPMod.ofTransport (𝓜 : GradedPMod S N M) (e : M ≃ₗ[Poly S N] M') :
    GradedHom (𝓜.transport e) 𝓜 where
  toLin := e.symm.toLinearMap
  map_piece _ m hm := by
    obtain ⟨m0, hm0, rfl⟩ := hm
    simpa using hm0
end Grading
section Free
variable {S : Type u} [CommRing S] {N : ℕ}
variable (S N) in

def freeGraded {r : ℕ} (deg : Fin r → ℤ) : GradedPMod S N (Fin r → Poly S N) where
  piece c := Submodule.pi Set.univ fun j => (polyGraded S N).piece (c - deg j)
  isInternal := by
    classical
    refine isInternal_of_proj _ (fun c => LinearMap.pi fun j =>
      (weightedHomogeneousComponent (fun _ : Fin (N + 1) => (1 : ℤ)) (c - deg j)).comp
        (LinearMap.proj j)) ?_ ?_ ?_
    · intro c f hf
      funext j
      have hj : f j ∈ (polyGraded S N).piece (c - deg j) := (Submodule.mem_pi.mp hf) j (Set.mem_univ _)
      change weightedHomogeneousComponent _ (c - deg j) (f j) = f j
      rw [weightedHomogeneousComponent_of_mem hj, if_pos rfl]
    · intro c c' f hcc' hf
      funext j
      have hj : f j ∈ (polyGraded S N).piece (c' - deg j) := (Submodule.mem_pi.mp hf) j (Set.mem_univ _)
      change weightedHomogeneousComponent _ (c - deg j) (f j) = 0
      rw [weightedHomogeneousComponent_of_mem hj, if_neg (by omega)]
    · rw [eq_top_iff]
      rintro f -
      rw [← Finset.univ_sum_single f]
      refine Submodule.sum_mem _ fun j _ => ?_
      have hall : f j ∈ ⨆ e, (polyGraded S N).piece e := by
        rw [((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp
          (polyGraded S N).isInternal).2]
        trivial
      have hmap : Pi.single j (f j) ∈
          (⨆ e, (polyGraded S N).piece e).map (LinearMap.single S (fun _ => Poly S N) j) :=
        ⟨f j, hall, rfl⟩
      rw [Submodule.map_iSup] at hmap
      have hsub : ∀ e, ((polyGraded S N).piece e).map (LinearMap.single S (fun _ => Poly S N) j) ≤
          Submodule.pi Set.univ fun j' => (polyGraded S N).piece (e + deg j - deg j') := by
        intro e
        rintro _ ⟨p, hp, rfl⟩
        rw [Submodule.mem_pi]
        intro j' _
        by_cases h : j' = j
        · subst h
          rw [LinearMap.single_apply, Pi.single_eq_same, add_sub_cancel_right]
          exact hp
        · rw [LinearMap.single_apply, Pi.single_eq_of_ne h]
          exact zero_mem _
      have hle : (⨆ e, ((polyGraded S N).piece e).map (LinearMap.single S (fun _ => Poly S N) j)) ≤
          ⨆ c, Submodule.pi Set.univ fun j' => (polyGraded S N).piece (c - deg j') :=
        iSup_mono' fun e => ⟨e + deg j, hsub e⟩
      exact hle hmap
  smul_mem e c p f hp hf := by
    rw [Submodule.mem_pi] at hf ⊢
    intro j _
    have := (polyGraded S N).smul_mem e (c - deg j) p (f j) hp (hf j (Set.mem_univ _))
    rw [show c + (e : ℤ) - deg j = c - deg j + e by ring]
    exact this
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
variable (S N) in

def freeMap {r : ℕ} (g : Fin r → M) : (Fin r → Poly S N) →ₗ[Poly S N] M :=
  ∑ j, (LinearMap.proj j).smulRight (g j)
end Free
section Kernel
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
variable {𝓕 : GradedPMod S N M} {𝓜 : GradedPMod S N M'}
omit [IsScalarTower S (Poly S N) M] [IsScalarTower S (Poly S N) M'] in

theorem GradedHom.map_decompose (φ : GradedHom 𝓕 𝓜) [DirectSum.Decomposition 𝓕.piece]
    [DirectSum.Decomposition 𝓜.piece] (c : ℤ) (m : M) :
    φ.toLin (DirectSum.decompose 𝓕.piece m c : M) = (DirectSum.decompose 𝓜.piece (φ.toLin m) c : M') := by
  classical
  induction m using DirectSum.Decomposition.inductionOn 𝓕.piece with
  | zero => simp
  | @homogeneous i m =>
    by_cases h : i = c
    · subst h
      rw [DirectSum.decompose_of_mem_same _ m.2, DirectSum.decompose_of_mem_same _ (φ.map_piece _ _ m.2)]
    · rw [DirectSum.decompose_of_mem_ne _ m.2 h, DirectSum.decompose_of_mem_ne _ (φ.map_piece _ _ m.2) h,
        map_zero]
  | add m m' hm hm' =>
    simp only [map_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, hm, hm']
def GradedHom.kerGraded (φ : GradedHom 𝓕 𝓜) : GradedPMod S N (LinearMap.ker φ.toLin) where
  piece c := (𝓕.piece c).comap ((LinearMap.ker φ.toLin).subtype.restrictScalars S)
  isInternal := by
    classical
    let _ := 𝓕.isInternal.chooseDecomposition
    let _ := 𝓜.isInternal.chooseDecomposition
    have hker : ∀ (c : ℤ) (k : LinearMap.ker φ.toLin),
        (DirectSum.decompose 𝓕.piece (k : M) c : M) ∈ LinearMap.ker φ.toLin := by
      intro c k
      rw [LinearMap.mem_ker, φ.map_decompose, LinearMap.mem_ker.mp k.2, DirectSum.decompose_zero]
      rfl
    let π : ℤ → LinearMap.ker φ.toLin →ₗ[S] LinearMap.ker φ.toLin := fun c =>
      { toFun := fun k => ⟨_, hker c k⟩
        map_add' := fun a b => by
          apply Subtype.ext
          simp [DirectSum.decompose_add]
        map_smul' := fun s a => by
          apply Subtype.ext
          simp [DirectSum.decompose_smul, DirectSum.smul_apply] }
    refine isInternal_of_proj _ π ?_ ?_ ?_
    · intro c k hk
      exact Subtype.ext (DirectSum.decompose_of_mem_same _ hk)
    · intro c c' k hcc' hk
      exact Subtype.ext (DirectSum.decompose_of_mem_ne _ hk (Ne.symm hcc'))
    · rw [eq_top_iff]
      rintro k -
      have hk : k = ∑ c ∈ (DirectSum.decompose 𝓕.piece (k : M)).support, π c k := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        exact (DirectSum.sum_support_decompose 𝓕.piece (k : M)).symm
      rw [hk]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.mem_iSup_of_mem c (DirectSum.decompose 𝓕.piece (k : M) c).2
  smul_mem d c p k hp hk := 𝓕.smul_mem d c p k hp hk
def GradedHom.kerIncl (φ : GradedHom 𝓕 𝓜) : GradedHom φ.kerGraded 𝓕 where
  toLin := (LinearMap.ker φ.toLin).subtype
  map_piece _ _ hk := hk
end Kernel
section Cohom
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
end Cohom
section Main
end Main
end
end GroundTheory.Heights₂.Heights.Kleiman


