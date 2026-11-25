-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFinite
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:17.317911+00:00
-- url     : https://prove2.me/theorems/054ea926-5614-5a90-90f6-575271da0fd7
-- title:
--   PTilde Finite
-- statement:
--   Definitions and structural lemmas for PTilde Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechTransport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_of_subset_d748224c1d3f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_locCone_eq_db25ae5cb6f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locCone_degLoc_5fdd4721a38b

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
universe u w
section Compare
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable (S x) in
open Classical in

def supportRes (I J : StdCell N) (_h : I.1 ⊆ J.1) : ConeLaurent S x →ₗ[S] ConeLaurent S x :=
  if J.1 ⊆ support x then LinearMap.id else 0
theorem supportRes_of_subset {I J : StdCell N} (h : I.1 ⊆ J.1) (hJ : J.1 ⊆ support x) :
    supportRes S x I J h = LinearMap.id := if_pos hJ
theorem supportRes_of_not {I J : StdCell N} (h : I.1 ⊆ J.1) (hJ : ¬ J.1 ⊆ support x) :
    supportRes S x I J h = 0 := if_neg hJ
def toChartIdx {n : ℕ} (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) n) (h : K.1.1 ⊆ support x) :
    Cech.Idx (support x) n :=
  ⟨⟨K.1.1, K.1.2.1, h⟩, K.2⟩
def ofChartIdx {n : ℕ} (K : Cech.Idx (support x) n) : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) n :=
  ⟨⟨K.1.1, K.1.2.1, Finset.subset_univ _⟩, K.2⟩
variable (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ)
def FinGradedSub.cellConeS (I : StdCell N) : LocMod S N M.coneSub I.1 →ₗ[S] ConeLaurent S x :=
  (M.cellCone I).restrictScalars S
def FinGradedSub.coneDeg (I : StdCell N) : Submodule S (ConeLaurent S x) :=
  (degLoc M.coneGraded c I).map (M.cellConeS I)
theorem FinGradedSub.mem_coneDeg_of_subset {I : StdCell N} (hI : I.1 ⊆ support x) {y : ConeLaurent S x} :
    y ∈ M.coneDeg c I ↔ ∃ v ∈ M.tilde c ⟨I.1, I.2.1, hI⟩, y = coneSingle S x c v := by
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨v, hv, hzv⟩ := locCone_degLoc M c I hI hz
    refine ⟨v, hv, ?_⟩
    change M.cellCone I z = _
    rw [M.cellCone_of_subset hI]
    exact hzv
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨z, hz, hzv⟩ := exists_locCone_eq M c I hI hv
    refine Submodule.mem_map.mpr ⟨z, hz, ?_⟩
    change M.cellCone I z = _
    rw [M.cellCone_of_subset hI]
    exact hzv
def FinGradedSub.tildeCone (I : Chart x) : (M.tildeSys c).sub I →ₗ[S] ConeLaurent S x :=
  (coneSingle S x c).comp
    { toFun := fun y => (y : Ω), map_add' := fun _ _ => rfl,
      map_smul' := fun a y => by rw [RingHom.id_apply]; exact Submodule.coe_smul_of_tower a y }
open Classical in

def FinGradedSub.embedC (n : ℕ) :
    Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) n →ₗ[S]
      Cech.Cochain (fun _ : StdCell N => ConeLaurent S x) n where
  toFun s K := if h : K.1.1 ⊆ support x then M.tildeCone c _ (s (toChartIdx K h)) else 0
  map_add' s t := by
    funext K
    by_cases h : K.1.1 ⊆ support x
    · simp only [dif_pos h, Pi.add_apply, map_add]
    · simp only [dif_neg h, Pi.add_apply, add_zero]
  map_smul' a s := by
    funext K
    by_cases h : K.1.1 ⊆ support x
    · simp only [dif_pos h, Pi.smul_apply, map_smul, RingHom.id_apply]
    · simp only [dif_neg h, Pi.smul_apply, smul_zero, RingHom.id_apply]
theorem FinGradedSub.embedC_of_subset {n : ℕ} (s : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) n)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) n) (h : K.1.1 ⊆ support x) :
    M.embedC c n s K = coneSingle S x c (s (toChartIdx K h) : Ω) := by
  simp only [FinGradedSub.embedC, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos h]
  rfl
theorem FinGradedSub.embedC_of_subset' {n : ℕ}
    (s : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) n)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) n) (h : K.1.1 ⊆ support x) :
    M.embedC c n s K = M.tildeCone c _ (s (toChartIdx K h)) :=
  M.embedC_of_subset c s K h
theorem FinGradedSub.embedC_of_not {n : ℕ} (s : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) n)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) n) (h : ¬ K.1.1 ⊆ support x) :
    M.embedC c n s K = 0 := by
  simp only [FinGradedSub.embedC, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_neg h]
theorem FinGradedSub.embedC_d (n : ℕ) (s : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) n) :
    M.embedC c (n + 1) (Cech.d _ (M.tildeSys c).res n s) =
      Cech.d (fun _ : StdCell N => ConeLaurent S x) (supportRes S x) n (M.embedC c n s) := by
  funext J
  rw [Cech.d_apply]
  by_cases hJ : J.1.1 ⊆ support x
  · rw [M.embedC_of_subset' c _ J hJ, Cech.d_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, supportRes_of_subset _ hJ, LinearMap.id_apply,
      M.embedC_of_subset c s _ ((Cech.face_subset J j).trans hJ)]
    rfl
  · rw [M.embedC_of_not c _ J hJ]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [supportRes_of_not _ hJ, LinearMap.zero_apply, smul_zero]
theorem FinGradedSub.embedC_mem (n : ℕ) (s : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) n) :
    M.embedC c n s ∈ Cech.Cdeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) n := by
  intro K _
  by_cases h : K.1.1 ⊆ support x
  · rw [M.embedC_of_subset c s K h]
    exact (M.mem_coneDeg_of_subset c h).mpr ⟨_, (s (toChartIdx K h)).2, rfl⟩
  · rw [M.embedC_of_not c s K h]
    exact zero_mem _
theorem FinGradedSub.embedC_mem_cocyDeg (n : ℕ) (s : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) n)
    (hs : s ∈ LinearMap.ker (Cech.d _ (M.tildeSys c).res n)) :
    M.embedC c n s ∈ Cech.cocyDeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) (supportRes S x) n :=
  ⟨LinearMap.mem_ker.mpr (by rw [← M.embedC_d, LinearMap.mem_ker.mp hs, map_zero]), M.embedC_mem c n s⟩
def FinGradedSub.embedH (n : ℕ) :
    (M.tildeSys c).H n →ₗ[S]
      Cech.Hdeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) (supportRes S x) n :=
  Submodule.mapQ _ _
    ((M.embedC c n).restrict (p := LinearMap.ker (Cech.d _ (M.tildeSys c).res n))
      (q := Cech.cocyDeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) (supportRes S x) n)
      (M.embedC_mem_cocyDeg c n))
    (by
      intro s hs
      cases n with
      | zero =>
        change (s : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) 0) ∈ (⊥ : Submodule S _) at hs
        rw [Submodule.mem_bot] at hs
        change M.embedC c 0 (s : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) 0) ∈
          (⊥ : Submodule S _)
        rw [hs, map_zero]
        exact zero_mem _
      | succ n =>
        obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hs
        change M.embedC c (n + 1) (s : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) (n + 1)) ∈
          (Cech.Cdeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) n).map
            (Cech.d (fun _ : StdCell N => ConeLaurent S x) (supportRes S x) n)
        exact Submodule.mem_map.mpr ⟨M.embedC c n t, M.embedC_mem c n t, by rw [← M.embedC_d, ht]; rfl⟩)
end Compare
end
end GroundTheory.Heights₂.Heights.Kleiman


