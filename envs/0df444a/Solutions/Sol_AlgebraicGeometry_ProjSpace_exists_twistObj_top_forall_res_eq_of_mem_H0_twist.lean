-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.exists_twistObj_top_forall_res_eq_of_mem_H0_twist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/bc7e1798-ca5e-5efe-a2ff-5e931250b018

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mWs6Glue

variable {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
  (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]

def single (a : Fin (n + 1)) : (ProjSpace.stdCoverPullback ι).Idx 0 :=
  ⟨fun _ => ⟨a⟩, fun x y h => absurd h (by omega)⟩

theorem eq_single (s : (ProjSpace.stdCoverPullback ι).Idx 0) : s = single ι (s.1 0).down := by
  apply Subtype.ext
  funext k
  have hk : k = 0 := Fin.ext (by omega)
  subst hk
  rfl

theorem inter_single (a : Fin (n + 1)) :
    (ProjSpace.stdCoverPullback ι).inter (single ι a) = ProjSpace.pullbackChart ι a := by
  apply le_antisymm
  · refine (Scheme.OrderedAffineCover.inter_le _ _ 0).trans ?_
    rw [ProjSpace.stdCoverPullback_U, ProjSpace.stdCover_U, ProjSpace.pullbackChart_eq]
    exact le_rfl
  · refine le_iInf fun t => ?_
    rw [ProjSpace.stdCoverPullback_U, ProjSpace.stdCover_U, ProjSpace.pullbackChart_eq]
    exact le_rfl

def pair (a b : Fin (n + 1)) (hab : a < b) : (ProjSpace.stdCoverPullback ι).Idx 1 :=
  ⟨fun j => if j = 0 then ⟨a⟩ else ⟨b⟩, by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    have hi : i = 0 := Fin.ext (by omega)
    subst hi
    show (⟨a⟩ : ULift (Fin (n + 1))) < ⟨b⟩
    exact hab⟩

theorem face_pair_zero (a b : Fin (n + 1)) (hab : a < b) :
    (ProjSpace.stdCoverPullback ι).face (pair ι a b hab) 0 = single ι b := by
  apply Subtype.ext; funext k
  have hk : k = 0 := Fin.ext (by omega)
  subst hk; rfl

theorem face_pair_one (a b : Fin (n + 1)) (hab : a < b) :
    (ProjSpace.stdCoverPullback ι).face (pair ι a b hab) 1 = single ι a := by
  apply Subtype.ext; funext k
  have hk : k = 0 := Fin.ext (by omega)
  subst hk; rfl

theorem inter_single_inf_le_inter_pair (a b : Fin (n + 1)) (hab : a < b) :
    (ProjSpace.stdCoverPullback ι).inter (single ι a) ⊓ (ProjSpace.stdCoverPullback ι).inter (single ι b)
      ≤ (ProjSpace.stdCoverPullback ι).inter (pair ι a b hab) := by
  refine le_iInf fun t => ?_
  show _ ≤ (ProjSpace.stdCoverPullback ι).U (if t = 0 then ⟨a⟩ else ⟨b⟩)
  split_ifs
  · exact inf_le_left.trans ((Scheme.OrderedAffineCover.inter_le _ (single ι a) 0).trans le_rfl)
  · exact inf_le_right.trans ((Scheme.OrderedAffineCover.inter_le _ (single ι b) 0).trans le_rfl)

end P2mWs6Glue

open P2mWs6Glue in
set_option maxHeartbeats 3200000 in
theorem solution
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom φ] (m : ℕ)
    (c : (ProjSpace.twist (φ ≫ ProjSpace.π A n) φ m).cochain (ProjSpace.stdCoverPullback φ) 0)
    (hc : c ∈ (ProjSpace.twist (φ ≫ ProjSpace.π A n) φ m).H0 (ProjSpace.stdCoverPullback φ)) :
    ∃ g : ProjSpace.twistObj (φ ≫ ProjSpace.π A n) φ m ⊤,
      ∀ s : (ProjSpace.stdCoverPullback φ).Idx 0,
        (ProjSpace.twist (φ ≫ ProjSpace.π A n) φ m).res (le_top : (ProjSpace.stdCoverPullback φ).inter s ≤ ⊤) g = c s := by
  classical

  have hC : ∀ (i : Fin (n + 1)) (s₁ s₂ : (ProjSpace.stdCoverPullback φ).Idx 0), s₁ = s₂ → ∀ (W : Z.Opens)
      (h₁ : W ≤ (ProjSpace.stdCoverPullback φ).inter s₁ ⊓ ProjSpace.pullbackChart φ i) (h₂ : W ≤ (ProjSpace.stdCoverPullback φ).inter s₂ ⊓ ProjSpace.pullbackChart φ i),
      ProjSpace.restrictFun h₁ ((c s₁).val i) = ProjSpace.restrictFun h₂ ((c s₂).val i) := by
    rintro i s₁ s₂ rfl W h₁ h₂; rfl

  have hcyc : ∀ (t : (ProjSpace.stdCoverPullback φ).Idx 1) (i : Fin (n + 1)) (W : Z.Opens) (hW : W ≤ (ProjSpace.stdCoverPullback φ).inter t ⊓ ProjSpace.pullbackChart φ i),
      ProjSpace.restrictFun (hW.trans (inf_le_inf_right _ ((ProjSpace.stdCoverPullback φ).inter_le_inter_face t 0))) ((c ((ProjSpace.stdCoverPullback φ).face t 0)).val i)
        = ProjSpace.restrictFun (hW.trans (inf_le_inf_right _ ((ProjSpace.stdCoverPullback φ).inter_le_inter_face t 1))) ((c ((ProjSpace.stdCoverPullback φ).face t 1)).val i) := by
    intro t i W hW
    have h0 : (ProjSpace.twist (φ ≫ ProjSpace.π A n) φ m).d (ProjSpace.stdCoverPullback φ) 0 c t = 0 := by
      rw [LinearMap.mem_ker.mp hc]; rfl
    rw [OModulePresheaf.d_apply, Fin.sum_univ_two] at h0
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, add_neg_eq_zero] at h0

    have h1 := congrArg (fun g : ProjSpace.twistObj (φ ≫ ProjSpace.π A n) φ m ((ProjSpace.stdCoverPullback φ).inter t) => g.val i) h0
    simp only [ProjSpace.twist_res_val] at h1
    have h2 := congrArg (ProjSpace.restrictFun hW) h1
    rw [ProjSpace.restrictFun_restrictFun, ProjSpace.restrictFun_restrictFun] at h2
    exact h2

  have hcov : ∀ (V : Z.Opens) (i : Fin (n + 1)), V ⊓ ProjSpace.pullbackChart φ i ≤ ⨆ s : (ProjSpace.stdCoverPullback φ).Idx 0, ((ProjSpace.stdCoverPullback φ).inter s ⊓ ProjSpace.pullbackChart φ i) := by
    intro V i x hx
    have hx' : x ∈ (⊤ : Z.Opens) := trivial
    rw [← (ProjSpace.stdCoverPullback φ).iSup_eq_top, TopologicalSpace.Opens.mem_iSup] at hx'
    obtain ⟨a, ha⟩ := hx'
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨single φ a.down, ?_⟩
    refine ⟨?_, hx.2⟩
    rw [inter_single, ProjSpace.pullbackChart_eq]
    rw [ProjSpace.stdCoverPullback_U, ProjSpace.stdCover_U] at ha
    exact ha

  have hcompat : ∀ (i : Fin (n + 1)) (s s' : (ProjSpace.stdCoverPullback φ).Idx 0) (W : Z.Opens)
      (h : W ≤ (ProjSpace.stdCoverPullback φ).inter s ⊓ ProjSpace.pullbackChart φ i) (h' : W ≤ (ProjSpace.stdCoverPullback φ).inter s' ⊓ ProjSpace.pullbackChart φ i),
      ProjSpace.restrictFun h ((c s).val i) = ProjSpace.restrictFun h' ((c s').val i) := by
    intro i s s' W h h'
    have hs := eq_single φ s
    have hs' := eq_single φ s'
    rcases lt_trichotomy (s.1 0).down (s'.1 0).down with hlt | heq | hgt
    ·
      let t := pair φ _ _ hlt
      have hWt : W ≤ (ProjSpace.stdCoverPullback φ).inter t ⊓ ProjSpace.pullbackChart φ i := by
        refine le_inf ?_ (h.trans inf_le_right)
        refine (le_inf (h.trans inf_le_left) (h'.trans inf_le_left)).trans ?_
        rw [hs, hs']
        exact inter_single_inf_le_inter_pair φ _ _ hlt
      have e0 : (ProjSpace.stdCoverPullback φ).face t 0 = s' := (face_pair_zero φ _ _ hlt).trans hs'.symm
      have e1 : (ProjSpace.stdCoverPullback φ).face t 1 = s := (face_pair_one φ _ _ hlt).trans hs.symm
      rw [hC i s _ e1.symm W h (hWt.trans (inf_le_inf_right _ ((ProjSpace.stdCoverPullback φ).inter_le_inter_face t 1))),
        hC i s' _ e0.symm W h' (hWt.trans (inf_le_inf_right _ ((ProjSpace.stdCoverPullback φ).inter_le_inter_face t 0)))]
      exact (hcyc t i W hWt).symm
    ·
      have : s = s' := by rw [hs, hs', heq]
      exact hC i s s' this W h h'
    · let t := pair φ _ _ hgt
      have hWt : W ≤ (ProjSpace.stdCoverPullback φ).inter t ⊓ ProjSpace.pullbackChart φ i := by
        refine le_inf ?_ (h.trans inf_le_right)
        refine (le_inf (h'.trans inf_le_left) (h.trans inf_le_left)).trans ?_
        rw [hs, hs']
        exact inter_single_inf_le_inter_pair φ _ _ hgt
      have e0 : (ProjSpace.stdCoverPullback φ).face t 0 = s := (face_pair_zero φ _ _ hgt).trans hs.symm
      have e1 : (ProjSpace.stdCoverPullback φ).face t 1 = s' := (face_pair_one φ _ _ hgt).trans hs'.symm
      rw [hC i s _ e0.symm W h (hWt.trans (inf_le_inf_right _ ((ProjSpace.stdCoverPullback φ).inter_le_inter_face t 0))),
        hC i s' _ e1.symm W h' (hWt.trans (inf_le_inf_right _ ((ProjSpace.stdCoverPullback φ).inter_le_inter_face t 1)))]
      exact hcyc t i W hWt

  have hglue : ∀ i : Fin (n + 1), ∃ gi : Γ(Z, (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i),
      ∀ s : (ProjSpace.stdCoverPullback φ).Idx 0, ProjSpace.restrictFun (inf_le_inf_right (ProjSpace.pullbackChart φ i) le_top :
        (ProjSpace.stdCoverPullback φ).inter s ⊓ ProjSpace.pullbackChart φ i ≤ (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i) gi = (c s).val i := by
    intro i
    have := Z.sheaf.existsUnique_gluing' (fun s : (ProjSpace.stdCoverPullback φ).Idx 0 => (ProjSpace.stdCoverPullback φ).inter s ⊓ ProjSpace.pullbackChart φ i)
      ((⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i) (fun s => homOfLE (inf_le_inf_right (ProjSpace.pullbackChart φ i) le_top)) (hcov ⊤ i)
      (fun s => (c s).val i) (fun s s' => hcompat i s s' _ inf_le_left inf_le_right)
    obtain ⟨gi, hgi, -⟩ := this
    exact ⟨gi, hgi⟩
  choose gf hgf using hglue

  have hTC : ProjSpace.TwistCompat φ m ⊤ gf := by
    intro i j
    apply Z.sheaf.eq_of_locally_eq' (fun s : (ProjSpace.stdCoverPullback φ).Idx 0 => ((ProjSpace.stdCoverPullback φ).inter s ⊓ ProjSpace.pullbackChart φ i) ⊓ ProjSpace.pullbackChart φ j)
      (((⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i) ⊓ ProjSpace.pullbackChart φ j)
      (fun s => homOfLE (inf_le_inf_right _ (inf_le_inf_right _ le_top)))
    ·
      intro x hx
      have := hcov ⊤ i ⟨hx.1.1, hx.1.2⟩
      rw [TopologicalSpace.Opens.mem_iSup] at this ⊢
      obtain ⟨s, hs⟩ := this
      exact ⟨s, hs, hx.2⟩
    · intro s
      show ProjSpace.restrictFun _ (ProjSpace.restrictFun _ (gf i)) =
        ProjSpace.restrictFun _ (ProjSpace.restrictFun _ (ProjSpace.frameUnit φ i j) ^ m * ProjSpace.restrictFun _ (gf j))
      rw [map_mul, map_pow, ProjSpace.restrictFun_restrictFun, ProjSpace.restrictFun_restrictFun,
        ProjSpace.restrictFun_restrictFun]
      have hi : ProjSpace.restrictFun ((inf_le_left.trans (inf_le_inf_right (ProjSpace.pullbackChart φ i) le_top)) :
          ((ProjSpace.stdCoverPullback φ).inter s ⊓ ProjSpace.pullbackChart φ i) ⊓ ProjSpace.pullbackChart φ j ≤ (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i) (gf i)
          = ProjSpace.restrictFun inf_le_left ((c s).val i) := by
        rw [← hgf i s, ProjSpace.restrictFun_restrictFun]
      have hj : ProjSpace.restrictFun ((le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans
            (inf_le_inf_right (ProjSpace.pullbackChart φ j) le_top) :
          ((ProjSpace.stdCoverPullback φ).inter s ⊓ ProjSpace.pullbackChart φ i) ⊓ ProjSpace.pullbackChart φ j ≤ (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ j) (gf j)
          = ProjSpace.restrictFun (le_inf (inf_le_left.trans inf_le_left) inf_le_right) ((c s).val j) := by
        rw [← hgf j s, ProjSpace.restrictFun_restrictFun]
      rw [hi, hj]
      exact (c s).compat i j
  refine ⟨⟨gf, hTC⟩, fun s => ?_⟩
  apply ProjSpace.twistObj.ext
  funext i
  rw [ProjSpace.twist_res_val]
  exact hgf i s

end S_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist (solution)
