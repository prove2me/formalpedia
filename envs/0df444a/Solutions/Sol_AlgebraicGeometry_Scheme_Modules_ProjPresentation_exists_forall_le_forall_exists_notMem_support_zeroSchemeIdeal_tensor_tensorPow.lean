-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_forall_le_forall_exists_notMem_support_zeroSchemeIdeal_tensor_tensorPow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/36963064-360c-56b7-a94d-258b2a6f9272

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_mem_preimage_basicOpen_iff
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_le_forall_exists_notMem_support_zeroSchemeIdeal_tensor_tensorPow
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite"

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace P2mSerreA

open AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Res

variable {M : X.Modules}

def rM (M : X.Modules) {U V : X.Opens} (h : V ≤ U) (m : Γ(M, U)) : Γ(M, V) :=
  M.presheaf.map (homOfLE h).op m

def rX {U V : X.Opens} (h : V ≤ U) (g : Γ(X, U)) : Γ(X, V) :=
  X.presheaf.map (homOfLE h).op g

lemma rM_def {U V : X.Opens} (h : V ≤ U) (m : Γ(M, U)) : rM M h m = M.presheaf.map (homOfLE h).op m := rfl

lemma rX_def {U V : X.Opens} (h : V ≤ U) (g : Γ(X, U)) : rX h g = X.presheaf.map (homOfLE h).op g := rfl

lemma rM_rM {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (m : Γ(M, U)) :
    rM M h₂ (rM M h₁ m) = rM M (h₂.trans h₁) m := by
  change (M.presheaf.map _ ≫ M.presheaf.map _) m = _
  rw [← M.presheaf.map_comp]
  rfl

lemma rX_rX {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (g : Γ(X, U)) :
    rX h₂ (rX h₁ g) = rX (h₂.trans h₁) g := by
  change (X.presheaf.map _ ≫ X.presheaf.map _) g = _
  rw [← X.presheaf.map_comp]
  rfl

lemma rM_refl {U : X.Opens} (h : U ≤ U) (m : Γ(M, U)) : rM M h m = m := by
  change M.presheaf.map (homOfLE h).op m = m
  rw [Subsingleton.elim (homOfLE h).op (𝟙 (op U)), M.presheaf.map_id]
  rfl

lemma rX_refl {U : X.Opens} (h : U ≤ U) (g : Γ(X, U)) : rX h g = g := by
  change X.presheaf.map (homOfLE h).op g = g
  rw [Subsingleton.elim (homOfLE h).op (𝟙 (op U)), X.presheaf.map_id]
  rfl

lemma rM_smul {U V : X.Opens} (h : V ≤ U) (g : Γ(X, U)) (m : Γ(M, U)) :
    rM M h (g • m) = rX h g • rM M h m :=
  Scheme.Modules.map_smul M _ g m

lemma rM_add {U V : X.Opens} (h : V ≤ U) (m m' : Γ(M, U)) :
    rM M h (m + m') = rM M h m + rM M h m' := map_add _ _ _

lemma rM_sub {U V : X.Opens} (h : V ≤ U) (m m' : Γ(M, U)) :
    rM M h (m - m') = rM M h m - rM M h m' := map_sub _ _ _

lemma rM_zero {U V : X.Opens} (h : V ≤ U) : rM M h (0 : Γ(M, U)) = 0 := map_zero _

lemma rX_mul {U V : X.Opens} (h : V ≤ U) (g g' : Γ(X, U)) : rX h (g * g') = rX h g * rX h g' :=
  map_mul _ _ _

lemma rX_pow {U V : X.Opens} (h : V ≤ U) (g : Γ(X, U)) (n : ℕ) : rX h (g ^ n) = rX h g ^ n :=
  map_pow _ _ _

lemma rX_one {U V : X.Opens} (h : V ≤ U) : rX h (1 : Γ(X, U)) = 1 := map_one _

lemma rM_injective_of_eq {U V : X.Opens} (e : V = U) (h : V ≤ U) : Function.Injective (rM M h) := by
  subst e
  intro a b hab
  rwa [rM_refl, rM_refl] at hab

lemma tensorPowSection_smul' {L : X.Modules} {U : X.Opens} (g : Γ(X, U)) (s : Γ(L, U)) (n : ℕ) :
    tensorPowSection (g • s) n = g ^ n • tensorPowSection s n := by
  induction n with
  | zero => rw [tensorPowSection_zero, tensorPowSection_zero, pow_zero, one_smul]
  | succ n ih =>
    rw [tensorPowSection_succ, tensorPowSection_succ, ih, tensorSections_smul_left,
      tensorSections_smul_right, smul_smul, pow_succ]
    rfl

lemma tensorSections_sub_left {L N' : X.Modules} {U : X.Opens} (s s' : Γ(L, U)) (t : Γ(N', U)) :
    tensorSections (s - s') t = tensorSections s t - tensorSections s' t := by
  rw [sub_eq_add_neg, tensorSections_add_left, tensorSections_neg_left, ← sub_eq_add_neg]

lemma rM_tensorSections {L N' : X.Modules} {U V : X.Opens} (h : V ≤ U) (s : Γ(L, U)) (t : Γ(N', U)) :
    rM (L ⊗ N') h (tensorSections s t) = tensorSections (rM L h s) (rM N' h t) :=
  map_homOfLE_tensorSections h s t

lemma rM_tensorPowSection {L : X.Modules} {U V : X.Opens} (h : V ≤ U) (s : Γ(L, U)) (n : ℕ) :
    rM (L.tensorPow n) h (tensorPowSection s n) = tensorPowSection (rM L h s) n :=
  map_tensorPowSection (homOfLE h) s n

lemma frame_of_rM {U U' V : X.Opens} {s : Γ(M, U)} (h : U' ≤ U) (hV : V ≤ U')
    (hs : IsFrameOn (rM M h s) V) : IsFrameOn s V := by
  intro W hWU hWV
  have e : M.presheaf.map (homOfLE hWU).op s = M.presheaf.map (homOfLE (hWV.trans hV)).op (rM M h s) :=
    (rM_rM h (hWV.trans hV) s).symm
  simp only [e]
  exact hs (hWV.trans hV) hWV

lemma frame_unit_smul {U V : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s V) {c : Γ(X, U)}
    (hc : IsUnit c) : IsFrameOn (c • s) V := by
  intro W hWU hWV
  have e : M.presheaf.map (homOfLE hWU).op (c • s) = rX hWU c • M.presheaf.map (homOfLE hWU).op s :=
    Scheme.Modules.map_smul M _ c s
  simp only [e]
  have hcu : IsUnit (rX hWU c) := hc.map (X.presheaf.map (homOfLE hWU).op).hom
  have : (fun a : Γ(X, W) => a • (rX hWU c • M.presheaf.map (homOfLE hWU).op s)) =
      (fun a : Γ(X, W) => a • M.presheaf.map (homOfLE hWU).op s) ∘ fun a => a * rX hWU c := by
    funext a
    simp only [Function.comp_apply, mul_smul]
  rw [this]
  exact (hs hWU hWV).comp (Units.mulRight hcu.unit).bijective

end Res

section Charts

variable {R : Type u} [CommRing R] {H : X.Modules} {N : ℕ} {f : X ⟶ Spec (.of R)}
  (𝔓 : H.ProjPresentation f N)

abbrev U (i : Fin (N + 1)) : X.Opens := ProjSpace.pullbackChart 𝔓.toProj i

abbrev u (i j : Fin (N + 1)) : Γ(X, U 𝔓 i) := ProjSpace.frameUnit 𝔓.toProj i j

abbrev σU (i : Fin (N + 1)) : Γ(H, U 𝔓 i) := rM H le_top (𝔓.σ i)

lemma frame_σ (i : Fin (N + 1)) : IsFrameOn (𝔓.σ i) (U 𝔓 i) := fun W _ hWi => 𝔓.frame i W hWi

lemma frame_σU (i : Fin (N + 1)) : IsFrameOn (σU 𝔓 i) (U 𝔓 i) := (frame_σ 𝔓 i).map (homOfLE le_top)

lemma u_smul_σU (i j : Fin (N + 1)) : u 𝔓 i j • σU 𝔓 i = rM H (le_top : U 𝔓 i ≤ ⊤) (𝔓.σ j) :=
  𝔓.app_ratio_smul i j

lemma u_self (i : Fin (N + 1)) : u 𝔓 i i = 1 := ProjSpace.frameUnit_self _ i

lemma exists_mem_U (x : X) : ∃ i, x ∈ U 𝔓 i := by
  have hcov := (ProjSpace.stdCover R N).iSup_eq_top
  have hx : 𝔓.toProj.base x ∈ (⊤ : Opens _) := trivial
  rw [← hcov, Opens.mem_iSup] at hx
  obtain ⟨j, hj⟩ := hx
  exact ⟨j.down, hj⟩

lemma iSup_U : ⨆ i, U 𝔓 i = ⊤ :=
  top_le_iff.1 fun x _ => Opens.mem_iSup.2 (exists_mem_U 𝔓 x)

lemma cocycle (i j j' : Fin (N + 1)) :
    rX (inf_le_right : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j') (u 𝔓 j' j) * rX inf_le_left (u 𝔓 j i) =
      rX inf_le_right (u 𝔓 j' i) := by
  have hle : U 𝔓 j ⊓ U 𝔓 j' ≤ ProjSpace.pullbackOverlap 𝔓.toProj j' j := by
    rw [ProjSpace.pullbackOverlap_eq_inf]; exact le_inf inf_le_right inf_le_left
  have key := congrArg (rX hle) (ProjSpace.frameUnit_cocycle 𝔓.toProj j' j i)
  rw [rX_mul] at key
  change rX hle (rX _ _) * rX hle (rX _ _) = rX hle (rX _ _) at key
  rw [rX_rX, rX_rX, rX_rX] at key
  exact key

lemma isUnit_u (i j : Fin (N + 1)) : IsUnit (rX (inf_le_left : U 𝔓 i ⊓ U 𝔓 j ≤ U 𝔓 i) (u 𝔓 i j)) := by
  have hle : U 𝔓 i ⊓ U 𝔓 j ≤ ProjSpace.pullbackOverlap 𝔓.toProj i j := by
    rw [ProjSpace.pullbackOverlap_eq_inf]
  have key := (ProjSpace.isUnit_restrictFun_frameUnit 𝔓.toProj i j).map (X.presheaf.map (homOfLE hle).op).hom
  change IsUnit (rX hle (rX _ _)) at key
  rwa [rX_rX] at key

private lemma _root_.P2mSerreA.isUnit_res_basicOpen {V : X.Opens} (r : Γ(X, V)) : IsUnit (rX (X.basicOpen_le r) r) :=
  RingedSpace.isUnit_res_basicOpen _ r

p2m_export "P2mSerreA" "isUnit_res_basicOpen"

lemma basicOpen_u (j i : Fin (N + 1)) : X.basicOpen (u 𝔓 j i) = U 𝔓 j ⊓ U 𝔓 i := by
  apply le_antisymm
  ·
    intro x hx
    refine ⟨X.basicOpen_le _ hx, ?_⟩
    have hB : X.basicOpen (u 𝔓 j i) ≤ U 𝔓 j := X.basicOpen_le _
    have hfr : IsFrameOn (rM H (hB.trans le_top) (𝔓.σ i)) (X.basicOpen (u 𝔓 j i)) := by
      have e : rM H (hB.trans le_top) (𝔓.σ i) = rX hB (u 𝔓 j i) • rM H (hB.trans le_top) (𝔓.σ j) := by
        rw [← rM_rM le_top hB, ← u_smul_σU, rM_smul, rM_rM]
      rw [e]
      exact frame_unit_smul (((frame_σ 𝔓 j).map (homOfLE (hB.trans le_top))).mono hB)
        (isUnit_res_basicOpen _)
    refine (𝔓.mem_preimage_basicOpen_iff i x).2 ⟨X.basicOpen (u 𝔓 j i), hx, fun V hV => ?_⟩
    have := hfr hV hV
    have e : H.presheaf.map (homOfLE hV).op (rM H (hB.trans le_top) (𝔓.σ i)) =
        H.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (𝔓.σ i) := rM_rM _ _ _
    simpa only [e] using this
  · intro x hx
    have hu := isUnit_u 𝔓 j i
    have e := X.basicOpen_of_isUnit hu
    rw [rX_def, Scheme.basicOpen_res] at e
    exact ((le_of_eq e.symm) hx).2

lemma basicOpen_u_le (j i : Fin (N + 1)) : X.basicOpen (u 𝔓 j i) ≤ U 𝔓 i := by
  rw [basicOpen_u]; exact inf_le_right

lemma basicOpen_u_self (i : Fin (N + 1)) : X.basicOpen (u 𝔓 i i) = U 𝔓 i := by
  rw [basicOpen_u]; exact inf_idem _

variable [IsAffineHom 𝔓.toProj]

lemma affU (i : Fin (N + 1)) : IsAffineOpen (U 𝔓 i) := ProjSpace.isAffineOpen_pullbackChart _ i

lemma affUU (i j : Fin (N + 1)) : IsAffineOpen (U 𝔓 i ⊓ U 𝔓 j) := by
  rw [← ProjSpace.pullbackOverlap_eq_inf]; exact ProjSpace.isAffineOpen_pullbackOverlap _ i j

include 𝔓 in
omit [IsAffineHom 𝔓.toProj] in

lemma isInvertible_H : Scheme.Modules.IsInvertible H :=
  ⟨fun x => by
    obtain ⟨i, hi⟩ := exists_mem_U 𝔓 x
    exact ⟨U 𝔓 i, hi, (frame_σU 𝔓 i).nonempty_pullback_iso_unit (U 𝔓 i) le_rfl le_rfl⟩⟩

end Charts

section Ext

variable {R : Type u} [CommRing R] {H : X.Modules} {N : ℕ} {f : X ⟶ Spec (.of R)}
  (𝔓 : H.ProjPresentation f N) [IsAffineHom 𝔓.toProj]
  (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)

omit [IsAffineHom 𝔓.toProj] in

lemma σU_overlap (j j' : Fin (N + 1)) :
    rM H (inf_le_left : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j) (σU 𝔓 j) =
      rX (inf_le_right : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j') (u 𝔓 j' j) •
        rM H (inf_le_right : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j') (σU 𝔓 j') := by
  rw [rM_rM, ← rM_smul, u_smul_σU, rM_rM]

include hL in

lemma numerators (i : Fin (N + 1)) (m : Γ(L, U 𝔓 i)) :
    ∃ (k : ℕ) (m' : ∀ j, Γ(L, U 𝔓 j)), ∀ j,
      rM L (X.basicOpen_le (u 𝔓 j i)) (m' j) =
        rX (X.basicOpen_le (u 𝔓 j i)) (u 𝔓 j i ^ k) • rM L (basicOpen_u_le 𝔓 j i) m := by
  have h1 : ∀ j, ∃ (k : ℕ) (y : Γ(L, U 𝔓 j)), rM L (X.basicOpen_le (u 𝔓 j i)) y =
      rX (X.basicOpen_le (u 𝔓 j i)) (u 𝔓 j i ^ k) • rM L (basicOpen_u_le 𝔓 j i) m := fun j =>
    (isLocalization_basicOpen_of_locallyTrivial L hL.exists_trivialization ⟨U 𝔓 j, affU 𝔓 j⟩
      (u 𝔓 j i)).1 (rM L (basicOpen_u_le 𝔓 j i) m)
  choose k y hy using h1
  refine ⟨Finset.univ.sup k, fun j => u 𝔓 j i ^ (Finset.univ.sup k - k j) • y j, fun j => ?_⟩
  rw [rM_smul, hy j, smul_smul, ← rX_mul, ← pow_add,
    Nat.sub_add_cancel (Finset.le_sup (f := k) (Finset.mem_univ j))]

omit [IsAffineHom 𝔓.toProj] in

def disc (k : ℕ) (m' : ∀ j, Γ(L, U 𝔓 j)) (j j' : Fin (N + 1)) : Γ(L, U 𝔓 j ⊓ U 𝔓 j') :=
  rX (inf_le_right : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j') (u 𝔓 j' j ^ k) •
      rM L (inf_le_left : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j) (m' j) -
    rM L (inf_le_right : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j') (m' j')

omit [IsAffineHom 𝔓.toProj] in

lemma disc_vanish (i : Fin (N + 1)) (k : ℕ) (m' : ∀ j, Γ(L, U 𝔓 j)) (m : Γ(L, U 𝔓 i))
    (hm' : ∀ j, rM L (X.basicOpen_le (u 𝔓 j i)) (m' j) =
      rX (X.basicOpen_le (u 𝔓 j i)) (u 𝔓 j i ^ k) • rM L (basicOpen_u_le 𝔓 j i) m)
    (j j' : Fin (N + 1)) :
    rM L (X.basicOpen_le (rX (inf_le_left : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j) (u 𝔓 j i)))
      (disc 𝔓 L k m' j j') = 0 := by
  have hTO : X.basicOpen (rX (inf_le_left : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j) (u 𝔓 j i)) ≤ U 𝔓 j ⊓ U 𝔓 j' :=
    X.basicOpen_le _
  have hTB : X.basicOpen (rX (inf_le_left : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j) (u 𝔓 j i)) ≤
      X.basicOpen (u 𝔓 j i) := by
    rw [rX_def, Scheme.basicOpen_res]; exact inf_le_right
  have hTi : X.basicOpen (rX (inf_le_left : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j) (u 𝔓 j i)) ≤ U 𝔓 i :=
    hTB.trans (basicOpen_u_le 𝔓 j i)
  have hTB' : X.basicOpen (rX (inf_le_left : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j) (u 𝔓 j i)) ≤
      X.basicOpen (u 𝔓 j' i) := by
    rw [basicOpen_u]; exact le_inf (hTO.trans inf_le_right) hTi
  have e1 : rM L (hTO.trans inf_le_left) (m' j) =
      rX (hTO.trans inf_le_left) (u 𝔓 j i) ^ k • rM L hTi m := by
    have := congrArg (rM L hTB) (hm' j)
    rw [rM_rM, rM_smul, rM_rM, rX_rX, rX_pow] at this
    exact this
  have e2 : rM L (hTO.trans inf_le_right) (m' j') =
      rX (hTO.trans inf_le_right) (u 𝔓 j' i) ^ k • rM L hTi m := by
    have := congrArg (rM L hTB') (hm' j')
    rw [rM_rM, rM_smul, rM_rM, rX_rX, rX_pow] at this
    exact this
  have e3 : rX (hTO.trans inf_le_right) (u 𝔓 j' j) * rX (hTO.trans inf_le_left) (u 𝔓 j i) =
      rX (hTO.trans inf_le_right) (u 𝔓 j' i) := by
    have := congrArg (rX hTO) (cocycle 𝔓 i j j')
    rw [rX_mul, rX_rX, rX_rX, rX_rX] at this
    exact this
  rw [disc, rM_sub, rM_smul, rM_rM, rM_rM, rX_rX, rX_pow, e1, e2, ← e3, smul_smul, ← mul_pow,
    sub_self]

include hL in

lemma killers (i : Fin (N + 1)) (k : ℕ) (m' : ∀ j, Γ(L, U 𝔓 j)) (m : Γ(L, U 𝔓 i))
    (hm' : ∀ j, rM L (X.basicOpen_le (u 𝔓 j i)) (m' j) =
      rX (X.basicOpen_le (u 𝔓 j i)) (u 𝔓 j i ^ k) • rM L (basicOpen_u_le 𝔓 j i) m) :
    ∃ e : ℕ, ∀ j j',
      rX (inf_le_left : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j) (u 𝔓 j i) ^ e • disc 𝔓 L k m' j j' = 0 := by
  have h : ∀ j j', ∃ e : ℕ,
      rX (inf_le_left : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j) (u 𝔓 j i) ^ e • disc 𝔓 L k m' j j' = 0 :=
    fun j j' => (isLocalization_basicOpen_of_locallyTrivial L hL.exists_trivialization
      ⟨U 𝔓 j ⊓ U 𝔓 j', affUU 𝔓 j j'⟩ _).2 _ (disc_vanish 𝔓 L i k m' m hm' j j')
  choose e he using h
  refine ⟨Finset.univ.sup fun p : Fin (N + 1) × Fin (N + 1) => e p.1 p.2, fun j j' => ?_⟩
  have hle : e j j' ≤ Finset.univ.sup fun p : Fin (N + 1) × Fin (N + 1) => e p.1 p.2 :=
    Finset.le_sup (f := fun p : Fin (N + 1) × Fin (N + 1) => e p.1 p.2) (Finset.mem_univ (j, j'))
  rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, he, smul_zero]

omit [IsAffineHom 𝔓.toProj] in

def tloc (i : Fin (N + 1)) (k : ℕ) (m' : ∀ j, Γ(L, U 𝔓 j)) (n : ℕ) (j : Fin (N + 1)) :
    Γ(L ⊗ H.tensorPow n, U 𝔓 j) :=
  u 𝔓 j i ^ (n - k) • tensorSections (m' j) (tensorPowSection (σU 𝔓 j) n)

omit [IsAffineHom 𝔓.toProj] in

lemma tloc_compat (i : Fin (N + 1)) (k : ℕ) (m' : ∀ j, Γ(L, U 𝔓 j)) (e : ℕ)
    (he : ∀ j j', rX (inf_le_left : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j) (u 𝔓 j i) ^ e • disc 𝔓 L k m' j j' = 0)
    (n : ℕ) (hn : k + e ≤ n) (j j' : Fin (N + 1)) :
    rM (L ⊗ H.tensorPow n) (inf_le_left : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j) (tloc 𝔓 L i k m' n j) =
      rM (L ⊗ H.tensorPow n) inf_le_right (tloc 𝔓 L i k m' n j') := by
  obtain ⟨d, rfl⟩ : ∃ d, n = k + e + d := ⟨n - (k + e), by omega⟩
  set a := rX (inf_le_right : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j') (u 𝔓 j' j) with ha
  set b := rX (inf_le_left : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j) (u 𝔓 j i) with hb
  set τ := tensorPowSection (rM H (inf_le_right : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j') (σU 𝔓 j')) (k + e + d)
    with hτ
  set μ := rM L (inf_le_left : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j) (m' j) with hμ
  set μ' := rM L (inf_le_right : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j') (m' j') with hμ'
  have hd : disc 𝔓 L k m' j j' = a ^ k • μ - μ' := by
    simp only [disc, rX_pow, ha, hμ, hμ']
  have hsub : k + e + d - k = e + d := by omega
  have lhs : rM (L ⊗ H.tensorPow (k + e + d)) inf_le_left (tloc 𝔓 L i k m' (k + e + d) j) =
      (b ^ (e + d) * a ^ (k + e + d)) • tensorSections μ τ := by
    rw [tloc, rM_smul, rX_pow, rM_tensorSections, rM_tensorPowSection, σU_overlap,
      tensorPowSection_smul', tensorSections_smul_right, smul_smul, hsub]
  have rhs : rM (L ⊗ H.tensorPow (k + e + d)) inf_le_right (tloc 𝔓 L i k m' (k + e + d) j') =
      (b ^ (e + d) * a ^ (e + d)) • tensorSections μ' τ := by
    rw [tloc, rM_smul, rX_pow, rM_tensorSections, rM_tensorPowSection, ← cocycle, hsub, mul_pow]
    congr 1
    exact mul_comm _ _
  rw [lhs, rhs]
  have hμ2 : a ^ k • μ = disc 𝔓 L k m' j j' + μ' := by rw [hd, sub_add_cancel]
  have hzero : (b ^ (e + d) * a ^ (e + d)) • tensorSections (disc 𝔓 L k m' j j') τ = 0 := by
    have : (b ^ (e + d) * a ^ (e + d)) • tensorSections (disc 𝔓 L k m' j j') τ =
        (b ^ d * a ^ (e + d)) • tensorSections (b ^ e • disc 𝔓 L k m' j j') τ := by
      rw [tensorSections_smul_left, smul_smul]
      congr 1
      ring
    rw [this, he j j', tensorSections_zero_left, smul_zero]
  calc (b ^ (e + d) * a ^ (k + e + d)) • tensorSections μ τ
      = (b ^ (e + d) * a ^ (e + d)) • tensorSections (a ^ k • μ) τ := by
        rw [tensorSections_smul_left, smul_smul]
        congr 1
        ring
    _ = (b ^ (e + d) * a ^ (e + d)) • tensorSections (disc 𝔓 L k m' j j') τ +
          (b ^ (e + d) * a ^ (e + d)) • tensorSections μ' τ := by
        rw [hμ2, tensorSections_add_left, smul_add]
    _ = (b ^ (e + d) * a ^ (e + d)) • tensorSections μ' τ := by rw [hzero, zero_add]

omit [IsAffineHom 𝔓.toProj] in

lemma glue (M : X.Modules) (t : ∀ j, Γ(M, U 𝔓 j))
    (ht : ∀ j j', rM M (inf_le_left : U 𝔓 j ⊓ U 𝔓 j' ≤ U 𝔓 j) (t j) = rM M inf_le_right (t j')) :
    ∃ s : Γ(M, ⊤), ∀ j, rM M le_top s = t j := by
  let F : TopCat.Sheaf Ab X.toTopCat := ⟨M.presheaf, Scheme.Modules.isSheaf M⟩
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' (fun j => U 𝔓 j) ⊤ (fun j => homOfLE le_top)
    (le_of_eq (iSup_U 𝔓).symm) t (fun j j' => ht j j')
  exact ⟨s, hs⟩

include hL in

lemma ext_frame (i : Fin (N + 1)) (m : Γ(L, U 𝔓 i)) {W : X.Opens} (hW : W ≤ U 𝔓 i)
    (hm : IsFrameOn m W) :
    ∃ n₁ : ℕ, ∀ n, n₁ ≤ n → ∃ t : Γ(L ⊗ H.tensorPow n, ⊤), IsFrameOn t W := by
  obtain ⟨k, m', hm'⟩ := numerators 𝔓 L hL i m
  obtain ⟨e, he⟩ := killers 𝔓 L hL i k m' m hm'
  refine ⟨k + e, fun n hn => ?_⟩
  obtain ⟨t, ht⟩ := glue 𝔓 (L ⊗ H.tensorPow n) (tloc 𝔓 L i k m' n)
    (tloc_compat 𝔓 L i k m' e he n hn)
  refine ⟨t, frame_of_rM (le_top : U 𝔓 i ≤ ⊤) hW ?_⟩
  have h1 : u 𝔓 i i ^ (n - k) = 1 := by rw [u_self, one_pow]
  rw [ht i, tloc, h1, one_smul]
  have hmi : m' i = m := by
    apply rM_injective_of_eq (M := L) (basicOpen_u_self 𝔓 i) (X.basicOpen_le (u 𝔓 i i))
    have h2 : u 𝔓 i i ^ k = 1 := by rw [u_self, one_pow]
    rw [hm' i, h2, rX_one, one_smul]
  rw [hmi]
  exact hm.tensorSections (((frame_σU 𝔓 i).tensorPowSection n).mono hW)

include hL in
lemma local_frame (i : Fin (N + 1)) (x : X) (hx : x ∈ U 𝔓 i) :
    ∃ (m : Γ(L, U 𝔓 i)) (W : X.Opens), x ∈ W ∧ W ≤ U 𝔓 i ∧ IsFrameOn m W := by
  obtain ⟨V, s, hxV, hs⟩ := hL.exists_isFrameOn x
  obtain ⟨r, hrV, hxr⟩ := (affU 𝔓 i).exists_basicOpen_le ⟨x, hxV⟩ hx
  obtain ⟨n, y, hy⟩ := (isLocalization_basicOpen_of_locallyTrivial L hL.exists_trivialization
    ⟨U 𝔓 i, affU 𝔓 i⟩ r).1 (rM L hrV s)
  refine ⟨y, X.basicOpen r, hxr, X.basicOpen_le r, frame_of_rM (X.basicOpen_le r) le_rfl ?_⟩
  change rM L (X.basicOpen_le r) y = rX (X.basicOpen_le r) (r ^ n) • rM L hrV s at hy
  rw [hy, rX_pow]
  exact frame_unit_smul ((hs.map (homOfLE hrV)).mono hrV) ((isUnit_res_basicOpen r).pow n)

include hL in
lemma finite_frames (i : Fin (N + 1)) :
    ∃ (ι : Type u) (T : Finset ι) (m : ι → Γ(L, U 𝔓 i)) (W : ι → X.Opens),
      (∀ l, W l ≤ U 𝔓 i ∧ IsFrameOn (m l) (W l)) ∧ ∀ x ∈ U 𝔓 i, ∃ l ∈ T, x ∈ W l := by
  choose m W hxW hWU hfr using local_frame 𝔓 L hL i
  obtain ⟨T, hT⟩ := (affU 𝔓 i).isCompact.elim_finite_subcover
    (fun p : U 𝔓 i => (W p.1 p.2 : Set X)) (fun p => (W p.1 p.2).isOpen)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxW x hx⟩)
  refine ⟨U 𝔓 i, T, fun p => m p.1 p.2, fun p => W p.1 p.2, fun p => ⟨hWU p.1 p.2, hfr p.1 p.2⟩,
    fun x hx => ?_⟩
  obtain ⟨p, hp⟩ := Set.mem_iUnion.1 (hT hx)
  obtain ⟨hpT, hxp⟩ := Set.mem_iUnion.1 hp
  exact ⟨p, hpT, hxp⟩

end Ext

section NonVanish

def homOfSection (M : X.Modules) (t : Γ(M, ⊤)) : 𝟙_ X.Modules ⟶ M :=
  M.unitHomEquiv.symm (PresheafOfModules.sectionsMk (M := M.val)
    (fun V => rM M (le_top : V.unop ≤ ⊤) t)
    (by
      intro V V' i
      change (M.presheaf.map _ ≫ M.presheaf.map i) t = _
      rw [← M.presheaf.map_comp]
      rfl))

lemma homOfSection_app (M : X.Modules) (t : Γ(M, ⊤)) :
    (homOfSection M t).app ⊤ (unitSection ⊤) = t := by
  have h1 : (M.unitHomEquiv (homOfSection M t)).val (op ⊤) = rM M le_top t := by
    rw [homOfSection, Equiv.apply_symm_apply]
    rfl
  have h2 : (homOfSection M t).app ⊤ (unitSection ⊤) = (M.unitHomEquiv (homOfSection M t)).val (op ⊤) :=
    rfl
  rw [h2, h1, rM_refl]

lemma not_bijective_smul_zero {Y : Scheme.{u}} [Nontrivial Γ(Y, ⊤)] {N' : Y.Modules} {r : Γ(N', ⊤)}
    (hr : r = 0) : ¬ Function.Bijective (fun g : Γ(Y, ⊤) => g • r) := by
  subst hr
  intro hb
  exact zero_ne_one (hb.1 (a₁ := 0) (a₂ := 1) (by simp only [smul_zero]))

scoped instance nontrivial_sections_spec_field (K : Type u) [Field K] : Nontrivial Γ(Spec (.of K), ⊤) :=
  (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial

lemma notMem_support_of_frame {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (t : Γ(M, ⊤))
    {W : X.Opens} {x : X} (hx : x ∈ W) (ht : IsFrameOn t W) :
    ∃ s : 𝟙_ X.Modules ⟶ M, x ∉ (Scheme.Modules.zeroSchemeIdeal s).support := by
  refine ⟨homOfSection M t, fun hmem => ?_⟩
  have hz : (X.fromSpecResidueField x).base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField (X.presheaf.stalk x))) = x :=
    X.fromSpecResidueField_apply x _
  have h0 : Scheme.Modules.pullbackSection (X.fromSpecResidueField x) (homOfSection M t) = 0 :=
    (Scheme.Modules.IsInvertible.pullbackSection_eq_zero_iff_mem_support hM (homOfSection M t)
      (X.fromSpecResidueField x)).2 (by convert hmem using 2; exact hz)
  have e0 : (Scheme.Modules.pullback (X.fromSpecResidueField x)).map (homOfSection M t) =
      (Scheme.Modules.pullbackUnitIso (X.fromSpecResidueField x)).hom ≫
        Scheme.Modules.pullbackSection (X.fromSpecResidueField x) (homOfSection M t) := by
    rw [Scheme.Modules.pullbackSection_def]
    exact (Iso.hom_inv_id_assoc _ _).symm
  have nat := (Scheme.Modules.pullbackPushforwardAdjunction (X.fromSpecResidueField x)).unit.naturality
    (homOfSection M t)
  have h3 : ((Scheme.Modules.pullbackPushforwardAdjunction (X.fromSpecResidueField x)).unit.app M).app ⊤
      t = 0 := by
    have := congrArg (fun φ => φ.app ⊤ (unitSection ⊤)) nat
    have e1 : (fun φ => φ.app ⊤ (unitSection ⊤)) ((𝟭 X.Modules).map (homOfSection M t) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction (X.fromSpecResidueField x)).unit.app M) =
        ((Scheme.Modules.pullbackPushforwardAdjunction (X.fromSpecResidueField x)).unit.app M).app ⊤ t := by
      show ((Scheme.Modules.pullbackPushforwardAdjunction (X.fromSpecResidueField x)).unit.app M).app ⊤
        ((homOfSection M t).app ⊤ (unitSection ⊤)) = _
      rw [homOfSection_app]
    beta_reduce at e1
    rw [e1, Functor.comp_map, e0, h0] at this
    exact this.trans rfl
  have hb := Scheme.Modules.bijective_smul_unit_app_of_bijective_smul (X.fromSpecResidueField x) M t
    (V := W) (fun W' hW' => ht le_top hW') ⊤ (fun p _ => by
      change (X.fromSpecResidueField x).base p ∈ W
      rw [Subsingleton.elim (α := PrimeSpectrum (IsLocalRing.ResidueField (X.presheaf.stalk x))) p
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField (X.presheaf.stalk x))), hz]
      exact hx)
  exact not_bijective_smul_zero (by rw [h3]; exact map_zero _) hb

end NonVanish

theorem main {R : Type u} [CommRing R] {H : X.Modules} {N : ℕ} {f : X ⟶ Spec (.of R)}
    (𝔓 : H.ProjPresentation f N) [IsAffineHom 𝔓.toProj]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ x : X,
      ∃ s : 𝟙_ X.Modules ⟶ L ⊗ H.tensorPow n, x ∉ (Scheme.Modules.zeroSchemeIdeal s).support := by
  choose ι T m W hW hcov using finite_frames 𝔓 L hL
  have hth : ∀ i (l : ι i), ∃ n₁ : ℕ, ∀ n, n₁ ≤ n →
      ∃ t : Γ(L ⊗ H.tensorPow n, ⊤), IsFrameOn t (W i l) :=
    fun i l => ext_frame 𝔓 L hL i (m i l) (hW i l).1 (hW i l).2
  choose n₁ hn₁ using hth
  refine ⟨Finset.univ.sup fun i => (T i).sup (n₁ i), fun n hn x => ?_⟩
  obtain ⟨i, hxi⟩ := exists_mem_U 𝔓 x
  obtain ⟨l, hlT, hxl⟩ := hcov i x hxi
  have hle : n₁ i l ≤ n :=
    le_trans (le_trans (Finset.le_sup (f := n₁ i) hlT)
      (Finset.le_sup (f := fun i => (T i).sup (n₁ i)) (Finset.mem_univ i))) hn
  obtain ⟨t, ht⟩ := hn₁ i l n hle
  exact notMem_support_of_frame (hL.tensor ((isInvertible_H 𝔓).tensorPow n)) t hxl ht

end P2mSerreA
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_le_forall_exists_notMem_support_zeroSchemeIdeal_tensor_tensorPow.P2mSerreA"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_le_forall_exists_notMem_support_zeroSchemeIdeal_tensor_tensorPow.P2mSerreA"

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    {H : X.Modules} {N : ℕ} (𝔓 : H.ProjPresentation f N) [IsAffineHom 𝔓.toProj]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ x : X,
      ∃ s : 𝟙_ X.Modules ⟶ L ⊗ H.tensorPow n, x ∉ (Scheme.Modules.zeroSchemeIdeal s).support :=
  P2mSerreA.main 𝔓 L hL

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_le_forall_exists_notMem_support_zeroSchemeIdeal_tensor_tensorPow
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_le_forall_exists_notMem_support_zeroSchemeIdeal_tensor_tensorPow (solution)
