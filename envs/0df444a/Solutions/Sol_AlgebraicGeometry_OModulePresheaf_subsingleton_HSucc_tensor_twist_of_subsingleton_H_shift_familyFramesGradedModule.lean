-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/1c563fc3-83c9-5cec-b641-af14e9ebdafc

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

local infixr:73 " ⨳ " => HSMul.hSMul

namespace P2mGrRetract

open AlgebraicGeometry.ProjSpace AlgebraicGeometry.OModulePresheaf HomogeneousLocalization ProjSpaceCech
open scoped TensorProduct

section Geometry

variable (A : Type u) [CommRing A] (N : ℕ)

theorem proj_basicOpen_awayToSection_ratio (j i : Fin (N + 1)) :
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)).basicOpen
        ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X j)).hom
          (ProjSpace.ratio A N j i))
      = Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)
          ((MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) * MvPolynomial.X i) := by
  set 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A with h𝒜
  set z : Away 𝒜 (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) := ProjSpace.ratio A N j i with hz
  have hkey : ∀ (x : Proj 𝒜) (hxj : x ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A)),
      IsUnit ((Proj 𝒜).presheaf.germ _ x hxj ((Proj.awayToSection 𝒜 (MvPolynomial.X j)).hom z))
        ↔ (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) A) ∉ x.asHomogeneousIdeal := by
    intro x hxj
    have hxj' : (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A)
        ∈ x.asHomogeneousIdeal.toIdeal.primeCompl := hxj
    have hgerm := congrArg (fun ψ => CommRingCat.Hom.hom ψ z)
      (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 (MvPolynomial.X j) x hxj)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hgerm
    erw [hgerm]
    haveI : IsLocalHom (Proj.stalkIso' 𝒜 x).toCommRingCatIso.inv.hom := isLocalHom_of_isIso _
    refine (isUnit_map_iff (Proj.stalkIso' 𝒜 x).toCommRingCatIso.inv.hom _).trans ?_
    rw [← HomogeneousLocalization.isUnit_iff_isUnit_val]
    have hval : (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hxj') z).val
        = Localization.mk (MvPolynomial.X i)
            ⟨(MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ 1, pow_mem hxj' 1⟩ := by
      simp only [hz, ProjSpace.ratio, HomogeneousLocalization.Away.mk, HomogeneousLocalization.mapId,
        HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
      rfl
    rw [show Submonoid.powers_le.mpr hxj = Submonoid.powers_le.mpr hxj' from rfl, hval,
      Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
    exact Iff.rfl
  ext x
  simp only [SetLike.mem_coe, Proj.basicOpen_mul, Proj.mem_basicOpen, Opens.mem_inf]
  refine ⟨fun hx => ?_, fun ⟨hxj, hxi⟩ => ?_⟩
  · have hxj : x ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) :=
      Scheme.basicOpen_le _ _ hx
    exact ⟨hxj, (hkey x hxj).mp ((Scheme.mem_basicOpen _ _ x hxj).mp hx)⟩
  · exact (Scheme.mem_basicOpen _ _ x hxj).mpr ((hkey x hxj).mpr hxi)

variable {A N} {X : Scheme.{u}} (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

theorem basicOpen_frameUnit (j i : Fin (N + 1)) : X.basicOpen (frameUnit φ j i) = pullbackOverlap φ j i := by
  have h := Scheme.preimage_basicOpen φ
    ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X j)).hom
      (ProjSpace.ratio A N j i))
  rw [proj_basicOpen_awayToSection_ratio] at h
  exact h.symm

theorem basicOpen_prod_frameUnit (j : Fin (N + 1)) {i : ℕ} (c : Fin (i + 1) → Fin (N + 1)) (s : Finset (Fin (i + 1))) :
    X.basicOpen (∏ v ∈ s, frameUnit φ j (c v)) = pullbackChart φ j ⊓ ⨅ v ∈ s, pullbackChart φ (c v) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Scheme.basicOpen_one]
    refine le_antisymm (le_inf le_rfl (le_iInf fun v => le_iInf fun hv => absurd hv (Finset.notMem_empty v))) inf_le_left
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul, ih, basicOpen_frameUnit, pullbackOverlap_eq_inf, Finset.iInf_insert]
    exact (inf_inf_distrib_left _ _ _).symm

theorem basicOpen_prod_frameUnit_univ (j : Fin (N + 1)) {i : ℕ} (c : Fin (i + 1) → Fin (N + 1)) :
    X.basicOpen (∏ v, frameUnit φ j (c v)) = pullbackChart φ j ⊓ ⨅ v, pullbackChart φ (c v) := by
  rw [basicOpen_prod_frameUnit]
  congr 1
  refine le_antisymm (le_iInf fun v => (iInf_le _ v).trans (iInf_le _ (Finset.mem_univ v)))
    (le_iInf fun v => le_iInf fun _ => iInf_le _ v)

end Geometry

section Simplex

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
  (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) [IsAffineHom ι]

abbrev 𝔘 : P.OrderedAffineCover := stdCoverPullback ι

variable {ι}

def c {i : ℕ} (s : (𝔘 ι).Idx i) (v : Fin (i + 1)) : Fin (r + 1) := (s.1 v).down

theorem c_injective {i : ℕ} (s : (𝔘 ι).Idx i) : Function.Injective (c s) := fun a b h => by
  have h' : s.1 a = s.1 b := by
    have : (s.1 a).down = (s.1 b).down := h
    exact ULift.ext _ _ this
  exact s.2.injective h'

def ch {i : ℕ} (s : (𝔘 ι).Idx i) : Fin (r + 1) := c s 0

def toIdx {i : ℕ} (s : (𝔘 ι).Idx i) : ProjSpaceCech.Idx r i := ⟨c s, fun _ _ h => s.2 h⟩

def ofIdx {i : ℕ} (σ : ProjSpaceCech.Idx r i) : (𝔘 ι).Idx i := ⟨fun v => ULift.up (σ.1 v), fun _ _ h => σ.2 h⟩

theorem toIdx_ofIdx {i : ℕ} (σ : ProjSpaceCech.Idx r i) : toIdx (ofIdx (ι := ι) σ) = σ := rfl
theorem ofIdx_toIdx {i : ℕ} (s : (𝔘 ι).Idx i) : ofIdx (toIdx s) = s := rfl
theorem toIdx_face {i : ℕ} (s : (𝔘 ι).Idx (i + 1)) (t : Fin (i + 2)) :
    toIdx ((𝔘 ι).face s t) = ProjSpaceCech.Idx.face r (toIdx s) t := rfl
theorem ofIdx_face {i : ℕ} (σ : ProjSpaceCech.Idx r (i + 1)) (t : Fin (i + 2)) :
    ofIdx (ι := ι) (ProjSpaceCech.Idx.face r σ t) = (𝔘 ι).face (ofIdx σ) t := rfl

abbrev I {i : ℕ} (s : (𝔘 ι).Idx i) : Finset (Fin (r + 1)) := ProjSpaceCech.Idx.img r (toIdx s)

theorem mem_I_iff {i : ℕ} (s : (𝔘 ι).Idx i) (l : Fin (r + 1)) : l ∈ I s ↔ ∃ v, c s v = l := by
  simp only [I, ProjSpaceCech.Idx.img, toIdx, Finset.mem_image, Finset.mem_univ, true_and]

theorem c_mem_I {i : ℕ} (s : (𝔘 ι).Idx i) (v : Fin (i + 1)) : c s v ∈ I s := (mem_I_iff s _).mpr ⟨v, rfl⟩

theorem ch_mem_I {i : ℕ} (s : (𝔘 ι).Idx i) : ch s ∈ I s := c_mem_I s 0

theorem card_I {i : ℕ} (s : (𝔘 ι).Idx i) : (I s).card = i + 1 := ProjSpaceCech.Idx.card_img r (toIdx s)

abbrev W {i : ℕ} (s : (𝔘 ι).Idx i) : P.Opens := ⨅ v, pullbackChart ι (c s v)

theorem inter_eq {i : ℕ} (s : (𝔘 ι).Idx i) : (𝔘 ι).inter s = W s := rfl

theorem W_le {i : ℕ} (s : (𝔘 ι).Idx i) (v : Fin (i + 1)) : W s ≤ pullbackChart ι (c s v) := iInf_le _ v

theorem W_le_ch {i : ℕ} (s : (𝔘 ι).Idx i) : W s ≤ pullbackChart ι (ch s) := W_le s 0

theorem W_le_of_mem {i : ℕ} (s : (𝔘 ι).Idx i) {l : Fin (r + 1)} (hl : l ∈ I s) : W s ≤ pullbackChart ι l := by
  obtain ⟨v, rfl⟩ := (mem_I_iff s l).mp hl
  exact W_le s v

theorem W_le_overlap {i : ℕ} (s : (𝔘 ι).Idx i) {l : Fin (r + 1)} (hl : l ∈ I s) :
    W s ≤ pullbackOverlap ι (ch s) l := by
  rw [pullbackOverlap_eq_inf]; exact le_inf (W_le_ch s) (W_le_of_mem s hl)

theorem W_face_le {i : ℕ} (s : (𝔘 ι).Idx (i + 1)) (t : Fin (i + 2)) : W s ≤ W ((𝔘 ι).face s t) :=
  (𝔘 ι).inter_le_inter_face s t

def uW {i : ℕ} (s : (𝔘 ι).Idx i) (l : Fin (r + 1)) : Γ(P, W s) := restrictFun (W_le_ch s) (frameUnit ι (ch s) l)

theorem isUnit_uW {i : ℕ} (s : (𝔘 ι).Idx i) {l : Fin (r + 1)} (hl : l ∈ I s) : IsUnit (uW s l) := by
  have h := (isUnit_restrictFun_frameUnit ι (ch s) l).map (restrictFun (W_le_overlap s hl))
  rwa [restrictFun_restrictFun] at h

theorem uW_self {i : ℕ} (s : (𝔘 ι).Idx i) : uW s (ch s) = 1 := by
  rw [uW, frameUnit_self, map_one]

variable (ι) in

def uprod (j : Fin (r + 1)) (a : Fin (r + 1) → ℕ) : Γ(P, pullbackChart ι j) := ∏ l, frameUnit ι j l ^ a l

theorem uprod_add (j : Fin (r + 1)) (a b : Fin (r + 1) → ℕ) : uprod ι j (a + b) = uprod ι j a * uprod ι j b := by
  simp only [uprod, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem uprod_zero (j : Fin (r + 1)) : uprod ι j 0 = 1 := by
  simp only [uprod, Pi.zero_apply, pow_zero, Finset.prod_const_one]

def uPow {i : ℕ} (s : (𝔘 ι).Idx i) (a : Fin (r + 1) → ℕ) : Γ(P, W s) := ∏ l, uW s l ^ a l

theorem uPow_eq {i : ℕ} (s : (𝔘 ι).Idx i) (a : Fin (r + 1) → ℕ) : uPow s a = restrictFun (W_le_ch s) (uprod ι (ch s) a) := by
  simp only [uPow, uprod, uW, map_prod, map_pow]

theorem uPow_add {i : ℕ} (s : (𝔘 ι).Idx i) (a b : Fin (r + 1) → ℕ) : uPow s (a + b) = uPow s a * uPow s b := by
  simp only [uPow, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem isUnit_uPow {i : ℕ} (s : (𝔘 ι).Idx i) (a : Fin (r + 1) → ℕ) (ha : ∀ l ∉ I s, a l = 0) : IsUnit (uPow s a) := by
  refine Finset.prod_induction _ IsUnit (fun _ _ hx hy => hx.mul hy) isUnit_one fun l _ => ?_
  by_cases hl : l ∈ I s
  · exact (isUnit_uW s hl).pow _
  · rw [ha l hl, pow_zero]; exact isUnit_one

def aN {i : ℕ} (s : (𝔘 ι).Idx i) (n : ℕ) : Fin (r + 1) → ℕ := fun l => if l ∈ I s then n else 0

theorem aN_supp {i : ℕ} (s : (𝔘 ι).Idx i) (n : ℕ) : ∀ l ∉ I s, aN s n l = 0 := fun l hl => if_neg hl

theorem sum_aN {i : ℕ} (s : (𝔘 ι).Idx i) (n : ℕ) : (∑ l, aN s n l) = n * (i + 1) := by
  simp only [aN]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, card_I, smul_eq_mul, mul_comm]

theorem uprod_aN (j : Fin (r + 1)) {i : ℕ} (s : (𝔘 ι).Idx i) (n : ℕ) :
    uprod ι j (aN s n) = (∏ v, frameUnit ι j (c s v)) ^ n := by
  simp only [uprod, aN]
  rw [← Finset.prod_pow]
  have h1 : (∏ l, frameUnit ι j l ^ (if l ∈ I s then n else 0)) = ∏ l ∈ I s, frameUnit ι j l ^ n := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun l => l ∈ I s)]
    have h2 : (∏ l ∈ Finset.univ.filter (fun l => l ∉ I s), frameUnit ι j l ^ (if l ∈ I s then n else 0)) = 1 :=
      Finset.prod_eq_one fun l hl => by rw [if_neg (Finset.mem_filter.mp hl).2, pow_zero]
    rw [h2, mul_one, Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact Finset.prod_congr rfl fun l hl => by rw [if_pos hl]
  rw [h1, show I s = Finset.univ.image (c s) from rfl, Finset.prod_image fun a _ b _ h => c_injective s h]

end Simplex

section Family

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}

abbrev Md (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) [IsAffineHom ι]
    {q : P ⟶ Spec (CommRingCat.of A)} {G : ℕ → OModulePresheaf q}
    {ny : ℕ} {θ : Fin ny → ∀ k : ℕ, AffHom (G k) (G (k + 1))} (hθ : YComm G θ) (d : ℕ) :
    GradedModule (MvPolynomial (Fin ny) A) r :=
  (familyFramesGradedModule ι G θ hθ).shift (d : ℤ)

variable {ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)} [IsAffineHom ι]
  {q : P ⟶ Spec (CommRingCat.of A)} {G : ℕ → OModulePresheaf q}
  {ny : ℕ} {θ : Fin ny → ∀ k : ℕ, AffHom (G k) (G (k + 1))} {hθ : YComm G θ} {d k : ℕ}

theorem res_smul' (F : OModulePresheaf q) {U U' : P.Opens} (h : U ≤ U') (a : Γ(P, U')) (x : F.obj U') :
    F.res h (a ⨳ x) = restrictFun h a ⨳ F.res h x :=
  F.res_smul h a x

theorem res_res_eq_self (F : OModulePresheaf q) {V V' : P.Opens} (h : V ≤ V') (h' : V' ≤ V) (x : F.obj V) :
    F.res h (F.res h' x) = x := by
  rw [F.res_res]; exact F.res_refl_apply V x

variable (d) in

def degZ (a : Fin (r + 1) → ℕ) : ℤ := (∑ l, (a l : ℤ)) + (d : ℤ)

variable (d) in

def degN (a : Fin (r + 1) → ℕ) : ℕ := (∑ l, a l) + d

theorem degZ_eq (a : Fin (r + 1) → ℕ) : degZ d a = (degN d a : ℤ) := by
  simp only [degZ, degN, Nat.cast_add, Nat.cast_sum]

theorem degZ_nonneg (a : Fin (r + 1) → ℕ) : 0 ≤ degZ d a := by rw [degZ_eq]; exact Int.natCast_nonneg _

theorem toNat_degZ (a : Fin (r + 1) → ℕ) : (degZ d a).toNat = degN d a := by rw [degZ_eq, Int.toNat_natCast]

theorem sum_cast_add (a b : Fin (r + 1) → ℕ) : (∑ l, ((a + b) l : ℤ)) = (∑ l, (a l : ℤ)) + ∑ l, (b l : ℤ) := by
  simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]

theorem degN_add (a b : Fin (r + 1) → ℕ) : degN d (a + b) = degN d a + ∑ l, b l := by
  simp only [degN, Pi.add_apply, Finset.sum_add_distrib]; ring

theorem isHomogeneousElem_num {I : Finset (Fin (r + 1))} (x : GradedModule.Frac (Md ι hθ d) I) :
    IsHomogeneousElem ι G (degZ d x.denExp) x.num := x.hnum

theorem framesCompat_num {I : Finset (Fin (r + 1))} (x : GradedModule.Frac (Md ι hθ d) I) (k : ℕ) :
    FramesCompat ι (G k) (degN d x.denExp) (x.num (degZ d x.denExp) k) := by
  have h := (isHomogeneousElem_num x).2.2.1 (degZ_nonneg _) k
  rwa [toNat_degZ] at h

theorem monMul_apply_top (cc : Fin (r + 1) → ℕ) (f : (familyFramesGradedModule ι G θ hθ).M) (e : ℤ) (k : ℕ) (j : Fin (r + 1)) :
    GradedModule.monMul (Md ι hθ d) cc f (e + ∑ l, (cc l : ℤ)) k j = uprod ι j cc ⨳ f e k j := by
  show GradedModule.monMul (familyFramesGradedModule ι G θ hθ) cc f (e + ∑ l, (cc l : ℤ)) k j = _
  rw [monMul_apply, add_sub_cancel_right]; rfl

theorem rel_apply {I : Finset (Fin (r + 1))} {x y : GradedModule.Frac (Md ι hθ d) I} {cc : Fin (r + 1) → ℕ}
    (h : GradedModule.monMul (Md ι hθ d) (cc + y.denExp) x.num = GradedModule.monMul (Md ι hθ d) (cc + x.denExp) y.num)
    (k : ℕ) (j : Fin (r + 1)) :
    uprod ι j (cc + y.denExp) ⨳ x.num (degZ d x.denExp) k j = uprod ι j (cc + x.denExp) ⨳ y.num (degZ d y.denExp) k j := by
  have h1 := congrFun (congrFun (congrFun h (degZ d x.denExp + ∑ l, ((cc + y.denExp) l : ℤ))) k) j
  have e2 : degZ d x.denExp + ∑ l, ((cc + y.denExp) l : ℤ) = degZ d y.denExp + ∑ l, ((cc + x.denExp) l : ℤ) := by
    simp only [degZ, sum_cast_add]; ring
  rw [monMul_apply_top] at h1
  rw [h1, e2, monMul_apply_top]

theorem single_add' (e : ℤ) (g g' : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)) :
    FamilyFrames.single ι G e k (fun j => g j + g' j) = FamilyFrames.single ι G e k g + FamilyFrames.single ι G e k g' := by
  refine FamilyFrames.ext fun e' k' j => ?_
  rw [FamilyFrames.add_apply]
  by_cases he : e' = e
  · subst he
    by_cases hk : k' = k
    · subst hk; simp only [FamilyFrames.single_apply_self]
    · simp only [FamilyFrames.single_apply_of_ne_level _ _ hk, Pi.zero_apply, add_zero]
  · simp only [FamilyFrames.single_apply_of_ne_degree he, Pi.zero_apply, add_zero]

theorem single_congr {e e' : ℤ} (he : e = e') {g g' : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)} (hg : g = g') :
    FamilyFrames.single ι G e k g = FamilyFrames.single ι G e' k g' := by subst he hg; rfl

theorem monMul_single (cc : Fin (r + 1) → ℕ) (e : ℤ) (g : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)) :
    GradedModule.monMul (Md ι hθ d) cc (FamilyFrames.single ι G e k g)
      = FamilyFrames.single ι G (e + ∑ l, (cc l : ℤ)) k (fun j => uprod ι j cc ⨳ g j) := by
  refine FamilyFrames.ext fun e' k' j => ?_
  show GradedModule.monMul (familyFramesGradedModule ι G θ hθ) cc (FamilyFrames.single ι G e k g) e' k' j = _
  rw [monMul_apply]
  by_cases he : e' - ∑ l, (cc l : ℤ) = e
  · have he' : e' = e + ∑ l, (cc l : ℤ) := by rw [← he]; ring
    rw [he, he']
    by_cases hk : k' = k
    · subst hk; rw [FamilyFrames.single_apply_self, FamilyFrames.single_apply_self]; rfl
    · rw [FamilyFrames.single_apply_of_ne_level _ _ hk, FamilyFrames.single_apply_of_ne_level _ _ hk, Pi.zero_apply,
        smul_zero]
  · have he' : e' ≠ e + ∑ l, (cc l : ℤ) := fun h => he (by rw [h]; ring)
    rw [FamilyFrames.single_apply_of_ne_degree he, FamilyFrames.single_apply_of_ne_degree he', Pi.zero_apply,
      Pi.zero_apply, smul_zero]

theorem uprod_cocycle (j l : Fin (r + 1)) (cc : Fin (r + 1) → ℕ) :
    restrictFun (pullbackOverlap_le_left ι j l) (uprod ι j cc)
      = restrictFun (pullbackOverlap_le_left ι j l) (frameUnit ι j l) ^ (∑ m, cc m) *
          restrictFun (pullbackOverlap_le_right ι j l) (uprod ι l cc) := by
  simp only [uprod, map_prod, map_pow]
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun m _ => by rw [← mul_pow, frameUnit_cocycle]

theorem framesCompat_uprod_smul {F : OModulePresheaf q} {n : ℕ} {g : ∀ j : Fin (r + 1), F.obj (pullbackChart ι j)}
    (hg : FramesCompat ι F n g) (cc : Fin (r + 1) → ℕ) :
    FramesCompat ι F (n + ∑ m, cc m) (fun j => uprod ι j cc ⨳ g j) := by
  intro j l
  rw [res_smul', res_smul', hg j l, smul_smul, smul_smul, uprod_cocycle]
  congr 1
  ring

theorem single_mem_grade (a : Fin (r + 1) → ℕ) {g : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)}
    (hg : FramesCompat ι (G k) (degN d a) g) :
    FamilyFrames.single ι G (degZ d a) k g ∈ (Md ι hθ d).grade (∑ l, (a l : ℤ)) := by
  show IsHomogeneousElem ι G (degZ d a) (FamilyFrames.single ι G (degZ d a) k g)
  refine (isHomogeneousElem_single_iff _ _ _).mpr ⟨fun h => absurd h (not_lt.mpr (degZ_nonneg a)), fun _ => ?_⟩
  rw [toNat_degZ]; exact hg

def mkSec (I : Finset (Fin (r + 1))) (a : Fin (r + 1) → ℕ) (ha : ∀ l ∉ I, a l = 0)
    (g : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)) (hg : FramesCompat ι (G k) (degN d a) g) :
    GradedModule.sec (Md ι hθ d) I :=
  GradedModule.sec.mk (Md ι hθ d) I ⟨a, ha, FamilyFrames.single ι G (degZ d a) k g, single_mem_grade a hg⟩

theorem sec_mk_congr_num {I : Finset (Fin (r + 1))} {a : Fin (r + 1) → ℕ} {ha : ∀ l ∉ I, a l = 0}
    {f f' : (Md ι hθ d).M} (hff' : f = f') (hf : f ∈ (Md ι hθ d).grade (∑ l, (a l : ℤ))) (hf' : f' ∈ (Md ι hθ d).grade (∑ l, (a l : ℤ))) :
    GradedModule.sec.mk (Md ι hθ d) I ⟨a, ha, f, hf⟩ = GradedModule.sec.mk (Md ι hθ d) I ⟨a, ha, f', hf'⟩ := by
  subst hff'; rfl

theorem mkSec_add (I : Finset (Fin (r + 1))) (a a' : Fin (r + 1) → ℕ) (ha : ∀ l ∉ I, a l = 0) (ha' : ∀ l ∉ I, a' l = 0)
    (g g' : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)) (hg : FramesCompat ι (G k) (degN d a) g)
    (hg' : FramesCompat ι (G k) (degN d a') g')
    (hgg' : FramesCompat ι (G k) (degN d (a + a')) (fun j => uprod ι j a' ⨳ g j + uprod ι j a ⨳ g' j)) :
    mkSec (hθ := hθ) (d := d) I a ha g hg + mkSec I a' ha' g' hg'
      = mkSec I (a + a') (GradedModule.Frac.supp_add I ha ha') (fun j => uprod ι j a' ⨳ g j + uprod ι j a ⨳ g' j) hgg' := by
  show GradedModule.sec.mk (Md ι hθ d) I ⟨a + a', _, GradedModule.monMul (Md ι hθ d) a' (FamilyFrames.single ι G (degZ d a) k g)
      + GradedModule.monMul (Md ι hθ d) a (FamilyFrames.single ι G (degZ d a') k g'), _⟩ = _
  refine sec_mk_congr_num ?_ _ _
  rw [monMul_single, monMul_single,
    single_congr (e' := degZ d (a + a')) (by simp only [degZ, sum_cast_add]; ring) rfl,
    single_congr (e := degZ d a' + _) (e' := degZ d (a + a')) (by simp only [degZ, sum_cast_add]; ring) rfl]
  exact (single_add' _ _ _).symm

end Family

section Beta

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
  {ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)} [IsAffineHom ι]
  {q : P ⟶ Spec (CommRingCat.of A)} {G : ℕ → OModulePresheaf q}
  {ny : ℕ} {θ : Fin ny → ∀ k : ℕ, AffHom (G k) (G (k + 1))} {hθ : YComm G θ} {d k : ℕ}

variable (hθ d k) in

def βraw {i : ℕ} (s : (𝔘 ι).Idx i) (x : GradedModule.Frac (Md ι hθ d) (I s)) : (G k).obj (W s) :=
  ((isUnit_uPow s x.denExp x.hden).unit⁻¹ : Γ(P, W s)ˣ) ⨳ (G k).res (W_le_ch s) (x.num (degZ d x.denExp) k (ch s))

theorem uPow_smul_βraw {i : ℕ} (s : (𝔘 ι).Idx i) (x : GradedModule.Frac (Md ι hθ d) (I s)) :
    uPow s x.denExp ⨳ βraw hθ d k s x = (G k).res (W_le_ch s) (x.num (degZ d x.denExp) k (ch s)) := by
  have h := isUnit_uPow s x.denExp x.hden
  calc uPow s x.denExp ⨳ βraw hθ d k s x
      = (h.unit : Γ(P, W s)) ⨳ ((h.unit⁻¹ : Γ(P, W s)ˣ) ⨳ (G k).res (W_le_ch s) (x.num (degZ d x.denExp) k (ch s))) := by
        rw [h.unit_spec]; rfl
    _ = _ := by rw [← Units.smul_def, smul_inv_smul]

theorem βraw_wellDefined {i : ℕ} (s : (𝔘 ι).Idx i) (x y : GradedModule.Frac (Md ι hθ d) (I s))
    (h : GradedModule.Frac.Rel (Md ι hθ d) (I s) x y) : βraw hθ d k s x = βraw hθ d k s y := by
  obtain ⟨cc, hcc, heq⟩ := h
  have hU : IsUnit (uPow s (cc + y.denExp) * uPow s x.denExp) :=
    (isUnit_uPow s _ (GradedModule.Frac.supp_add _ hcc y.hden)).mul (isUnit_uPow s _ x.hden)
  refine (hU.smul_left_cancel).mp ?_
  have key := congrArg ((G k).res (W_le_ch s)) (rel_apply heq k (ch s))
  rw [res_smul', res_smul', ← uPow_eq, ← uPow_eq] at key
  rw [mul_smul, uPow_smul_βraw, key, show uPow s (cc + y.denExp) * uPow s x.denExp = uPow s (cc + x.denExp) * uPow s y.denExp by
    rw [uPow_add, uPow_add]; ring, mul_smul, uPow_smul_βraw]

theorem uPow_smul_βraw_mk {i : ℕ} (s : (𝔘 ι).Idx i) (a : Fin (r + 1) → ℕ) (ha : ∀ l ∉ I s, a l = 0)
    (f : (Md ι hθ d).M) (hf : f ∈ (Md ι hθ d).grade (∑ l, (a l : ℤ))) :
    uPow s a ⨳ βraw hθ d k s ⟨a, ha, f, hf⟩ = (G k).res (W_le_ch s) (f (degZ d a) k (ch s)) :=
  uPow_smul_βraw s ⟨a, ha, f, hf⟩

theorem βraw_add {i : ℕ} (s : (𝔘 ι).Idx i) (x y : GradedModule.Frac (Md ι hθ d) (I s)) :
    βraw hθ d k s ⟨x.denExp + y.denExp, GradedModule.Frac.supp_add _ x.hden y.hden,
        GradedModule.monMul (Md ι hθ d) y.denExp x.num + GradedModule.monMul (Md ι hθ d) x.denExp y.num, by
          have hx := GradedModule.monMul_mem_grade (Md ι hθ d) y.denExp _ x.num x.hnum
          have hy := GradedModule.monMul_mem_grade (Md ι hθ d) x.denExp _ y.num y.hnum
          refine Submodule.add_mem _ ?_ ?_
          · convert hx using 2
            simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]
          · convert hy using 2
            simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]; ring⟩
      = βraw hθ d k s x + βraw hθ d k s y := by
  obtain ⟨a, ha, f, hf⟩ := x
  obtain ⟨b, hb, g, hg⟩ := y
  refine ((isUnit_uPow s (a + b) (GradedModule.Frac.supp_add _ ha hb)).smul_left_cancel).mp ?_
  rw [uPow_smul_βraw_mk, smul_add]
  dsimp only
  rw [show (GradedModule.monMul (Md ι hθ d) b f + GradedModule.monMul (Md ι hθ d) a g) (degZ d (a + b)) k (ch s)
      = GradedModule.monMul (Md ι hθ d) b f (degZ d (a + b)) k (ch s) + GradedModule.monMul (Md ι hθ d) a g (degZ d (a + b)) k (ch s)
      from rfl, map_add]
  have ex : degZ d (a + b) = degZ d a + ∑ l, (b l : ℤ) := by
    simp only [degZ, sum_cast_add]; ring
  have ey : degZ d (a + b) = degZ d b + ∑ l, (a l : ℤ) := by
    simp only [degZ, sum_cast_add]; ring
  have h1 : GradedModule.monMul (Md ι hθ d) b f (degZ d (a + b)) k (ch s) = uprod ι (ch s) b ⨳ f (degZ d a) k (ch s) := by
    rw [ex, monMul_apply_top]
  have h2 : GradedModule.monMul (Md ι hθ d) a g (degZ d (a + b)) k (ch s) = uprod ι (ch s) a ⨳ g (degZ d b) k (ch s) := by
    rw [ey, monMul_apply_top]
  rw [h1, h2, res_smul', res_smul', ← uPow_eq, ← uPow_eq, ← uPow_smul_βraw_mk s a ha f hf, ← uPow_smul_βraw_mk s b hb g hg,
    smul_smul, smul_smul, ← uPow_add, ← uPow_add, add_comm b]

variable (hθ d k) in

def β {i : ℕ} (s : (𝔘 ι).Idx i) : GradedModule.sec (Md ι hθ d) (I s) →+ (G k).obj (W s) :=
  AddMonoidHom.mk' (Quotient.lift (βraw hθ d k s) (βraw_wellDefined s)) (by
    rintro ⟨x⟩ ⟨y⟩
    exact βraw_add s x y)

theorem β_mk {i : ℕ} (s : (𝔘 ι).Idx i) (x : GradedModule.Frac (Md ι hθ d) (I s)) :
    β hθ d k s (GradedModule.sec.mk _ _ x) = βraw hθ d k s x := rfl

theorem uPow_smul_β_mk {i : ℕ} (s : (𝔘 ι).Idx i) (a : Fin (r + 1) → ℕ) (ha : ∀ l ∉ I s, a l = 0)
    (f : (Md ι hθ d).M) (hf : f ∈ (Md ι hθ d).grade (∑ l, (a l : ℤ))) :
    uPow s a ⨳ β hθ d k s (GradedModule.sec.mk _ _ ⟨a, ha, f, hf⟩) = (G k).res (W_le_ch s) (f (degZ d a) k (ch s)) :=
  uPow_smul_βraw s ⟨a, ha, f, hf⟩

theorem c_face {i : ℕ} (s : (𝔘 ι).Idx (i + 1)) (t : Fin (i + 2)) (v : Fin (i + 1)) :
    c ((𝔘 ι).face s t) v = c s (t.succAbove v) := rfl

theorem I_face_subset {i : ℕ} (s : (𝔘 ι).Idx (i + 1)) (t : Fin (i + 2)) : I ((𝔘 ι).face s t) ⊆ I s :=
  ProjSpaceCech.Idx.img_face_subset r (toIdx s) t

theorem ch_face_mem {i : ℕ} (s : (𝔘 ι).Idx (i + 1)) (t : Fin (i + 2)) : ch ((𝔘 ι).face s t) ∈ I s :=
  I_face_subset s t (ch_mem_I _)

theorem uW_face {i : ℕ} (s : (𝔘 ι).Idx (i + 1)) (t : Fin (i + 2)) (l : Fin (r + 1)) :
    uW s l = uW s (ch ((𝔘 ι).face s t)) * restrictFun (W_face_le s t) (uW ((𝔘 ι).face s t) l) := by
  have hW : W s ≤ pullbackOverlap ι (ch s) (ch ((𝔘 ι).face s t)) := W_le_overlap s (ch_face_mem s t)
  have key := congrArg (restrictFun hW) (frameUnit_cocycle ι (ch s) (ch ((𝔘 ι).face s t)) l)
  rw [map_mul, restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_restrictFun] at key
  rw [uW, uW, uW, restrictFun_restrictFun, ← key]

theorem uPow_face {i : ℕ} (s : (𝔘 ι).Idx (i + 1)) (t : Fin (i + 2)) (a : Fin (r + 1) → ℕ) :
    uPow s a = uW s (ch ((𝔘 ι).face s t)) ^ (∑ l, a l) * restrictFun (W_face_le s t) (uPow ((𝔘 ι).face s t) a) := by
  simp only [uPow, map_prod, map_pow]
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun l _ => by rw [← mul_pow, ← uW_face]

theorem res_num_face {i : ℕ} (s : (𝔘 ι).Idx (i + 1)) (t : Fin (i + 2)) {n : ℕ}
    {f : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)} (hf : FramesCompat ι (G k) n f) :
    (G k).res (W_le_ch s) (f (ch s))
      = uW s (ch ((𝔘 ι).face s t)) ^ n ⨳ (G k).res (W_le_of_mem s (ch_face_mem s t)) (f (ch ((𝔘 ι).face s t))) := by
  have hW : W s ≤ pullbackOverlap ι (ch s) (ch ((𝔘 ι).face s t)) := W_le_overlap s (ch_face_mem s t)
  have key := congrArg ((G k).res hW) (hf (ch s) (ch ((𝔘 ι).face s t)))
  rw [(G k).res_res, res_smul', (G k).res_res, map_pow, restrictFun_restrictFun] at key
  exact key

theorem β_face {i : ℕ} (s : (𝔘 ι).Idx (i + 1)) (t : Fin (i + 2)) (w : GradedModule.sec (Md ι hθ d) (I ((𝔘 ι).face s t))) :
    β hθ d k s (GradedModule.secIncl (Md ι hθ d) (I_face_subset s t) w)
      = uW s (ch ((𝔘 ι).face s t)) ^ d ⨳ (G k).res (W_face_le s t) (β hθ d k ((𝔘 ι).face s t) w) := by
  induction w using Quotient.inductionOn with
  | h x =>
    obtain ⟨a, ha, f, hf⟩ := x
    change β hθ d k s (GradedModule.sec.mk _ _ ⟨a, _, f, hf⟩) = _ ⨳ (G k).res _ (β hθ d k _ (GradedModule.sec.mk _ _ ⟨a, ha, f, hf⟩))
    refine ((isUnit_uPow s a fun l hl => ha l fun h => hl (I_face_subset s t h)).smul_left_cancel).mp ?_
    rw [uPow_smul_β_mk]
    have hfc := framesCompat_num (⟨a, ha, f, hf⟩ : GradedModule.Frac (Md ι hθ d) _) k
    dsimp only at hfc ⊢
    rw [res_num_face s t hfc, smul_smul, uPow_face s t, mul_right_comm, mul_smul, ← res_smul', uPow_smul_β_mk, (G k).res_res,
      degN, pow_add]

end Beta

section Alpha

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
  {ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)} [IsAffineHom ι]
  {q : P ⟶ Spec (CommRingCat.of A)} {G : ℕ → OModulePresheaf q}
  {ny : ℕ} {θ : Fin ny → ∀ k : ℕ, AffHom (G k) (G (k + 1))} {hθ : YComm G θ} {d k : ℕ}

theorem UW_le_U {i : ℕ} (s : (𝔘 ι).Idx i) (j : Fin (r + 1)) : pullbackChart ι j ⊓ W s ≤ pullbackChart ι j := inf_le_left
theorem UW_le_W {i : ℕ} (s : (𝔘 ι).Idx i) (j : Fin (r + 1)) : pullbackChart ι j ⊓ W s ≤ W s := inf_le_right

variable (d k) in

def Rep {i : ℕ} (s : (𝔘 ι).Idx i) (t : (G k).obj (W s)) (a : Fin (r + 1) → ℕ)
    (g : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)) : Prop :=
  ∀ j : Fin (r + 1), (G k).res (UW_le_U s j) (g j)
    = restrictFun (UW_le_U s j) (uprod ι j a * frameUnit ι j (ch s) ^ d) ⨳ (G k).res (UW_le_W s j) t

theorem Rep.add {i : ℕ} {s : (𝔘 ι).Idx i} {t t' : (G k).obj (W s)} {a a' : Fin (r + 1) → ℕ}
    {g g' : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)} (h : Rep d k s t a g) (h' : Rep d k s t' a' g') :
    Rep d k s (t + t') (a + a') (fun j => uprod ι j a' ⨳ g j + uprod ι j a ⨳ g' j) := by
  intro j
  rw [map_add, res_smul', res_smul', h j, h' j, smul_smul, smul_smul, map_add, smul_add, ← map_mul, ← map_mul, uprod_add]
  congr 3 <;> ring

theorem exists_rep (hq : (G k).IsQuasicoherent) {i : ℕ} (s : (𝔘 ι).Idx i) (t : (G k).obj (W s)) :
    ∃ (n : ℕ) (g : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)),
      FramesCompat ι (G k) (degN d (aN s n)) g ∧ Rep d k s t (aN s n) g := by
  obtain ⟨n, g, hg, hres⟩ := exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent ι (G k) hq (c s) d t
  refine ⟨n, g, ?_, fun j => ?_⟩
  · rw [degN, sum_aN, add_comm]; exact hg
  · rw [hres j, uprod_aN, map_mul, map_pow, map_pow, map_prod]; rfl

theorem exists_torsion (hq : (G k).IsQuasicoherent) {i : ℕ} (s : (𝔘 ι).Idx i) (j : Fin (r + 1))
    (y : (G k).obj (pullbackChart ι j)) (hy : (G k).res (UW_le_U s j) y = 0) :
    ∃ e : ℕ, (∏ v, frameUnit ι j (c s v)) ^ e ⨳ y = 0 := by
  have e := basicOpen_prod_frameUnit_univ ι j (c s)
  refine (hq ⟨pullbackChart ι j, isAffineOpen_pullbackChart ι j⟩ (∏ v, frameUnit ι j (c s v))).2 y ?_
  have : (G k).res (P.basicOpen_le _) y = (G k).res e.le ((G k).res (UW_le_U s j) y) := by rw [(G k).res_res]
  rw [this, hy, map_zero]

theorem rep_unique (hq : (G k).IsQuasicoherent) {i : ℕ} (s : (𝔘 ι).Idx i) (t : (G k).obj (W s))
    {a a' : Fin (r + 1) → ℕ} (ha : ∀ l ∉ I s, a l = 0) (ha' : ∀ l ∉ I s, a' l = 0)
    {g g' : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)}
    (hg : FramesCompat ι (G k) (degN d a) g) (hg' : FramesCompat ι (G k) (degN d a') g')
    (h : Rep d k s t a g) (h' : Rep d k s t a' g') :
    mkSec (hθ := hθ) (d := d) (I s) a ha g hg = mkSec (I s) a' ha' g' hg' := by

  have hδ : ∀ j, (G k).res (UW_le_U s j) (uprod ι j a' ⨳ g j - uprod ι j a ⨳ g' j) = 0 := fun j => by
    rw [map_sub, res_smul', res_smul', h j, h' j, smul_smul, smul_smul, ← map_mul, ← map_mul, ← sub_smul, ← map_sub,
      show uprod ι j a' * (uprod ι j a * frameUnit ι j (ch s) ^ d) - uprod ι j a * (uprod ι j a' * frameUnit ι j (ch s) ^ d) = 0
        by ring, map_zero, zero_smul]
  choose e0 he0 using fun j => exists_torsion hq s j _ (hδ j)
  obtain ⟨n, hle⟩ : ∃ n : ℕ, ∀ j, e0 j ≤ n := ⟨Finset.univ.sup e0, fun j => Finset.le_sup (f := e0) (Finset.mem_univ j)⟩
  have hn : ∀ j, (∏ v, frameUnit ι j (c s v)) ^ n ⨳ (uprod ι j a' ⨳ g j - uprod ι j a ⨳ g' j) = 0 := fun j => by
    rw [← Nat.sub_add_cancel (hle j), pow_add, mul_smul, he0 j, smul_zero]
  refine (GradedModule.sec_mk_eq _ _).mpr ⟨aN s n, aN_supp s n, ?_⟩
  show GradedModule.monMul (Md ι hθ d) (aN s n + a') (FamilyFrames.single ι G (degZ d a) k g)
    = GradedModule.monMul (Md ι hθ d) (aN s n + a) (FamilyFrames.single ι G (degZ d a') k g')
  rw [monMul_single, monMul_single]
  refine single_congr (by simp only [degZ, sum_cast_add]; ring) (funext fun j => ?_)
  have hj := hn j
  rw [smul_sub, sub_eq_zero, ← uprod_aN, smul_smul, smul_smul, ← uprod_add, ← uprod_add] at hj
  exact hj

variable (hθ d) in

def αfun (hq : (G k).IsQuasicoherent) {i : ℕ} (s : (𝔘 ι).Idx i) (t : (G k).obj (W s)) : GradedModule.sec (Md ι hθ d) (I s) :=
  mkSec (I s) (aN s (exists_rep (d := d) hq s t).choose) (aN_supp s _) (exists_rep (d := d) hq s t).choose_spec.choose
    (exists_rep (d := d) hq s t).choose_spec.choose_spec.1

theorem αfun_eq (hq : (G k).IsQuasicoherent) {i : ℕ} (s : (𝔘 ι).Idx i) (t : (G k).obj (W s))
    {a : Fin (r + 1) → ℕ} (ha : ∀ l ∉ I s, a l = 0) {g : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)}
    (hg : FramesCompat ι (G k) (degN d a) g) (h : Rep d k s t a g) :
    αfun hθ d hq s t = mkSec (I s) a ha g hg :=
  rep_unique hq s t _ ha _ hg (exists_rep (d := d) hq s t).choose_spec.choose_spec.2 h

theorem αfun_add (hq : (G k).IsQuasicoherent) {i : ℕ} (s : (𝔘 ι).Idx i) (t t' : (G k).obj (W s)) :
    αfun hθ d hq s (t + t') = αfun hθ d hq s t + αfun hθ d hq s t' := by
  obtain ⟨n, g, hg, h⟩ := exists_rep (d := d) hq s t
  obtain ⟨n', g', hg', h'⟩ := exists_rep (d := d) hq s t'
  have hgg' : FramesCompat ι (G k) (degN d (aN s n + aN s n')) (fun j => uprod ι j (aN s n') ⨳ g j + uprod ι j (aN s n) ⨳ g' j) := by
    have h1 := framesCompat_uprod_smul hg (aN s n')
    have h2 := framesCompat_uprod_smul hg' (aN s n)
    rw [← degN_add] at h1
    rw [← degN_add, add_comm (aN s n')] at h2
    exact h1.add h2
  rw [αfun_eq hq s t (aN_supp s n) hg h, αfun_eq hq s t' (aN_supp s n') hg' h',
    αfun_eq hq s (t + t') (GradedModule.Frac.supp_add _ (aN_supp s n) (aN_supp s n')) hgg' (h.add h'), mkSec_add]

variable (hθ d k) in

def α (hq : (G k).IsQuasicoherent) {i : ℕ} (s : (𝔘 ι).Idx i) : (G k).obj (W s) →+ GradedModule.sec (Md ι hθ d) (I s) :=
  AddMonoidHom.mk' (αfun hθ d hq s) (αfun_add hq s)

theorem α_apply (hq : (G k).IsQuasicoherent) {i : ℕ} (s : (𝔘 ι).Idx i) (t : (G k).obj (W s)) :
    α hθ d k hq s t = αfun hθ d hq s t := rfl

theorem res_UW_of_rep {i : ℕ} {s : (𝔘 ι).Idx i} {t : (G k).obj (W s)} {a : Fin (r + 1) → ℕ}
    {g : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)} (h : Rep d k s t a g) :
    (G k).res (W_le_ch s) (g (ch s)) = uPow s a ⨳ t := by
  have e1 : (G k).res (W_le_ch s) (g (ch s)) = (G k).res (le_inf (W_le_ch s) le_rfl) ((G k).res (UW_le_U s (ch s)) (g (ch s))) := by
    rw [(G k).res_res]
  rw [e1, h (ch s), res_smul', restrictFun_restrictFun, res_res_eq_self, frameUnit_self, one_pow, mul_one, uPow_eq]

theorem β_α (hq : (G k).IsQuasicoherent) {i : ℕ} (s : (𝔘 ι).Idx i) (t : (G k).obj (W s)) :
    β hθ d k s (α hθ d k hq s t) = t := by
  obtain ⟨n, g, hg, h⟩ := exists_rep (d := d) hq s t
  rw [α_apply, αfun_eq hq s t (aN_supp s n) hg h]
  refine ((isUnit_uPow s (aN s n) (aN_supp s n)).smul_left_cancel).mp ?_
  rw [mkSec, uPow_smul_β_mk, FamilyFrames.single_apply_self, res_UW_of_rep h]

theorem Rep.face {i : ℕ} {s : (𝔘 ι).Idx (i + 1)} {t : Fin (i + 2)} {z : (G k).obj (W ((𝔘 ι).face s t))}
    {a : Fin (r + 1) → ℕ} {g : ∀ j : Fin (r + 1), (G k).obj (pullbackChart ι j)} (h : Rep d k ((𝔘 ι).face s t) z a g) :
    Rep d k s (uW s (ch ((𝔘 ι).face s t)) ^ d ⨳ (G k).res (W_face_le s t) z) a g := by
  intro j
  have hUW : pullbackChart ι j ⊓ W s ≤ pullbackChart ι j ⊓ W ((𝔘 ι).face s t) := inf_le_inf_left _ (W_face_le s t)
  have e1 : (G k).res (UW_le_U s j) (g j) = (G k).res hUW ((G k).res (UW_le_U ((𝔘 ι).face s t) j) (g j)) := by
    rw [(G k).res_res]
  rw [e1, h j, res_smul', (G k).res_res, restrictFun_restrictFun, res_smul', (G k).res_res, map_pow, smul_smul]
  congr 1

  have hO : pullbackChart ι j ⊓ W s ≤ pullbackOverlap ι j (ch s) := by
    rw [pullbackOverlap_eq_inf]; exact inf_le_inf_left _ (W_le_ch s)
  have key := congrArg (restrictFun hO) (frameUnit_cocycle ι j (ch s) (ch ((𝔘 ι).face s t)))
  rw [map_mul, restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_restrictFun] at key
  rw [map_mul, map_mul, map_pow, map_pow, uW, restrictFun_restrictFun, ← key]
  ring

theorem α_face (hq : (G k).IsQuasicoherent) {i : ℕ} (s : (𝔘 ι).Idx (i + 1)) (t : Fin (i + 2))
    (z : (G k).obj (W ((𝔘 ι).face s t))) :
    GradedModule.secIncl (Md ι hθ d) (I_face_subset s t) (α hθ d k hq ((𝔘 ι).face s t) z)
      = α hθ d k hq s (uW s (ch ((𝔘 ι).face s t)) ^ d ⨳ (G k).res (W_face_le s t) z) := by
  obtain ⟨n, g, hg, h⟩ := exists_rep (d := d) hq ((𝔘 ι).face s t) z
  rw [α_apply, α_apply, αfun_eq hq _ z (aN_supp _ n) hg h,
    αfun_eq hq s _ (fun l hl => aN_supp _ n l fun h' => hl (I_face_subset s t h')) hg h.face]
  rfl

end Alpha

section Untwist

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
  {ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)}
  (q : P ⟶ Spec (CommRingCat.of A)) (d : ℕ)

theorem restrictFun_injective_of_ge {W W' : P.Opens} (h : W ≤ W') (h' : W' ≤ W) : Function.Injective (restrictFun h) := by
  intro a b hab
  have := congrArg (restrictFun h') hab
  rwa [restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_refl, restrictFun_refl] at this

def evT (j : Fin (r + 1)) (W : P.Opens) (hW : W ≤ pullbackChart ι j) : (twist q ι d).obj W ≃ₗ[Γ(P, W)] Γ(P, W) :=
  Classical.choose (exists_linearEquiv_twistObj_of_le_pullbackChart q ι d hW)

theorem restrictFun_evT (j : Fin (r + 1)) (W : P.Opens) (hW : W ≤ pullbackChart ι j) (g : (twist q ι d).obj W) :
    restrictFun (inf_le_left : W ⊓ pullbackChart ι j ≤ W) (evT q d j W hW g) = g.val j :=
  (Classical.choose_spec (exists_linearEquiv_twistObj_of_le_pullbackChart q ι d hW)).1 g

theorem evT_res (j : Fin (r + 1)) {W W' : P.Opens} (h : W' ≤ W) (hW : W ≤ pullbackChart ι j) (g : (twist q ι d).obj W) :
    restrictFun h (evT q d j W hW g) = evT q d j W' (h.trans hW) ((twist q ι d).res h g) := by
  refine restrictFun_injective_of_ge (inf_le_left : W' ⊓ pullbackChart ι j ≤ W') (le_inf le_rfl (h.trans hW)) ?_
  rw [restrictFun_evT, twist_res_val, ← restrictFun_evT q d j W hW g, restrictFun_restrictFun, restrictFun_restrictFun]

theorem evT_change (j j' : Fin (r + 1)) (W : P.Opens) (hWj : W ≤ pullbackChart ι j) (hWj' : W ≤ pullbackChart ι j')
    (g : (twist q ι d).obj W) :
    evT q d j W hWj g = restrictFun hWj (frameUnit ι j j') ^ d * evT q d j' W hWj' g := by
  refine restrictFun_injective_of_ge
    (inf_le_left.trans inf_le_left : (W ⊓ pullbackChart ι j) ⊓ pullbackChart ι j' ≤ W) (le_inf (le_inf le_rfl hWj) hWj') ?_
  have eL : restrictFun (inf_le_left.trans inf_le_left : (W ⊓ pullbackChart ι j) ⊓ pullbackChart ι j' ≤ W) (evT q d j W hWj g)
      = restrictFun inf_le_left (g.val j) := by
    rw [← restrictFun_evT q d j W hWj g, restrictFun_restrictFun]
  have eR : restrictFun (inf_le_left.trans inf_le_left : (W ⊓ pullbackChart ι j) ⊓ pullbackChart ι j' ≤ W) (evT q d j' W hWj' g)
      = restrictFun (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          (W ⊓ pullbackChart ι j) ⊓ pullbackChart ι j' ≤ W ⊓ pullbackChart ι j') (g.val j') := by
    rw [← restrictFun_evT q d j' W hWj' g, restrictFun_restrictFun]
  rw [map_mul, map_pow, eL, eR, restrictFun_restrictFun, g.compat j j']

variable (F : OModulePresheaf q)

def E (j : Fin (r + 1)) (W : P.Opens) (hW : W ≤ pullbackChart ι j) :
    F.obj W ⊗[Γ(P, W)] (twist q ι d).obj W ≃ₗ[Γ(P, W)] F.obj W :=
  (TensorProduct.congr (LinearEquiv.refl Γ(P, W) (F.obj W)) (evT q d j W hW)).trans (TensorProduct.rid Γ(P, W) (F.obj W))

theorem E_tmul (j : Fin (r + 1)) (W : P.Opens) (hW : W ≤ pullbackChart ι j) (x : F.obj W) (g : (twist q ι d).obj W) :
    E q d F j W hW (x ⊗ₜ g) = evT q d j W hW g ⨳ x := by
  simp only [E, LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.rid_tmul]

theorem E_res (j j' : Fin (r + 1)) {W W' : P.Opens} (h : W' ≤ W) (hWj : W ≤ pullbackChart ι j)
    (hW'j' : W' ≤ pullbackChart ι j') (y : F.obj W ⊗[Γ(P, W)] (twist q ι d).obj W) :
    E q d F j' W' hW'j' ((F.tensor (twist q ι d)).res h y)
      = restrictFun hW'j' (frameUnit ι j' j) ^ d ⨳ F.res h (E q d F j W hWj y) := by
  change E q d F j' W' hW'j' (F.tensorResₛₗ (twist q ι d) h y) = _
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul x g =>
    rw [tensorResₛₗ_tmul, E_tmul, E_tmul, res_smul', evT_change q d j' j W' hW'j' (h.trans hWj), ← evT_res, mul_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]

end Untwist

section Chain

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
  {ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)} [IsAffineHom ι]
  {q : P ⟶ Spec (CommRingCat.of A)} {G : ℕ → OModulePresheaf q}
  {ny : ℕ} {θ : Fin ny → ∀ k : ℕ, AffHom (G k) (G (k + 1))} {hθ : YComm G θ} {d k : ℕ}

theorem neg_one_pow_smul {R : Type u} [Ring R] {V : Type u} [AddCommGroup V] [Module R V] (t : ℕ) (m : V) :
    (-1 : R) ^ t ⨳ m = (-1 : ℤ) ^ t ⨳ m := by
  rw [← Int.cast_smul_eq_zsmul R, Int.cast_pow, Int.cast_neg, Int.cast_one]

variable (ι G d k) in

abbrev GT : OModulePresheaf q := (G k).tensor (twist q ι d)

variable (hθ d k) in

def AE (hq : (G k).IsQuasicoherent) {i : ℕ} (s : (𝔘 ι).Idx i) (y : (GT ι G d k).obj (W s)) :
    GradedModule.sec (Md ι hθ d) (I s) :=
  α hθ d k hq s (E q d (G k) (ch s) (W s) (W_le_ch s) y)

variable (hθ d k) in

def BE {i : ℕ} (s : (𝔘 ι).Idx i) (w : GradedModule.sec (Md ι hθ d) (I s)) : (GT ι G d k).obj (W s) :=
  (E q d (G k) (ch s) (W s) (W_le_ch s)).symm (β hθ d k s w)

theorem BE_AE (hq : (G k).IsQuasicoherent) {i : ℕ} (s : (𝔘 ι).Idx i) (y : (GT ι G d k).obj (W s)) :
    BE hθ d k s (AE hθ d k hq s y) = y := by
  rw [BE, AE, β_α, LinearEquiv.symm_apply_apply]

theorem AE_add (hq : (G k).IsQuasicoherent) {i : ℕ} (s : (𝔘 ι).Idx i) (y y' : (GT ι G d k).obj (W s)) :
    AE hθ d k hq s (y + y') = AE hθ d k hq s y + AE hθ d k hq s y' :=
  (congrArg (α hθ d k hq s) (map_add (E q d (G k) (ch s) (W s) (W_le_ch s)) y y')).trans (map_add _ _ _)

theorem AE_zsmul (hq : (G k).IsQuasicoherent) {i : ℕ} (s : (𝔘 ι).Idx i) (n : ℤ) (y : (GT ι G d k).obj (W s)) :
    AE hθ d k hq s (n ⨳ y) = n ⨳ AE hθ d k hq s y :=
  (congrArg (α hθ d k hq s) (map_zsmul (E q d (G k) (ch s) (W s) (W_le_ch s)) n y)).trans (map_zsmul _ _ _)

theorem BE_add {i : ℕ} (s : (𝔘 ι).Idx i) (w w' : GradedModule.sec (Md ι hθ d) (I s)) :
    BE hθ d k s (w + w') = BE hθ d k s w + BE hθ d k s w' :=
  (congrArg (E q d (G k) (ch s) (W s) (W_le_ch s)).symm (map_add (β hθ d k s) w w')).trans (map_add _ _ _)

theorem BE_zsmul {i : ℕ} (s : (𝔘 ι).Idx i) (n : ℤ) (w : GradedModule.sec (Md ι hθ d) (I s)) :
    BE hθ d k s (n ⨳ w) = n ⨳ BE hθ d k s w :=
  (congrArg (E q d (G k) (ch s) (W s) (W_le_ch s)).symm (map_zsmul (β hθ d k s) n w)).trans (map_zsmul _ _ _)

theorem AE_face (hq : (G k).IsQuasicoherent) {i : ℕ} (s : (𝔘 ι).Idx (i + 1)) (t : Fin (i + 2))
    (y : (GT ι G d k).obj (W ((𝔘 ι).face s t))) :
    AE hθ d k hq s ((GT ι G d k).res (W_face_le s t) y)
      = GradedModule.secIncl (Md ι hθ d) (I_face_subset s t) (AE hθ d k hq ((𝔘 ι).face s t) y) := by
  rw [AE, AE, E_res q d (G k) (ch ((𝔘 ι).face s t)) (ch s) (W_face_le s t) (W_le_ch _) (W_le_ch s), α_face]
  rfl

theorem BE_face {i : ℕ} (s : (𝔘 ι).Idx (i + 1)) (t : Fin (i + 2)) (w : GradedModule.sec (Md ι hθ d) (I ((𝔘 ι).face s t))) :
    (GT ι G d k).res (W_face_le s t) (BE hθ d k ((𝔘 ι).face s t) w)
      = BE hθ d k s (GradedModule.secIncl (Md ι hθ d) (I_face_subset s t) w) := by
  rw [BE, BE, β_face]
  apply (E q d (G k) (ch s) (W s) (W_le_ch s)).injective
  rw [LinearEquiv.apply_symm_apply, E_res q d (G k) (ch ((𝔘 ι).face s t)) (ch s) (W_face_le s t) (W_le_ch _) (W_le_ch s),
    LinearEquiv.apply_symm_apply]
  rfl

variable (hθ d k) in

def Aco (hq : (G k).IsQuasicoherent) (i : ℕ) (x : (GT ι G d k).cochain (𝔘 ι) i) :
    GradedModule.cochain (Md ι hθ d) i :=
  fun σ => AE hθ d k hq (ofIdx σ) (x (ofIdx σ))

variable (hθ d k) in

def Bco (i : ℕ) (y : GradedModule.cochain (Md ι hθ d) i) : (GT ι G d k).cochain (𝔘 ι) i :=
  fun s => BE hθ d k s (y (toIdx s))

theorem Bco_Aco (hq : (G k).IsQuasicoherent) (i : ℕ) (x : (GT ι G d k).cochain (𝔘 ι) i) :
    Bco hθ d k i (Aco hθ d k hq i x) = x := by
  funext s
  exact BE_AE hq s (x s)

theorem Aco_zero (hq : (G k).IsQuasicoherent) (i : ℕ) : Aco hθ d k hq i (0 : (GT ι G d k).cochain (𝔘 ι) i) = 0 := by
  funext σ
  exact (congrArg (α hθ d k hq (ofIdx σ)) (map_zero (E q d (G k) (ch (ofIdx σ)) (W (ofIdx σ)) (W_le_ch _)))).trans
    (map_zero _)

variable (hθ d k) in

def AEh (hq : (G k).IsQuasicoherent) {i : ℕ} (s : (𝔘 ι).Idx i) :
    (GT ι G d k).obj ((𝔘 ι).inter s) →+ GradedModule.sec (Md ι hθ d) (I s) :=
  AddMonoidHom.mk' (AE hθ d k hq s) (AE_add hq s)

variable (hθ d k) in

def BEh {i : ℕ} (s : (𝔘 ι).Idx i) : GradedModule.sec (Md ι hθ d) (I s) →+ (GT ι G d k).obj ((𝔘 ι).inter s) :=
  AddMonoidHom.mk' (BE hθ d k s) (BE_add s)

theorem d_Aco (hq : (G k).IsQuasicoherent) (i : ℕ) (x : (GT ι G d k).cochain (𝔘 ι) i) :
    GradedModule.d (Md ι hθ d) i (Aco hθ d k hq i x) = Aco hθ d k hq (i + 1) ((GT ι G d k).d (𝔘 ι) i x) := by
  funext σ
  rw [GradedModule.d_apply]
  change _ = AEh hθ d k hq (ofIdx σ) ((GT ι G d k).d (𝔘 ι) i x (ofIdx σ))
  rw [OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_zsmul, neg_one_pow_smul (R := MvPolynomial (Fin ny) A)]
  exact congrArg _ (AE_face hq (ofIdx σ) t (x ((𝔘 ι).face (ofIdx σ) t))).symm

theorem d_Bco (i : ℕ) (y : GradedModule.cochain (Md ι hθ d) i) :
    (GT ι G d k).d (𝔘 ι) i (Bco hθ d k i y) = Bco hθ d k (i + 1) (GradedModule.d (Md ι hθ d) i y) := by
  funext s
  rw [OModulePresheaf.d_apply]
  change _ = BEh hθ d k s (GradedModule.d (Md ι hθ d) i y (toIdx s))
  rw [GradedModule.d_apply, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [neg_one_pow_smul (R := MvPolynomial (Fin ny) A), map_zsmul]
  exact congrArg _ (BE_face s t (y (toIdx ((𝔘 ι).face s t))))

theorem main (hq : (G k).IsQuasicoherent) (i : ℕ)
    (hv : Subsingleton (GradedModule.H (Md ι hθ d) (i + 1))) :
    Subsingleton ((GT ι G d k).HSucc (𝔘 ι) i) := by
  refine ⟨fun y y' => ?_⟩
  suffices hzero : ∀ z : (GT ι G d k).HSucc (𝔘 ι) i, z = 0 by rw [hzero y, hzero y']
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H x =>
    refine (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr ?_)
    have hξ : GradedModule.d (Md ι hθ d) (i + 1) (Aco hθ d k hq (i + 1) x.1) = 0 := by
      rw [d_Aco, LinearMap.mem_ker.mp x.2, Aco_zero]
    have hmk : (Submodule.Quotient.mk ⟨Aco hθ d k hq (i + 1) x.1, LinearMap.mem_ker.mpr hξ⟩ :
        GradedModule.H (Md ι hθ d) (i + 1)) = 0 :=
      @Subsingleton.elim _ hv _ _
    obtain ⟨b, hb⟩ := Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero _).mp hmk)
    refine ⟨Bco hθ d k i b, ?_⟩
    show (GT ι G d k).d (𝔘 ι) i (Bco hθ d k i b) = x.1
    rw [d_Bco, show GradedModule.d (Md ι hθ d) i b = Aco hθ d k hq (i + 1) x.1 from hb, Bco_Aco]

end Chain

end P2mGrRetract

end

theorem solution
    {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
    (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) [IsAffineHom ι]
    {q : P ⟶ Spec (CommRingCat.of A)}
    (G : ℕ → OModulePresheaf q) (hq : ∀ k, (G k).IsQuasicoherent)
    {s : ℕ} (θ : Fin s → ∀ k : ℕ, OModulePresheaf.AffHom (G k) (G (k + 1))) (hθ : OModulePresheaf.YComm G θ)
    (d k i : ℕ)
    (hv : Subsingleton (ProjSpaceCech.GradedModule.H
      (ProjSpaceCech.GradedModule.shift (OModulePresheaf.familyFramesGradedModule ι G θ hθ) (d : ℤ)) (i + 1))) :
    Subsingleton (((G k).tensor (ProjSpace.twist q ι d)).HSucc (ProjSpace.stdCoverPullback ι) i) :=
  P2mGrRetract.main (hθ := hθ) (hq k) i hv

end S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule (solution)
