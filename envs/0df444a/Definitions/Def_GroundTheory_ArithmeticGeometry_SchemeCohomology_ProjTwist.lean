-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwist
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwist
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:50.764794+00:00
-- url     : https://prove2.me/theorems/b7e4cba7-edb7-4809-9cea-ddbe44185bf6
-- title:
--   Proj Twist
-- statement:
--   Definitions and structural lemmas for Proj Twist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwist.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
namespace ProjTwist
abbrev Loc (x : ProjectiveSpectrum 𝒜) : Type u :=
  Localization x.asHomogeneousIdeal.toIdeal.primeCompl
variable {𝒜}
def IsFraction (k : ℤ) {U : Opens (ProjectiveSpectrum.top 𝒜)} (f : ∀ x : U, Loc 𝒜 x.1) : Prop :=
  ∃ (i j : ℕ) (_ : (j : ℤ) = i + k) (r s : A) (_ : r ∈ 𝒜 j) (_ : s ∈ 𝒜 i)
    (s_nin : ∀ x : U, s ∉ x.1.asHomogeneousIdeal), ∀ x : U, f x = Localization.mk r ⟨s, s_nin x⟩
variable (𝒜) in

def isFractionPrelocal (k : ℤ) :
    PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => Loc 𝒜 x where
  pred f := IsFraction k f
  res := by
    rintro V U i f ⟨a, b, hab, r, s, hr, hs, h, w⟩
    exact ⟨a, b, hab, r, s, hr, hs, (h <| i ·), (w <| i ·)⟩
variable (𝒜) in

def isLocallyFraction (k : ℤ) : LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => Loc 𝒜 x :=
  (isFractionPrelocal 𝒜 k).sheafify
theorem exists_pos_deg_nmem (x : ProjectiveSpectrum 𝒜) :
    ∃ (f : A) (m : ℕ), f ∈ 𝒜 m ∧ 0 < m ∧ f ∉ x.asHomogeneousIdeal := by
  classical
  by_contra! h
  refine x.not_irrelevant_le fun z hz => ?_
  rw [← DirectSum.sum_support_decompose 𝒜 z]
  refine x.1.toIdeal.sum_mem fun n hn => ?_
  by_cases hn0 : n = 0
  · subst hn0
    have : (DirectSum.decompose 𝒜 z 0 : A) = 0 := by
      rw [← GradedRing.proj_apply]
      exact (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hz
    rw [this]
    exact zero_mem _
  · exact h _ n (SetLike.coe_mem _) (Nat.pos_of_ne_zero hn0)
theorem exists_den (k : ℤ) (x : ProjectiveSpectrum 𝒜) :
    ∃ (i j : ℕ) (s : A), (j : ℤ) = i + k ∧ s ∈ 𝒜 i ∧ s ∉ x.asHomogeneousIdeal := by
  obtain ⟨f, m, hf, hm, hfx⟩ := exists_pos_deg_nmem x
  refine ⟨m * (-k).toNat, m * (-k).toNat + k.toNat - (-k).toNat + 0, f ^ (-k).toNat, ?_,
    ?_, fun h => hfx (x.isPrime.mem_of_pow_mem _ h)⟩
  · have : ((-k).toNat : ℤ) ≤ m * (-k).toNat := by
      exact_mod_cast Nat.le_mul_of_pos_left _ hm
    push_cast
    omega
  · simpa [mul_comm] using SetLike.pow_mem_graded (-k).toNat hf
theorem nmem_mul {x : ProjectiveSpectrum 𝒜} {s s' : A} (h : s ∉ x.asHomogeneousIdeal)
    (h' : s' ∉ x.asHomogeneousIdeal) : s * s' ∉ x.asHomogeneousIdeal := fun hh =>
  (x.isPrime.mem_or_mem hh).elim h h'
theorem zero_mem' (k : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    (isLocallyFraction 𝒜 k).pred (0 : ∀ x : U, Loc 𝒜 x.1) := fun x => by
  obtain ⟨i, j, s, hij, hs, hsx⟩ := exists_den k x.1
  refine ⟨U ⊓ ProjectiveSpectrum.basicOpen 𝒜 s, ⟨x.2, hsx⟩, Opens.infLELeft _ _, i, j, hij, 0, s,
    zero_mem _, hs, fun y => y.2.2, fun y => ?_⟩
  simp [Localization.mk_zero]
theorem add_mem' (k : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) (a b : ∀ x : U, Loc 𝒜 x.1)
    (ha : (isLocallyFraction 𝒜 k).pred a) (hb : (isLocallyFraction 𝒜 k).pred b) :
    (isLocallyFraction 𝒜 k).pred (a + b) := fun x => by
  obtain ⟨Va, ma, ia, i, j, hij, r, s, hr, hs, hsn, wa⟩ := ha x
  obtain ⟨Vb, mb, ib, i', j', hij', r', s', hr', hs', hsn', wb⟩ := hb x
  have hdeg : j' + i = j + i' := by omega
  refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, i + i', j + i', by push_cast; omega,
    r * s' + s * r', s * s', add_mem (SetLike.mul_mem_graded hr hs') ?_,
    SetLike.mul_mem_graded hs hs', fun ⟨y, hya, hyb⟩ => ?_, fun ⟨y, hya, hyb⟩ => ?_⟩
  · have := SetLike.mul_mem_graded hs hr'
    rwa [add_comm i j', hdeg] at this
  · exact nmem_mul (hsn ⟨y, hya⟩) (hsn' ⟨y, hyb⟩)
  · have e1 : a (ia ⟨y, hya⟩) = _ := wa ⟨y, hya⟩
    have e2 : b (ib ⟨y, hyb⟩) = _ := wb ⟨y, hyb⟩
    change a (ia ⟨y, hya⟩) + b (ib ⟨y, hyb⟩) = _
    rw [e1, e2, Localization.add_mk]
    congr 1
    ring
theorem neg_mem' (k : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) (a : ∀ x : U, Loc 𝒜 x.1)
    (ha : (isLocallyFraction 𝒜 k).pred a) : (isLocallyFraction 𝒜 k).pred (-a) := fun x => by
  obtain ⟨V, m, iV, i, j, hij, r, s, hr, hs, hsn, w⟩ := ha x
  refine ⟨V, m, iV, i, j, hij, -r, s, neg_mem hr, hs, hsn, fun y => ?_⟩
  simp only [Pi.neg_apply, w y, Localization.neg_mk]
variable (𝒜) in

def twistSheafInType (k : ℤ) : Sheaf (Type u) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜 k)
def sectionsSubgroup (k : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    AddSubgroup (∀ x : U, Loc 𝒜 x.1) where
  carrier := {f | (isLocallyFraction 𝒜 k).pred f}
  zero_mem' := zero_mem' k U
  add_mem' := add_mem' k U _ _
  neg_mem' := neg_mem' k U _
instance (k : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    AddCommGroup ((twistSheafInType 𝒜 k).obj.obj U) :=
  (sectionsSubgroup k U.unop).toAddCommGroup
open ProjectiveSpectrum in

def toLocFun (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    (Proj.structureSheaf 𝒜).obj.obj (op U) →+* (∀ x : U, Loc 𝒜 x.1) where
  toFun t x := (t.1 x).val
  map_one' := by funext x; exact HomogeneousLocalization.val_one
  map_mul' a b := by funext x; exact HomogeneousLocalization.val_mul _ _
  map_zero' := by funext x; exact HomogeneousLocalization.val_zero
  map_add' a b := by funext x; exact HomogeneousLocalization.val_add _ _
open ProjectiveSpectrum in
instance (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Module ((Proj.structureSheaf 𝒜).obj.obj (op U)) (∀ x : U, Loc 𝒜 x.1) :=
  Module.compHom _ (toLocFun U)
open ProjectiveSpectrum in

def sectionsSubmodule (k : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Submodule ((Proj.structureSheaf 𝒜).obj.obj (op U)) (∀ x : U, Loc 𝒜 x.1) where
  __ := sectionsSubgroup k U
  smul_mem' t f hf x := by
    obtain ⟨V, hxV, iV, l, ⟨a, ha⟩, ⟨b, hb⟩, hbn, wt⟩ := t.2 x
    obtain ⟨W, hxW, iW, i, j, hij, r, s, hr, hs, hsn, wf⟩ := hf x
    refine ⟨V ⊓ W, ⟨hxV, hxW⟩, Opens.infLELeft _ _ ≫ iV, l + i, l + j, by push_cast; omega,
      a * r, b * s, SetLike.mul_mem_graded ha hr, SetLike.mul_mem_graded hb hs,
      fun ⟨y, hyV, hyW⟩ => nmem_mul (hbn ⟨y, hyV⟩) (hsn ⟨y, hyW⟩), fun ⟨y, hyV, hyW⟩ => ?_⟩
    have e1 : t.1 (iV ⟨y, hyV⟩) = _ := wt ⟨y, hyV⟩
    have e2 : f (iW ⟨y, hyW⟩) = _ := wf ⟨y, hyW⟩
    change (t.1 (iV ⟨y, hyV⟩)).val * f (iW ⟨y, hyW⟩) = _
    rw [e1, e2, HomogeneousLocalization.val_mk, Localization.mk_mul]
    rfl
open ProjectiveSpectrum in
instance (k : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((Proj.structureSheaf 𝒜).obj.obj U) ((twistSheafInType 𝒜 k).obj.obj U) :=
  (sectionsSubmodule k U.unop).module
variable (𝒜) in

def twistPresheafAb (k : ℤ) : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of ((twistSheafInType 𝒜 k).obj.obj U)
  map i := AddCommGrpCat.ofHom
    { toFun := (twistSheafInType 𝒜 k).obj.map i
      map_zero' := rfl
      map_add' _ _ := rfl }
end ProjTwist
open ProjTwist in

noncomputable def twistingSheaf (k : ℤ) : (Proj 𝒜).Modules where
  val :=
    letI (U : (Opens (Proj 𝒜))ᵒᵖ) :
        Module ((Proj 𝒜).ringCatSheaf.obj.obj U) ((twistPresheafAb 𝒜 k).obj U) :=
      let U' : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ := U
      inferInstanceAs (Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj U')
        ((twistSheafInType 𝒜 k).obj.obj U'))
    PresheafOfModules.ofPresheaf (R := (Proj 𝒜).ringCatSheaf.obj) (twistPresheafAb 𝒜 k)
      fun _ _ _ _ _ => rfl
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    (twistSheafInType 𝒜 k).2
namespace ProjTwist
variable {𝒜} {k : ℤ} {U V : (Proj 𝒜).Opens}
def val (s : Γ(twistingSheaf 𝒜 k, U)) : ∀ x : U, Loc 𝒜 x.1 := s.1
def mkSection (f : ∀ x : U, Loc 𝒜 x.1) (hf : (isLocallyFraction 𝒜 k).pred f) :
    Γ(twistingSheaf 𝒜 k, U) := ⟨f, hf⟩
end ProjTwist
end GroundTheory.Arith.SchemeCoh


