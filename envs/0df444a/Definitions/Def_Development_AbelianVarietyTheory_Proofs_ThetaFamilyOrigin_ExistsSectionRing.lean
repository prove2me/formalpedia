-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsSectionRing
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsSectionRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:17:53.124001+00:00
-- url     : https://prove2.me/theorems/bad33a31-527d-40dc-a572-a4a908094a48
-- title:
--   Exists Section Ring
-- statement:
--   Definitions and structural lemmas for Exists Section Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsSectionRing.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialMemReesAlgIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SectionRing
section Abstract
open Polynomial
variable {K A : Type} [Field K] [CommRing A] [Algebra K A]
def polyAlg (M : ℕ → Submodule K A) [SetLike.GradedMonoid M] : Subalgebra K A[X] := GlobalTheory.ReesAlgebraMembership.reesAlg M
variable (M : ℕ → Submodule K A) [SetLike.GradedMonoid M]
def mono (e : ℕ) : M e →ₗ[K] polyAlg M where
  toFun a := ⟨monomial e (a : A), fun n => by
    rw [coeff_monomial]
    split_ifs with h
    · exact h ▸ a.2
    · exact (M n).zero_mem⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' c a := Subtype.ext (smul_monomial c e (a : A)).symm
theorem mono_val (e : ℕ) (a : M e) : (mono M e a : A[X]) = monomial e (a : A) := rfl
def piece (e : ℕ) : Submodule K (polyAlg M) := LinearMap.range (mono M e)
instance : SetLike.GradedMonoid (piece M) where
  one_mem := ⟨⟨1, SetLike.one_mem_graded M⟩, Subtype.ext (by simp [mono_val])⟩
  mul_mem := by
    rintro i j _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨⟨a * b, SetLike.mul_mem_graded a.2 b.2⟩,
      Subtype.ext (by simp [mono_val, monomial_mul_monomial])⟩
theorem coeff_coe (x : DirectSum ℕ fun e => piece M e) (n : ℕ) :
    ((DirectSum.coeAddMonoidHom (piece M) x : polyAlg M) : A[X]).coeff n =
      ((x n : polyAlg M) : A[X]).coeff n := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i y =>
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases h : i = n
    · subst h
      rw [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
      obtain ⟨_, a, rfl⟩ := y
      simp [mono_val, coeff_monomial, h]
  | add x y hx hy => simp [hx, hy]
theorem isInternal : DirectSum.IsInternal (piece M) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    ext1 n
    have h := coeff_coe M x n
    rw [hx] at h
    obtain ⟨a, ha⟩ := (x n).2
    rw [← ha, mono_val, coeff_monomial_same] at h
    have ha0 : a = 0 := Subtype.ext (by simpa using h.symm)
    apply Subtype.ext
    rw [← ha, ha0, map_zero]
    rfl
  · intro r
    refine ⟨∑ n ∈ (r : A[X]).support,
      DirectSum.of (fun e => piece M e) n ⟨mono M n ⟨_, r.2 n⟩, _, rfl⟩, ?_⟩
    rw [map_sum]
    apply Subtype.ext
    simp only [DirectSum.coeAddMonoidHom_of, AddSubmonoidClass.coe_finset_sum, mono_val]
    exact (as_sum_support _).symm
def grading : GradedAlgebra (piece M) where
  toGradedMonoid := inferInstance
  toDecomposition := (isInternal M).chooseDecomposition
end Abstract
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
section Sections
variable {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (L : LB X)
def constHom (U : X.Opens) : K →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
theorem res_constHom {U V : X.Opens} (h : V ≤ U) (a : K) :
    (X.presheaf.map (homOfLE h).op).hom (constHom p U a) = constHom p V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)
abbrev chart (j : PUnit → L.ι) : X.Opens := LB.wchart L (K := PUnit) (fun _ => 𝟙 X) j
def Fam (_p : X ⟶ Sp K) (L : LB X) : Type := ∀ j : PUnit → L.ι, Γ(X, chart L j)
instance : CommRing (Fam p L) := inferInstanceAs (CommRing (∀ j : PUnit → L.ι, Γ(X, chart L j)))
instance : Algebra K (Fam p L) :=
  (Pi.ringHom (fun j => constHom p (chart L j)) :
    K →+* ∀ j : PUnit → L.ι, Γ(X, chart L j)).toAlgebra
def evalFam (j : PUnit → L.ι) : Fam p L →+* Γ(X, chart L j) :=
  Pi.evalRingHom (fun j : PUnit → L.ι => Γ(X, chart L j)) j
def trans (e : ℕ) (i j : PUnit → L.ι) : Γ(X, chart L i ⊓ chart L j) :=
  ((lbPow L e).g i j).val
theorem trans_zero (i j : PUnit → L.ι) : trans L 0 i j = 1 := by
  have : (lbPow L 0).g i j = 1 := by
    unfold lbPow LB.LinComb
    dsimp only
    exact Finset.prod_eq_one fun _ _ => zpow_zero _
  unfold trans
  rw [this]
  rfl
theorem trans_add (e e' : ℕ) (i j : PUnit → L.ι) :
    trans L (e + e') i j = trans L e i j * trans L e' i j := by
  unfold trans lbPow LB.LinComb
  dsimp only
  rw [← Units.val_mul, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun _ _ => ?_
  rw [Nat.cast_add, _root_.zpow_add]
def secs (e : ℕ) : Submodule K (Fam p L) where
  carrier := {f | ∀ i j,
    (X.presheaf.map (homOfLE (inf_le_left : chart L i ⊓ chart L j ≤ chart L i)).op).hom
        (evalFam p L i f) =
      trans L e i j *
        (X.presheaf.map (homOfLE (inf_le_right : chart L i ⊓ chart L j ≤ chart L j)).op).hom
          (evalFam p L j f)}
  add_mem' := fun {a b} ha hb i j => by
    simp only [map_add, ha i j, hb i j, _root_.mul_add]
  zero_mem' := fun i j => by simp only [map_zero, MulZeroClass.mul_zero]
  smul_mem' := fun c a ha i j => by
    have h : ∀ k, evalFam p L k (c • a) = constHom p _ c * evalFam p L k a := fun k => rfl
    rw [h, h, map_mul, map_mul, res_constHom, res_constHom, ha i j]
    ring
instance : SetLike.GradedMonoid (secs p L) where
  one_mem := fun i j => by
    simp only [map_one, trans_zero, _root_.mul_one]
  mul_mem := fun e e' a b ha hb i j => by
    simp only [map_mul, ha i j, hb i j, trans_add]
    ring
def secEquiv (e : ℕ) : (lbPow L e).Sec ≃ secs p L e where
  toFun s := ⟨s.f, s.compat⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
end Sections
end GlobalTheory.SectionRing


