-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_of_forall_mem_adjoin_iff_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a241e755-aab6-5930-b14e-b33f7c259142

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ValuationSubring_exists_smul_mem_of_transcendental_residue
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic.AlgebraicCurve IsLocalRing Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation"
namespace RegularProlongation
p2m_export "AlgebraicCurve.RegularProlongation" "isUnit_of_residue_ne_zero integers residue_algebraMap residue_surjective algebraMap_mem_iff exists_smul_mem ker_residue residue"
namespace SolExistsOfForallMemAdjoinIffOfIsAlgebraic
p2m_open "AlgebraicCurve.RegularProlongation AlgebraicCurve"

section Units

variable {F : Type*} [Field F]

theorem inv_mem_of_isUnit {V : ValuationSubring F} {x : F} {hx : x ∈ V}
    (hu : IsUnit (⟨x, hx⟩ : V)) : x⁻¹ ∈ V := by
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  have hxy : x * (y : F) = 1 := by
    have := congrArg (fun z : V => (z : F)) hy
    simpa using this
  have : (y : F) = x⁻¹ := eq_inv_of_mul_eq_one_right hxy
  rw [← this]
  exact y.2

theorem isUnit_of_inv_mem {V : ValuationSubring F} {x : F} (hx : x ∈ V) (hx0 : x ≠ 0)
    (hinv : x⁻¹ ∈ V) : IsUnit (⟨x, hx⟩ : V) :=
  IsUnit.of_mul_eq_one (⟨x⁻¹, hinv⟩ : V) (Subtype.ext (mul_inv_cancel₀ hx0))

end Units

section Constants

variable {L : Type*} [Field L] (A : ValuationSubring L)
  {F : Type*} [Field F] [Algebra L F]
  (V : ValuationSubring F) (hV : ∀ x : L, algebraMap L F x ∈ V ↔ x ∈ A)

def toV : A →+* V where
  toFun a := ⟨algebraMap L F a, (hV a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_toV (a : A) : ((toV A V hV a : V) : F) = algebraMap L F a := rfl

theorem isLocalHom_toV : IsLocalHom (toV A V hV) := by
  constructor
  intro a hu
  by_cases ha0 : (a : L) = 0
  · exfalso
    have h0 : toV A V hV a = 0 := Subtype.ext (by simp [ha0])
    rw [h0] at hu
    exact not_isUnit_zero hu
  · have hinvF : (algebraMap L F a)⁻¹ ∈ V := inv_mem_of_isUnit hu
    rw [← map_inv₀] at hinvF
    have hinvA : (a : L)⁻¹ ∈ A := (hV _).mp hinvF
    have : IsUnit (⟨(a : L), a.2⟩ : A) := isUnit_of_inv_mem a.2 ha0 hinvA
    simpa using this

theorem coe_eval_map_toV (P : A[X]) (x : V) :
    (((P.map (toV A V hV)).eval x : V) : F) =
      P.eval₂ ((algebraMap L F).comp A.subtype) (x : F) := by
  rw [Polynomial.eval_map]
  have h := Polynomial.hom_eval₂ P (toV A V hV) V.subtype x
  have hcomp : V.subtype.comp (toV A V hV) = (algebraMap L F).comp A.subtype := by
    ext a
    rfl
  rw [hcomp] at h
  exact h

theorem residue_eval_map_toV {E : Type*} [Field E] [Algebra (ResidueField A) E]
    (ρ : V →+* E)
    (hρ : ∀ a : A, ρ (toV A V hV a) = algebraMap (ResidueField A) E (IsLocalRing.residue A a))
    (P : A[X]) (x : V) :
    ρ ((P.map (toV A V hV)).eval x) = aeval (ρ x) (P.map (IsLocalRing.residue A)) := by
  rw [Polynomial.eval_map, Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
  congr 1
  ext a
  simp [hρ]

theorem eval₂_mem_adjoin (P : A[X]) (x : F) :
    P.eval₂ ((algebraMap L F).comp A.subtype) x ∈ IntermediateField.adjoin L ({x} : Set F) := by
  have h : P.eval₂ ((algebraMap L F).comp A.subtype) x = aeval x (P.map A.subtype) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  rw [h]
  exact IntermediateField.algebra_adjoin_le_adjoin L _ (Polynomial.aeval_mem_adjoin_singleton L x)

end Constants

section Setting

variable {L : Type*} [Field L] {A : ValuationSubring L}
  {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
  (R : RegularProlongation A F Fbar) {f : F} (hfO : f ∈ R.integers)
  {W : ValuationSubring F}
  (hW : ∀ e : F, e ∈ IntermediateField.adjoin L ({f} : Set F) → (e ∈ W ↔ e ∈ R.integers))

include hW in

theorem algebraMap_mem_W_iff (x : L) : algebraMap L F x ∈ W ↔ x ∈ A :=
  (hW _ (IntermediateField.algebraMap_mem _ x)).trans (R.algebraMap_mem_iff x)

include hW hfO in

theorem f_mem_W : f ∈ W :=
  (hW f (IntermediateField.mem_adjoin_simple_self L f)).mpr hfO

@[reducible] noncomputable def residueFieldAlgebra : Algebra (ResidueField A) (ResidueField W) :=
  (@ResidueField.map A W _ _ _ _ (toV A W (algebraMap_mem_W_iff R hW))
    (isLocalHom_toV A W (algebraMap_mem_W_iff R hW))).toAlgebra

theorem residue_toV_eq (a : A) :
    letI := residueFieldAlgebra R hW
    IsLocalRing.residue W (toV A W (algebraMap_mem_W_iff R hW) a) =
      algebraMap (ResidueField A) (ResidueField W) (IsLocalRing.residue A a) := by
  letI := residueFieldAlgebra R hW
  show IsLocalRing.residue W (toV A W (algebraMap_mem_W_iff R hW) a) =
    @ResidueField.map A W _ _ _ _ (toV A W (algebraMap_mem_W_iff R hW))
      (isLocalHom_toV A W (algebraMap_mem_W_iff R hW)) (IsLocalRing.residue A a)
  exact (@ResidueField.map_residue A W _ _ _ _ (toV A W (algebraMap_mem_W_iff R hW))
    (isLocalHom_toV A W (algebraMap_mem_W_iff R hW)) a).symm

include hfO hW in

theorem transcendental_residue_W [Algebra (ResidueField A) (ResidueField W)]
    (hcompat : ∀ a : A, IsLocalRing.residue W (toV A W (algebraMap_mem_W_iff R hW) a) =
      algebraMap (ResidueField A) (ResidueField W) (IsLocalRing.residue A a))
    (htr : Transcendental (ResidueField A) (R.residue ⟨f, hfO⟩)) :
    Transcendental (ResidueField A) (IsLocalRing.residue W ⟨f, f_mem_W R hfO hW⟩) := by
  rw [transcendental_iff]
  intro p hp
  obtain ⟨P, rfl⟩ :=
    Polynomial.map_surjective (IsLocalRing.residue A) IsLocalRing.residue_surjective p

  set hOW := algebraMap_mem_W_iff R hW
  set fW : W := ⟨f, f_mem_W R hfO hW⟩
  set fO : R.integers := ⟨f, hfO⟩
  set yW : W := (P.map (toV A W hOW)).eval fW
  set yO : R.integers := (P.map (toV A R.integers R.algebraMap_mem_iff)).eval fO
  have hyW : (yW : F) = P.eval₂ ((algebraMap L F).comp A.subtype) f :=
    coe_eval_map_toV A W hOW P fW
  have hyO : (yO : F) = P.eval₂ ((algebraMap L F).comp A.subtype) f :=
    coe_eval_map_toV A R.integers R.algebraMap_mem_iff P fO

  have hres_W : IsLocalRing.residue W yW = 0 := by
    rw [residue_eval_map_toV A W hOW (IsLocalRing.residue W) hcompat P fW]
    exact hp
  have hyW_max : yW ∈ maximalIdeal W := (residue_eq_zero_iff _).mp hres_W

  by_contra hp0
  have hres_O : R.residue yO ≠ 0 := by
    rw [residue_eval_map_toV A R.integers R.algebraMap_mem_iff R.residue R.residue_algebraMap P fO]
    intro h0
    exact hp0 ((transcendental_iff.mp htr) _ h0)
  have hunitO : IsUnit yO := R.isUnit_of_residue_ne_zero hres_O
  have hy0 : (yO : F) ≠ 0 := by
    intro h0
    apply hres_O
    have : yO = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hinvO : (yO : F)⁻¹ ∈ R.integers := inv_mem_of_isUnit (hx := yO.2) (by simpa using hunitO)
  have hyK : (yO : F) ∈ IntermediateField.adjoin L ({f} : Set F) := by
    rw [hyO]
    exact eval₂_mem_adjoin A P f
  have hinvW : (yO : F)⁻¹ ∈ W := (hW _ (inv_mem hyK)).mpr hinvO
  have hunitW : IsUnit yW := by
    have hcoe : (yW : F) = (yO : F) := by rw [hyW, hyO]
    have h := isUnit_of_inv_mem (V := W) (x := (yO : F)) (hcoe ▸ yW.2) hy0 hinvW
    have hEq : (⟨(yO : F), hcoe ▸ yW.2⟩ : W) = yW := Subtype.ext hcoe.symm
    rwa [hEq] at h
  exact (IsLocalRing.mem_maximalIdeal _).mp hyW_max hunitW

end Setting

end AlgebraicCurve.RegularProlongation.SolExistsOfForallMemAdjoinIffOfIsAlgebraic
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic.AlgebraicCurve.RegularProlongation.SolExistsOfForallMemAdjoinIffOfIsAlgebraic"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic.AlgebraicCurve.RegularProlongation"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic.AlgebraicCurve"

open AlgebraicCurve.RegularProlongation.SolExistsOfForallMemAdjoinIffOfIsAlgebraic in

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (f : F) (hfO : f ∈ R.integers)
    (htr : Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfO⟩))
    [Algebra.IsAlgebraic (IntermediateField.adjoin L ({f} : Set F)) F]
    (W : ValuationSubring F)
    (hW : ∀ e : F, e ∈ IntermediateField.adjoin L ({f} : Set F) → (e ∈ W ↔ e ∈ R.integers)) :
    ∃ (_ : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField W))
      (R' : RegularProlongation A F (IsLocalRing.ResidueField W)),
      R'.integers = W ∧ ∃ hf' : f ∈ R'.integers,
        Transcendental (IsLocalRing.ResidueField A) (R'.residue ⟨f, hf'⟩) := by
  letI := residueFieldAlgebra R hW
  have hOW := algebraMap_mem_W_iff R hW
  have hfW : f ∈ W := f_mem_W R hfO hW
  have hcompat := residue_toV_eq R hW
  have htrW : Transcendental (ResidueField A) (IsLocalRing.residue W ⟨f, hfW⟩) :=
    transcendental_residue_W R hfO hW hcompat htr
  have hreg : ∀ g : F, g ≠ 0 → ∃ c : L, ∃ h : c • g ∈ W, IsLocalRing.residue W ⟨c • g, h⟩ ≠ 0 :=
    fun g hg =>
      ValuationSubring.exists_smul_mem_of_transcendental_residue A W hOW (IsLocalRing.residue W)
        IsLocalRing.ker_residue hcompat f hfW htrW g hg
  refine ⟨residueFieldAlgebra R hW,
    { integers := W
      residue := IsLocalRing.residue W
      algebraMap_mem_iff := hOW
      residue_surjective := IsLocalRing.residue_surjective
      ker_residue := IsLocalRing.ker_residue
      residue_algebraMap := hcompat
      exists_smul_mem := hreg }, rfl, hfW, htrW⟩

end S_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_of_forall_mem_adjoin_iff_of_isAlgebraic (solution)
