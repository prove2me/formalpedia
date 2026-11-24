-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_LocalTraceForms_TraceCompSmulRight
-- name    : Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_LocalTraceForms_TraceCompSmulRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:51.597381+00:00
-- url     : https://prove2.me/theorems/7a22d82c-96a7-43d9-bcf3-324d432002d4
-- title:
--   Trace Comp Smul Right
-- statement:
--   Definitions and structural lemmas for Trace Comp Smul Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/LocalTraceForms/TraceCompSmulRight.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
namespace PositivityTheory.RgUd.TP.Loc.Ptf
section Fibre
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
theorem mk_smul (I : Ideal R) (r : R) (w : V ⧸ (I • (⊤ : Submodule R V))) :
    (Ideal.Quotient.mk I r) • w = r • w := by
  induction w using Submodule.Quotient.induction_on with
  | H v => rfl
theorem le_comap (I : Ideal R) (x : V →ₗ[R] V) :
    I • (⊤ : Submodule R V) ≤ (I • (⊤ : Submodule R V)).comap x := by
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
  exact Submodule.smul_mono le_rfl le_top
def xq (I : Ideal R) (x : V →ₗ[R] V) :
    (V ⧸ (I • (⊤ : Submodule R V))) →ₗ[R ⧸ I] (V ⧸ (I • (⊤ : Submodule R V))) where
  toFun := Submodule.mapQ _ _ x (le_comap I x)
  map_add' := map_add _
  map_smul' c w := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    simp only [RingHom.id_apply, mk_smul]
    exact map_smul _ r w
theorem xq_mk (I : Ideal R) (x : V →ₗ[R] V) (v : V) :
    xq I x (Submodule.Quotient.mk v) = Submodule.Quotient.mk (x v) := rfl
theorem xq_ext (I : Ideal R) {f g : (V ⧸ (I • (⊤ : Submodule R V))) →ₗ[R ⧸ I] (V ⧸ (I • (⊤ : Submodule R V)))}
    (h : ∀ v : V, f (Submodule.Quotient.mk v) = g (Submodule.Quotient.mk v)) : f = g :=
  LinearMap.ext fun w => by
    induction w using Submodule.Quotient.induction_on with
    | H v => exact h v
theorem xq_add (I : Ideal R) (x y : V →ₗ[R] V) : xq I (x + y) = xq I x + xq I y :=
  xq_ext I fun _ => rfl
theorem xq_smul {k : Type*} [Field k] [Algebra k R] [Module k V] [IsScalarTower k R V] (I : Ideal R) (c : k)
    (x : V →ₗ[R] V) : xq I (c • x) = (algebraMap k (R ⧸ I) c) • xq I x := by
  refine xq_ext I fun v => ?_
  rw [LinearMap.smul_apply, xq_mk, xq_mk, LinearMap.smul_apply, ← algebraMap_smul R c (x v),
    ← Ideal.Quotient.mk_algebraMap, mk_smul]
  rfl
end Fibre
open Classical
attribute [local instance] Ideal.Quotient.field
instance isMax {R : Type*} [CommRing R] (I : MaximalSpectrum R) : I.asIdeal.IsMaximal := I.isMaximal
theorem finQ (k : Type*) {R V : Type*} [Field k] [CommRing R] [Algebra k R] [AddCommGroup V] [Module R V] [Module k V]
    [IsScalarTower k R V] [FiniteDimensional k V] (I : MaximalSpectrum R) :
    FiniteDimensional (R ⧸ I.asIdeal) (V ⧸ (I.asIdeal • (⊤ : Submodule R V))) := by
  haveI : Module.Finite R V := Module.Finite.of_restrictScalars_finite k R V
  exact Module.Finite.of_restrictScalars_finite R _ _
theorem exists_lam (k : Type*) {R : Type*} [Field k] [CommRing R] [Algebra k R] (I : MaximalSpectrum R) :
    ∃ l : (R ⧸ I.asIdeal) →ₗ[k] k, l 1 ≠ 0 := by
  let b := Module.Free.chooseBasis k (R ⧸ I.asIdeal)
  have h1 : b.repr 1 ≠ 0 := by
    intro h
    exact one_ne_zero (b.repr.injective (h.trans (map_zero _).symm))
  obtain ⟨i, hi⟩ : ∃ i, b.repr 1 i ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact h1 (Finsupp.ext hne)
  exact ⟨b.coord i, hi⟩
variable {k R V : Type*} [Field k] [CommRing R] [IsArtinianRing R] [IsReduced R] [Algebra k R]
  [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V] [FiniteDimensional k V]
instance : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
def lam (I : MaximalSpectrum R) : (R ⧸ I.asIdeal) →ₗ[k] k := (exists_lam k I).choose
def tI (I : MaximalSpectrum R) (x : V →ₗ[R] V) : k :=
  haveI := finQ k (V := V) I
  lam (k := k) I (LinearMap.trace (R ⧸ I.asIdeal) _ (xq I.asIdeal x))
theorem tI_add (I : MaximalSpectrum R) (x y : V →ₗ[R] V) : tI (k := k) I (x + y) = tI I x + tI I y := by
  simp only [tI, xq_add, map_add]
theorem tI_smul (I : MaximalSpectrum R) (c : k) (x : V →ₗ[R] V) : tI (k := k) I (c • x) = c • tI I x := by
  simp only [tI, xq_smul, map_smul, smul_eq_mul]
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]
def tau : (V →ₗ[R] V) →ₗ[k] k where
  toFun x := ∑ I : MaximalSpectrum R, tI (k := k) I x
  map_add' x y := by simp only [tI_add, Finset.sum_add_distrib]
  map_smul' c x := by simp only [tI_smul, RingHom.id_apply, Finset.smul_sum]
def eI (I : MaximalSpectrum R) : R := (IsArtinianRing.equivPi R).symm (Pi.single I 1)
theorem equivPi_apply' (r : R) (J : MaximalSpectrum R) :
    IsArtinianRing.equivPi R r J = Ideal.Quotient.mk J.asIdeal r := rfl
theorem eI_mul (I : MaximalSpectrum R) {r : R} (hr : r ∈ I.asIdeal) : eI I * r = 0 := by
  apply (IsArtinianRing.equivPi R).injective
  rw [map_mul, map_zero, eI, AlgEquiv.apply_symm_apply]
  funext J
  by_cases h : J = I
  · subst h
    simp [equivPi_apply', Ideal.Quotient.eq_zero_iff_mem.2 hr]
  · simp [Pi.single_eq_of_ne h]
theorem eI_smul_eq_zero (I : MaximalSpectrum R) {w : V} (hw : w ∈ I.asIdeal • (⊤ : Submodule R V)) :
    eI I • w = 0 := by
  refine Submodule.smul_induction_on (p := fun w => eI I • w = 0) hw (fun r hr m _ => ?_) (fun a b ha hb => ?_)
  · rw [smul_smul, eI_mul I hr, zero_smul]
  · rw [smul_add, ha, hb, add_zero]
def sec (I : MaximalSpectrum R) : (V ⧸ (I.asIdeal • (⊤ : Submodule R V))) →ₗ[R] V :=
  (I.asIdeal • (⊤ : Submodule R V)).liftQ (eI I • LinearMap.id) fun w hw => by
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
    exact eI_smul_eq_zero I hw
end PositivityTheory.RgUd.TP.Loc.Ptf


