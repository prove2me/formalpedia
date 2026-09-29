-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.FiniteMapData.finite_H0_H1_lineBundle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f00a9567-3f37-5aee-b72b-e56130c64e30

import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Theorems.Thm_TwoChartCech_Sections_finite_H1_of_chartFinite
import Theorems.Thm_TwoChartCech_Sections_finite_H0_of_chartFinite
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_finite_H0_H1_lineBundle

set_option autoImplicit false

noncomputable section

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_finite_H0_H1_lineBundle.AlgebraicGeometry Opposite NeronModelInfra"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme IsAffineOpen SmoothProperCurve.FiniteMapData Scheme.TwoAffineOpenCover"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Γ basicOpen Opens basicOpen_le Cover TwoAffineOpenCover"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "cover cover_ρ0_apply cover_ρ1_apply lineBundleSections"
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"
namespace ChartFiniteInstances

variable {X : Scheme.{u}}

abbrev res {U W : X.Opens} (h : W ≤ U) : Γ(X, U) → Γ(X, W) := fun x => (X.presheaf.map (homOfLE h).op).hom x

theorem res_res' {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (x : Γ(X, V₁)) :
    res h₃₂ (res h₂₁ x) = res (h₃₂.trans h₂₁) x := by
  show (X.presheaf.map (homOfLE h₃₂).op).hom ((X.presheaf.map (homOfLE h₂₁).op).hom x) = _
  rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl

theorem res_self {V : X.Opens} (h : V ≤ V) (x : Γ(X, V)) : res h x = x := by
  show (X.presheaf.map (homOfLE h).op).hom x = x
  rw [Subsingleton.elim (homOfLE h) (𝟙 V), op_id, X.presheaf.map_id]; rfl

theorem exists_pow_mul_eq_res {U W : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) (hW : W = X.basicOpen f)
    (m : Γ(X, W)) :
    ∃ (x : Γ(X, U)) (n : ℕ), res (hW.le.trans (X.basicOpen_le f)) f ^ n * m
      = res (hW.le.trans (X.basicOpen_le f)) x := by
  subst hW
  haveI := hU.isLocalization_basicOpen f
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) m
  refine ⟨x, n, ?_⟩

  rw [mul_comm]
  simp [map_pow] at h
  exact h

theorem exists_pow_mul_eq_zero {U W : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) (hW : W = X.basicOpen f)
    (x : Γ(X, U)) (hx : res (hW.le.trans (X.basicOpen_le f)) x = 0) :
    ∃ n : ℕ, f ^ n * x = 0 := by
  subst hW
  haveI := hU.isLocalization_basicOpen f
  have hx' : algebraMap Γ(X, U) Γ(X, X.basicOpen f) x = 0 := hx
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f)] at hx'
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := hx'
  exact ⟨n, hn⟩

theorem finite_adjoin_of_aeval_finite {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A] (f : A)
    (h : (Polynomial.aeval f : Polynomial R →ₐ[R] A).toRingHom.Finite) :
    Module.Finite (Algebra.adjoin R ({f} : Set A)) A := by
  letI : Algebra (Polynomial R) A := (Polynomial.aeval f : Polynomial R →ₐ[R] A).toRingHom.toAlgebra
  haveI : Module.Finite (Polynomial R) A := h
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite (Polynomial R) A)
  refine Module.finite_def.mpr ⟨s, ?_⟩
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span (Polynomial R) (s : Set A) := by rw [hs]; trivial
  refine Submodule.span_induction (p := fun y _ => y ∈ Submodule.span (Algebra.adjoin R ({f} : Set A)) (s : Set A))
    (fun y hy => Submodule.subset_span hy) (Submodule.zero_mem _) (fun y z _ _ hy hz => Submodule.add_mem _ hy hz)
    (fun p y _ hy => ?_) hx

  have hp : (Polynomial.aeval f p : A) ∈ Algebra.adjoin R ({f} : Set A) := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨p, rfl⟩
  have : (p • y : A) = (⟨Polynomial.aeval f p, hp⟩ : Algebra.adjoin R ({f} : Set A)) • y := rfl
  show p • y ∈ Submodule.span (Algebra.adjoin R ({f} : Set A)) (s : Set A)
  rw [this]
  exact Submodule.smul_mem _ _ hy

end ChartFiniteInstances
end AlgebraicGeometry.Scheme.TwoAffineOpenCover

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme IsAffineOpen SmoothProperCurve.FiniteMapData Scheme.TwoAffineOpenCover"
namespace SmoothProperCurve
p2m_export "AlgebraicGeometry.SmoothProperCurve" "FiniteMapData"
namespace FiniteMapData
p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "twoAffineOpenCover finite_f U f m V isAffineOpen_U inf_eq_basicOpen_g isAffineOpen_V finite_g g inf_eq_basicOpen res_f_mul_res_g"
p2m_open "AlgebraicGeometry.SmoothProperCurve.FiniteMapData AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_finite_H0_H1_lineBundle.AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_finite_H0_H1_lineBundle.AlgebraicGeometry.Scheme.TwoAffineOpenCover.ChartFiniteInstances"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} (𝔉 : FiniteMapData c ε)

theorem VU_le_U : 𝔉.V ⊓ 𝔉.U ≤ 𝔉.U := inf_le_right
theorem VU_le_V : 𝔉.V ⊓ 𝔉.U ≤ 𝔉.V := inf_le_left
private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.VU_eq_basicOpen_g : 𝔉.V ⊓ 𝔉.U = C.basicOpen 𝔉.g := by rw [inf_comm, 𝔉.inf_eq_basicOpen_g]
p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "VU_eq_basicOpen_g"
private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.VU_eq_basicOpen_f : 𝔉.V ⊓ 𝔉.U = C.basicOpen 𝔉.f := by rw [inf_comm, 𝔉.inf_eq_basicOpen]

p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "VU_eq_basicOpen_f"
variable (c) in

private abbrev _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.gA0 : (𝔉.twoAffineOpenCover.cover c).A0 := 𝔉.g
p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "gA0"
variable (c) in

private abbrev _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.fA1 : (𝔉.twoAffineOpenCover.cover c).A1 := 𝔉.f

p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "fA1"

private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.ρ0_g_mul_ρ1_f :
    (𝔉.twoAffineOpenCover.cover c).ρ0 (𝔉.gA0 c) * (𝔉.twoAffineOpenCover.cover c).ρ1 (𝔉.fA1 c) = 1 := by
  rw [cover_ρ0_apply, cover_ρ1_apply, mul_comm]
  have h := congrArg (res (X := C) (inf_comm 𝔉.V 𝔉.U).le) 𝔉.res_f_mul_res_g
  simp only [res, map_mul, map_one] at h
  rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp] at h
  exact h

p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "ρ0_g_mul_ρ1_f"
private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.loc0 (m : (𝔉.twoAffineOpenCover.cover c).A01) :
    ∃ (x : (𝔉.twoAffineOpenCover.cover c).A0) (n : ℕ),
      (𝔉.twoAffineOpenCover.cover c).ρ0 (𝔉.gA0 c) ^ n * m = (𝔉.twoAffineOpenCover.cover c).ρ0 x := by
  obtain ⟨x, n, h⟩ := exists_pow_mul_eq_res 𝔉.isAffineOpen_V 𝔉.g 𝔉.VU_eq_basicOpen_g m
  exact ⟨x, n, h⟩

p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "loc0"
private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.loc1 (m : (𝔉.twoAffineOpenCover.cover c).A01) :
    ∃ (y : (𝔉.twoAffineOpenCover.cover c).A1) (n : ℕ),
      (𝔉.twoAffineOpenCover.cover c).ρ1 (𝔉.fA1 c) ^ n * m = (𝔉.twoAffineOpenCover.cover c).ρ1 y := by
  obtain ⟨y, n, h⟩ := exists_pow_mul_eq_res 𝔉.isAffineOpen_U 𝔉.f 𝔉.VU_eq_basicOpen_f m
  exact ⟨y, n, h⟩

p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "loc1"
private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.tors0 (x : (𝔉.twoAffineOpenCover.cover c).A0) (hx : (𝔉.twoAffineOpenCover.cover c).ρ0 x = 0) :
    ∃ n : ℕ, 𝔉.gA0 c ^ n * x = 0 :=
  exists_pow_mul_eq_zero 𝔉.isAffineOpen_V 𝔉.g 𝔉.VU_eq_basicOpen_g x hx

p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "tors0"
private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.tors1 (y : (𝔉.twoAffineOpenCover.cover c).A1) (hy : (𝔉.twoAffineOpenCover.cover c).ρ1 y = 0) :
    ∃ n : ℕ, 𝔉.fA1 c ^ n * y = 0 :=
  exists_pow_mul_eq_zero 𝔉.isAffineOpen_U 𝔉.f 𝔉.VU_eq_basicOpen_f y hy

p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "tors1"

private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.chartFinite_lineBundle (t : (𝔉.twoAffineOpenCover.cover c).A01ˣ) :
    let 𝒰 := 𝔉.twoAffineOpenCover.cover c
    let S := 𝔉.twoAffineOpenCover.lineBundleSections c t
    (𝒰.ρ0 (𝔉.gA0 c) * 𝒰.ρ1 (𝔉.fA1 c) = 1) ∧
    Module.Finite (Algebra.adjoin R ({𝔉.gA0 c} : Set 𝒰.A0)) S.M0 ∧
    Module.Finite (Algebra.adjoin R ({𝔉.fA1 c} : Set 𝒰.A1)) S.M1 ∧
    (∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ0 (𝔉.gA0 c)) ^ n • m ∈ LinearMap.range S.r0) ∧
    (∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ1 (𝔉.fA1 c)) ^ n • m ∈ LinearMap.range S.r1) ∧
    (∀ x : S.M0, S.r0 x = 0 → ∃ n : ℕ, 𝔉.gA0 c ^ n • x = 0) ∧
    (∀ y : S.M1, S.r1 y = 0 → ∃ n : ℕ, 𝔉.fA1 c ^ n • y = 0) := by
  intro 𝒰 S
  refine ⟨𝔉.ρ0_g_mul_ρ1_f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact finite_adjoin_of_aeval_finite (𝔉.gA0 c) 𝔉.finite_g
  · exact finite_adjoin_of_aeval_finite (𝔉.fA1 c) 𝔉.finite_f
  · intro m
    obtain ⟨x, n, h⟩ := 𝔉.loc0 m
    exact ⟨n, x, by rw [TwoChartCech.Cover.lineBundle_r0_apply, smul_eq_mul]; exact h.symm⟩
  · intro m
    obtain ⟨y, n, h⟩ := 𝔉.loc1 ((↑t⁻¹ : 𝒰.A01) * m)
    refine ⟨n, y, ?_⟩
    rw [TwoChartCech.Cover.lineBundle_r1_apply, smul_eq_mul, ← h, mul_left_comm, ← mul_assoc (t : 𝒰.A01),
      Units.mul_inv, one_mul]
  · intro x hx
    rw [TwoChartCech.Cover.lineBundle_r0_apply] at hx
    obtain ⟨n, hn⟩ := 𝔉.tors0 x hx
    exact ⟨n, by rw [smul_eq_mul]; exact hn⟩
  · intro y hy
    rw [TwoChartCech.Cover.lineBundle_r1_apply] at hy
    obtain ⟨n, hn⟩ := 𝔉.tors1 y ((Units.mul_right_eq_zero t).mp hy)
    exact ⟨n, by rw [smul_eq_mul]; exact hn⟩

p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "chartFinite_lineBundle"
end AlgebraicGeometry.SmoothProperCurve.FiniteMapData

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (t : (𝔉.twoAffineOpenCover.cover c).A01ˣ) :
    Module.Finite R (𝔉.twoAffineOpenCover.lineBundleSections c t).H0 ∧
      Module.Finite R (𝔉.twoAffineOpenCover.lineBundleSections c t).H1 := by
  obtain ⟨hfg, hfin0, hfin1, hloc0, hloc1, htors0, htors1⟩ := 𝔉.chartFinite_lineBundle t
  exact ⟨TwoChartCech.Sections.finite_H0_of_chartFinite _ (𝔉.gA0 c) (𝔉.fA1 c) hfg hfin0 hfin1 hloc0 hloc1 htors0 htors1,
    TwoChartCech.Sections.finite_H1_of_chartFinite _ (𝔉.gA0 c) (𝔉.fA1 c) hfg hfin0 hloc0 hloc1⟩

end

end S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_finite_H0_H1_lineBundle
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_finite_H0_H1_lineBundle (solution)
