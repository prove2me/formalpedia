-- Prove2me | Definitions.Def_DedekindZeta_PoissonSummation
-- name    : DedekindZeta_PoissonSummation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T23:45:02.643938+00:00
-- url     : https://prove2.me/theorems/092633d7-b61c-4d87-93b5-a9e71dc27ab2
-- title:
--   Poisson Summation
-- statement:
--   Definitions and structural lemmas for Poisson Summation, from Mathlib Initiative and contributors's pinned A real sum-product counterexample conditional on Martinet’s tower theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PoissonSummation.lean

import Mathlib
set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
namespace DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
noncomputable def dualLattice (L : Submodule ℤ V) : Submodule ℤ V :=
  LinearMap.BilinForm.dualSubmodule (innerₗ V) L
theorem innerₗ_nondegenerate : (innerₗ V).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h := hx x
    rw [innerₗ_apply_apply] at h
    exact inner_self_eq_zero.mp h
  · have h := hy y
    rw [innerₗ_apply_apply] at h
    exact inner_self_eq_zero.mp h
theorem dualLattice_eq_span_dualBasis (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    letI := Classical.decEq (Module.Free.ChooseBasisIndex ℤ L)
    dualLattice L = Submodule.span ℤ (Set.range
      (LinearMap.BilinForm.dualBasis (innerₗ V) innerₗ_nondegenerate
        ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L))) := by
  classical
  set b := Module.Free.chooseBasis ℤ L with hb
  set B : Basis (Module.Free.ChooseBasisIndex ℤ L) ℝ V := b.ofZLatticeBasis ℝ L with hB
  have hLspan : L = Submodule.span ℤ (Set.range B) := (b.ofZLatticeBasis_span ℝ).symm
  change LinearMap.BilinForm.dualSubmodule (innerₗ V) L = _
  -- Rewrite the explicit `L` argument only (a plain `rw [hLspan]` would also try
  -- to rewrite the `L` hidden inside `B = b.ofZLatticeBasis ℝ L`).
  exact (congrArg (LinearMap.BilinForm.dualSubmodule (innerₗ V)) hLspan).trans
    (LinearMap.BilinForm.dualSubmodule_span_of_basis _ innerₗ_nondegenerate B)
instance instDiscreteTopologyDualLattice (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] : DiscreteTopology (dualLattice L) := by
  classical
  rw [dualLattice_eq_span_dualBasis L]
  infer_instance
section Periodisation
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (f : SchwartzMap V ℂ)
noncomputable def periodisation : V → ℂ := fun x => ∑' v : L, (f : V → ℂ) (x + v)
theorem periodisation_apply (x : V) :
    periodisation L f x = ∑' v : L, (f : V → ℂ) (x + v) := rfl
theorem periodisation_add_mem (x : V) {v : V} (hv : v ∈ L) :
    periodisation L f (x + v) = periodisation L f x := by
  rw [periodisation_apply, periodisation_apply]
  have hreindex :=
    Equiv.tsum_eq (Equiv.addRight (⟨v, hv⟩ : L))
      (fun w : L => (f : V → ℂ) (x + w))
  rw [← hreindex]
  refine tsum_congr fun w => ?_
  congr 1
  simp only [Equiv.coe_addRight, Submodule.coe_add]
  abel
noncomputable def periodisationTorus : (V ⧸ L.toAddSubgroup) → ℂ := fun q =>
  Quotient.liftOn' q (periodisation L f) <| by
    intro a b h
    rw [QuotientAddGroup.leftRel_apply] at h
    have hv : -a + b ∈ L := by simpa using h
    have : periodisation L f (a + (-a + b)) = periodisation L f a :=
      periodisation_add_mem L f a hv
    simpa using this.symm
end Periodisation
section FourierCoefficients
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (f : SchwartzMap V ℂ)
end FourierCoefficients
section FourierInversion
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (f : SchwartzMap V ℂ)
end FourierInversion
section TorusTransport
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
variable {d : ℕ} (b : Basis (Fin d) ℤ L)
noncomputable def latticeEquivFun : V ≃L[ℝ] (Fin d → ℝ) :=
  (b.ofZLatticeBasis ℝ L).equivFunL
theorem latticeEquivFun_apply (x : V) (i : Fin d) :
    latticeEquivFun L b x i = (b.ofZLatticeBasis ℝ L).repr x i := by
  simp [latticeEquivFun]
theorem latticeEquivFun_image_lattice :
    latticeEquivFun L b '' (L : Set V)
      = {z : Fin d → ℝ | ∀ i, z i ∈ Set.range ((↑) : ℤ → ℝ)} := by
  ext z
  simp only [Set.mem_image, SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    rw [latticeEquivFun_apply, b.ofZLatticeBasis_repr_apply ℝ L ⟨x, hx⟩ i]
    exact ⟨b.repr ⟨x, hx⟩ i, rfl⟩
  · intro hz
    choose n hn using hz
    refine ⟨(latticeEquivFun L b).symm z, ?_, (latticeEquivFun L b).apply_symm_apply z⟩
    have hsymm : (latticeEquivFun L b).symm z
        = ∑ i, z i • (b.ofZLatticeBasis ℝ L) i := by
      rw [show (latticeEquivFun L b).symm z
            = (b.ofZLatticeBasis ℝ L).equivFun.symm z from rfl,
        Basis.equivFun_symm_apply]
    rw [hsymm]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hn i, Basis.ofZLatticeBasis_apply, Int.cast_smul_eq_zsmul ℝ]
    exact L.smul_mem (n i) (b i).2
noncomputable def latticeEquivFunHom : V →+ (Fin d → ℝ) :=
  (latticeEquivFun L b).toLinearEquiv.toLinearMap.toAddMonoidHom
noncomputable def piCircleHom :
    (Fin d → ℝ) →+ (Fin d → AddCircle (1 : ℝ)) :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).compLeft (Fin d)
noncomputable def toPiCircleHom :
    V →+ (Fin d → AddCircle (1 : ℝ)) :=
  (piCircleHom (d := d)).comp (latticeEquivFunHom L b)
theorem toPiCircleHom_apply (x : V) :
    toPiCircleHom L b x
      = fun i => ((latticeEquivFun L b x i : ℝ) : AddCircle (1 : ℝ)) := rfl
theorem toPiCircleHom_eq_zero_iff (x : V) :
    toPiCircleHom L b x = 0 ↔ x ∈ L.toAddSubgroup := by
  have hcoe : ∀ r : ℝ,
      ((r : AddCircle (1 : ℝ)) = 0 ↔ r ∈ Set.range ((↑) : ℤ → ℝ)) := by
    intro r
    rw [AddCircle.coe_eq_zero_iff]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, by simpa using hn⟩
    · rintro ⟨n, rfl⟩; exact ⟨n, by simp⟩
  rw [toPiCircleHom_apply, funext_iff]
  simp only [Pi.zero_apply, hcoe]
  rw [show (∀ i, latticeEquivFun L b x i ∈ Set.range ((↑) : ℤ → ℝ))
        ↔ latticeEquivFun L b x
            ∈ {z : Fin d → ℝ | ∀ i, z i ∈ Set.range ((↑) : ℤ → ℝ)} from Iff.rfl,
    ← latticeEquivFun_image_lattice L b,
    (latticeEquivFun L b).injective.mem_set_image]
  exact (Submodule.mem_toAddSubgroup L).symm
noncomputable def torusHom :
    (V ⧸ L.toAddSubgroup) →+ (Fin d → AddCircle (1 : ℝ)) :=
  QuotientAddGroup.lift L.toAddSubgroup (toPiCircleHom L b)
    (by intro x hx; rw [AddMonoidHom.mem_ker]; exact (toPiCircleHom_eq_zero_iff L b x).2 hx)
theorem continuous_toPiCircleHom :
    Continuous (toPiCircleHom L b) := by
  refine continuous_pi (fun i => ?_)
  simp only [toPiCircleHom_apply]
  exact QuotientAddGroup.continuous_mk.comp
    ((continuous_apply i).comp (latticeEquivFun L b).continuous)
instance instCompactSpaceTorus :
    CompactSpace (V ⧸ L.toAddSubgroup) := by
  rw [← isCompact_univ_iff]
  have hrange : Set.range ((↑) : V → V ⧸ L.toAddSubgroup) = Set.univ :=
    QuotientAddGroup.range_mk
  rw [← hrange]
  refine IsZLattice.isCompact_range_of_periodic L _ QuotientAddGroup.continuous_mk ?_
  intro z w hw
  rw [QuotientAddGroup.eq]
  have hzw : -(z + w) + z = -w := by abel
  rw [hzw]
  exact (L.toAddSubgroup).neg_mem ((Submodule.mem_toAddSubgroup L).2 hw)
theorem torusHom_bijective : Function.Bijective (torusHom L b) := by
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    induction a using QuotientAddGroup.induction_on with
    | _ x =>
      rw [show torusHom L b (x : V ⧸ L.toAddSubgroup) = toPiCircleHom L b x from rfl] at ha
      exact (QuotientAddGroup.eq_zero_iff (N := L.toAddSubgroup) x).2 ((toPiCircleHom_eq_zero_iff L b x).1 ha)
  · intro t
    choose r hr using fun i => QuotientAddGroup.mk_surjective (t i)
    refine ⟨((latticeEquivFun L b).symm r : V ⧸ L.toAddSubgroup), ?_⟩
    rw [show torusHom L b ((latticeEquivFun L b).symm r : V ⧸ L.toAddSubgroup)
          = toPiCircleHom L b ((latticeEquivFun L b).symm r) from rfl, toPiCircleHom_apply]
    funext i
    rw [(latticeEquivFun L b).apply_symm_apply]
    exact hr i
noncomputable def torusEquiv :
    (V ⧸ L.toAddSubgroup) ≃ₜ+ (Fin d → AddCircle (1 : ℝ)) := by
  let e : (V ⧸ L.toAddSubgroup) ≃+ (Fin d → AddCircle (1 : ℝ)) :=
    AddEquiv.ofBijective (torusHom L b) (torusHom_bijective L b)
  have hcont : Continuous e := by
    rw [← (QuotientAddGroup.isOpenQuotientMap_mk).continuous_comp_iff]
    have hcomp : (e ∘ (QuotientAddGroup.mk : V → V ⧸ L.toAddSubgroup))
        = fun x => toPiCircleHom L b x := by
      funext x; rfl
    rw [hcomp]
    exact continuous_toPiCircleHom L b
  exact ContinuousAddEquiv.mk'
    (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) hcont)
    (fun x y => map_add e x y)
@[simp] theorem torusEquiv_mk (x : V) :
    (torusEquiv L b) (x : V ⧸ L.toAddSubgroup)
      = fun i => ((latticeEquivFun L b x i : ℝ) : AddCircle (1 : ℝ)) := by
  have h : (torusEquiv L b) (x : V ⧸ L.toAddSubgroup) = toPiCircleHom L b x := rfl
  rw [h, toPiCircleHom_apply]
noncomputable def dualBasisR : Basis (Fin d) ℝ V :=
  LinearMap.BilinForm.dualBasis (innerₗ V) innerₗ_nondegenerate (b.ofZLatticeBasis ℝ L)
theorem dualLattice_eq_span_dualBasisR :
    dualLattice L = Submodule.span ℤ (Set.range (dualBasisR L b)) := by
  classical
  have hLspan : L = Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ L)) :=
    (b.ofZLatticeBasis_span ℝ).symm
  change LinearMap.BilinForm.dualSubmodule (innerₗ V) L = _
  exact (congrArg (LinearMap.BilinForm.dualSubmodule (innerₗ V)) hLspan).trans
    (LinearMap.BilinForm.dualSubmodule_span_of_basis _ innerₗ_nondegenerate
      (b.ofZLatticeBasis ℝ L))
theorem dualBasisR_linearIndependent :
    LinearIndependent ℤ (dualBasisR L b) := by
  have hinj : Function.Injective (fun c : ℤ => c • (1 : ℝ)) := by
    intro a c h; simpa using h
  exact (dualBasisR L b).linearIndependent.restrict_scalars hinj
noncomputable def dualLatticeBasis : Basis (Fin d) ℤ (dualLattice L) :=
  (Basis.span (dualBasisR_linearIndependent L b)).map
    (LinearEquiv.ofEq _ _ (dualLattice_eq_span_dualBasisR L b).symm)
noncomputable def dualLatticeEquiv : (dualLattice L) ≃ (Fin d → ℤ) :=
  (dualLatticeBasis L b).equivFun.toEquiv
end TorusTransport
section ProductTorusFourier
open UnitAddTorus ComplexConjugate
noncomputable local instance _p2m_local_instance_c635516111_828 : MeasureSpace (AddCircle (1 : ℝ)) :=
  ⟨AddCircle.haarAddCircle⟩
variable {d : ℕ}
noncomputable def fourierCoeffProd (F : (Fin d → AddCircle (1 : ℝ)) → ℂ)
    (n : Fin d → ℤ) : ℂ :=
  ∫ θ, (∏ i, conj (fourier (n i) (θ i))) • F θ
end ProductTorusFourier
section TorusMeasureTransport
open UnitAddTorus
noncomputable local instance _p2m_local_instance_c635516111_908 : MeasureSpace (AddCircle (1 : ℝ)) :=
  ⟨AddCircle.haarAddCircle⟩
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
variable {d : ℕ} (b : Basis (Fin d) ℤ L)
end TorusMeasureTransport
section FourierInversionAssembly
open UnitAddTorus ComplexConjugate
noncomputable local instance _p2m_local_instance_c635516111_1176 : MeasureSpace (AddCircle (1 : ℝ)) :=
  ⟨AddCircle.haarAddCircle⟩
local instance _p2m_local_instance_c635516111_1182 : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (f : SchwartzMap V ℂ)
end FourierInversionAssembly
end DedekindZeta.PoissonSummation


