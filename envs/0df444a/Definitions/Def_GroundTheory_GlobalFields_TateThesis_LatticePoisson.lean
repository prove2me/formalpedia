-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
-- name    : GroundTheory_GlobalFields_TateThesis_LatticePoisson
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:18:39.242834+00:00
-- url     : https://prove2.me/theorems/039bfa55-3be0-4f89-a9a3-d8a1db717af1
-- title:
--   Lattice Poisson
-- statement:
--   Definitions and structural lemmas for Lattice Poisson, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Theorems.Thm_GroundTheory_Global_continuous_tsum_comp_add
import Theorems.Thm_GroundTheory_Global_mem_dualLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open MeasureTheory Module Set Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace LatticePoisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)
def dualB : Basis ι ℝ E :=
  LinearMap.BilinForm.dualBasis (innerₗ E) innerₗ_nondegenerate (b.ofZLatticeBasis ℝ L)
theorem inner_dualB (i j : ι) :
    ⟪dualB b i, b.ofZLatticeBasis ℝ L j⟫ = if j = i then 1 else 0 :=
  LinearMap.BilinForm.apply_dualBasis_left innerₗ_nondegenerate _ i j
def dualPt (m : ι → ℤ) : E := ∑ i, (m i : ℝ) • dualB b i
theorem inner_dualPt_basis (m : ι → ℤ) (j : ι) :
    ⟪dualPt b m, b.ofZLatticeBasis ℝ L j⟫ = m j := by
  simp only [dualPt, sum_inner, real_inner_smul_left, inner_dualB, mul_ite, mul_one, mul_zero]
  simp
theorem inner_dualPt_mem (m : ι → ℤ) (ℓ : L) :
    ⟪dualPt b m, (ℓ : E)⟫ = ((∑ i, m i * b.repr ℓ i : ℤ) : ℝ) := by
  conv_lhs => rw [← (b.ofZLatticeBasis ℝ L).sum_repr (ℓ : E)]
  rw [inner_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right, inner_dualPt_basis, Basis.ofZLatticeBasis_repr_apply ℝ L b ℓ i]
  ring
theorem dualPt_mem (m : ι → ℤ) : dualPt b m ∈ dualLattice L :=
  mem_dualLattice.mpr fun ℓ hℓ => ⟨_, inner_dualPt_mem b m ⟨ℓ, hℓ⟩⟩
omit [Fintype ι] [DecidableEq ι] in
theorem basis_mem (j : ι) : b.ofZLatticeBasis ℝ L j ∈ L := by
  rw [Basis.ofZLatticeBasis_apply ℝ L b j]; exact (b j).2
def dualEquiv : (ι → ℤ) ≃ dualLattice L :=
  Equiv.ofBijective (fun m => ⟨dualPt b m, dualPt_mem b m⟩) ⟨fun m m' h => by
      funext j
      have : ⟪dualPt b m, b.ofZLatticeBasis ℝ L j⟫ = ⟪dualPt b m', b.ofZLatticeBasis ℝ L j⟫ :=
        congrArg (fun v : dualLattice L => ⟪(v : E), b.ofZLatticeBasis ℝ L j⟫) h
      rw [inner_dualPt_basis, inner_dualPt_basis] at this
      exact_mod_cast this,
    fun μ => by
      have hμ := mem_dualLattice.mp μ.2
      choose m hm using fun j => hμ _ (basis_mem b j)
      refine ⟨m, Subtype.ext ?_⟩
      change dualPt b m = (μ : E)
      conv_rhs => rw [← (dualB b).sum_repr (μ : E)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [dualB, LinearMap.BilinForm.dualBasis_repr_apply, innerₗ_apply_apply, hm]⟩
def toTorus : C(ι → ℝ, UnitAddTorus ι) :=
  ⟨fun x i => (x i : UnitAddCircle),
    continuous_pi fun i => continuous_quotient_mk'.comp (continuous_apply i)⟩
omit [Fintype ι] [DecidableEq ι] in
theorem isQuotientMap_toTorus : Topology.IsQuotientMap (toTorus (ι := ι)) :=
  (IsOpenQuotientMap.piMap (A := fun _ : ι => ℝ) (B := fun _ => UnitAddCircle)
    fun _ => QuotientAddGroup.isOpenQuotientMap_mk).isQuotientMap
def per (L : Submodule ℤ E) (f : 𝓢(E, ℂ)) (x : E) : ℂ := ∑' ℓ : L, f (x + ℓ)
omit [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L] [Fintype ι] [DecidableEq ι] in
theorem per_add (f : 𝓢(E, ℂ)) (x : E) {v : E} (hv : v ∈ L) : per L f (x + v) = per L f x := by
  unfold per
  rw [← (Equiv.addLeft (⟨v, hv⟩ : L)).tsum_eq (fun ℓ : L => f (x + ℓ))]
  simp [add_assoc]
def perCoord (f : 𝓢(E, ℂ)) : C(ι → ℝ, ℂ) :=
  ⟨fun x => per L f ((b.ofZLatticeBasis ℝ L).equivFun.symm x),
    (continuous_tsum_comp_add L f).comp (LinearMap.continuous_of_finiteDimensional _)⟩
omit [DecidableEq ι] in
theorem perCoord_factorsThrough (f : 𝓢(E, ℂ)) :
    Function.FactorsThrough (perCoord b f) (toTorus (ι := ι)) := by
  intro x y hxy
  have hk : ∀ i, ∃ k : ℤ, y i = x i + k := by
    intro i
    have hi : ((x i : ℝ) : UnitAddCircle) = (y i : UnitAddCircle) := congrFun hxy i
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp hi)
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    linarith
  choose k hk using hk
  have hy : y = x + fun i => (k i : ℝ) := funext fun i => by simp [hk]
  have hmem : (b.ofZLatticeBasis ℝ L).equivFun.symm (fun i => (k i : ℝ)) ∈ L := by
    rw [Basis.equivFun_symm_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact zsmul_mem (basis_mem b i) _
  change per L f ((b.ofZLatticeBasis ℝ L).equivFun.symm x) =
    per L f ((b.ofZLatticeBasis ℝ L).equivFun.symm y)
  rw [hy, LinearEquiv.map_add]
  exact (per_add f _ hmem).symm
def perTorus (f : 𝓢(E, ℂ)) : C(UnitAddTorus ι, ℂ) :=
  isQuotientMap_toTorus.lift (perCoord b f) (perCoord_factorsThrough b f)
variable [MeasurableSpace E] [BorelSpace E]
end LatticePoisson
section Main
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
end Main
end
end GroundTheory.Global


