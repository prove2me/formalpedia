-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T02:24:52.193818+00:00
-- url     : https://prove2.me/theorems/214af79f-1ef8-5bc4-a789-09a1014f1505
-- title:
--   Second Countable Topology Arch Unitary
-- statement:
--   Definitions and structural lemmas for Second Countable Topology Arch Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/SecondCountableTopologyArchUnitary.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_MajorantInvolutionDiagonalForm
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
universe u
section Topology
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
instance secondCountableTopology_GL_complex : SecondCountableTopology (GL ι ℂ) := by
  have : SecondCountableTopology (Matrix ι ι ℂ) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → ℂ))
  have : SecondCountableTopology (Matrix ι ι ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology
instance secondCountableTopology_archUnitary (h : HermitianForm F E W) (v : Basis ι E W) :
    SecondCountableTopology (archUnitary h v) := by
  have : SecondCountableTopology (InfinitePlace E → GL ι ℂ) := inferInstance
  exact TopologicalSpace.Subtype.secondCountableTopology _
end Topology
section Groups
variable (G : Type*) [Group G]
def UnfoldOrbit.Statement [MeasurableSpace G] [MeasurableMul G] : Prop :=
  ∀ (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Γ₀ : Subgroup G) [Countable Γ], Γ₀ ≤ Γ →
    ∀ FD FD₀ : Set G, IsFundamentalDomain Γ FD μ → IsFundamentalDomain Γ₀ FD₀ μ →
    ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ γ ∈ Γ₀, ∀ g, φ (γ * g) = φ g) →
    ∫⁻ g in FD, ∑' q : Γ ⧸ Γ₀.subgroupOf Γ, φ (((Quotient.out q : Γ) : G)⁻¹ * g) ∂μ =
      ∫⁻ g in FD₀, φ g ∂μ
def DiscreteFundamentalDomain.Statement [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] : Prop :=
  ∀ (μ : Measure G) (Γ : Subgroup G), DiscreteTopology Γ →
    ∃ FD : Set G, MeasurableSet FD ∧ IsFundamentalDomain Γ FD μ
end Groups
section Numbers
variable (E : Type*) [Field E] [NumberField E]
def IdealClassesFinite.Statement : Prop :=
  ∃ T : Set (AddSubgroup E), T.Finite ∧ ∀ I : AddSubgroup E, I.FG → I ≠ ⊥ →
    (∀ a : 𝓞 E, ∀ x ∈ I, (a : E) * x ∈ I) →
    ∃ J ∈ T, ∃ c : E, c ≠ 0 ∧ I = J.map (AddMonoidHom.mulLeft c)
def IntegralFamilyBound.Statement : Prop :=
  ∃ r : ℝ, ∃ a : Fin (finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (a i : E)) ∧
    ∀ i (σ : E →+* ℂ), ‖σ (a i)‖ ≤ r
end Numbers
section Spaces
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def MajorantExists.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  Nonempty (Majorant h v)
def WittPartner.Statement (h : HermitianForm F E W) : Prop :=
  ∀ x₀ : W, x₀ ≠ 0 → h.toSesq x₀ x₀ = 0 → ∃ w₀ : W, h.toSesq x₀ w₀ = 1 ∧ h.toSesq w₀ w₀ = 0
def VectorOrbitsFinite.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (VV : Set W), IsDIntegral h D La → VV ⊆ La →
    (∀ x ∈ VV, x ≠ 0 ∧ h.toSesq x x = 0) → (∀ γ ∈ latticeStab h La, ∀ x ∈ VV, γ • x ∈ VV) →
    (∃ C : ℕ, ∀ x ∈ VV, lineIndex E La x ≤ C) →
    ∃ S : Finset W, (S : Set W) ⊆ VV ∧ ∀ x ∈ VV, ∃ y ∈ S, ∃ γ ∈ latticeStab h La, γ • y = x
def ArchLatticeDiscrete.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ La : AddSubgroup W, IsLattice E La → DiscreteTopology (archLatticeGroup h v La)
variable (F E)
def CovolumeFiniteBelow (N : ℕ) : Prop :=
  ∀ (W' : Type u) [AddCommGroup W'] [Module E W'] [FiniteDimensional E W']
    (h' : HermitianForm F E W') (n : ℕ) (v' : Basis (Fin n) E W'),
    finrank E W' < N → ArithmeticCovolumeFinite.Statement h' v'
def LatticeOrbitsFiniteBelow (N : ℕ) : Prop :=
  ∀ (W' : Type u) [AddCommGroup W'] [Module E W'] [FiniteDimensional E W']
    (h' : HermitianForm F E W'), finrank E W' < N → LatticeOrbitsFinite.Statement h'
end Spaces
section Inhabitants
open GaussianPlane
abbrev C2 : Type := Multiplicative (ZMod 2)
instance : MeasurableSpace C2 := ⊤
instance : MeasurableMul C2 := ⟨fun _ => measurable_from_top, fun _ => measurable_from_top⟩
instance : (Measure.count : Measure C2).IsMulLeftInvariant :=
  ⟨fun g => by
    ext s hs
    rw [Measure.map_apply (measurable_from_top) hs]
    have he : (fun x : C2 => g * x) ⁻¹' s = (fun x => g⁻¹ * x) '' s := by
      ext x
      simp
    rw [he, Measure.count_apply MeasurableSpace.measurableSet_top, Measure.count_apply hs]
    exact congrArg _ ((mul_right_injective (g⁻¹ : C2)).injOn.encard_image)⟩
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


