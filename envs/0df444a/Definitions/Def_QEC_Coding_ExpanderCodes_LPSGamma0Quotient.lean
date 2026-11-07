-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Quotient
-- name    : QEC_Coding_ExpanderCodes_LPSGamma0Quotient
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:49:42.902209+00:00
-- url     : https://prove2.me/theorems/2214ede3-08b5-4a38-ae7a-21327056c659
-- title:
--   LPSGamma0 Quotient
-- statement:
--   Definitions and structural lemmas for LPSGamma0 Quotient, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0Quotient.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Stabilizers
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Mathlib.Geometry.Manifold.Instances.Quotient
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_fixed_mapGL

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Matrix Filter Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section
def lpsGamma0Projective (N : ℕ) : Subgroup PGL(2,ℝ) :=
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).map Matrix.ProjGenLinGroup.mk
lemma lpsGamma0_projective_orbit_iff (N : ℕ) (τ σ : ℍ) :
    τ∈MulAction.orbit (lpsGamma0Projective N) σ ↔
      τ∈MulAction.orbit (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) σ := by
  constructor
  · rintro ⟨g,hg⟩
    obtain ⟨γ,hγ,he⟩ := g.property
    refine ⟨⟨γ,hγ⟩,?_⟩
    change γ • σ=τ
    change g.val • σ=τ at hg
    simpa only [←he,UpperHalfPlane.pglMk_smul] using hg
  · rintro ⟨g,hg⟩
    refine ⟨⟨Matrix.ProjGenLinGroup.mk g.val,⟨g.val,g.property,rfl⟩⟩,?_⟩
    change Matrix.ProjGenLinGroup.mk g.val • σ=τ
    change g.val • σ=τ at hg
    simpa only [UpperHalfPlane.pglMk_smul] using hg
lemma lpsGamma0Projective_isCancelSMul (N : ℕ) (hN : 4∣N) :
    IsCancelSMul (lpsGamma0Projective N) ℍ := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g τ hfix
  obtain ⟨γ,hγ,he⟩ := g.property
  obtain ⟨δ,hδ,hd⟩ := hγ
  change g.val • τ=τ at hfix
  rw [←he,UpperHalfPlane.pglMk_smul,←hd] at hfix
  apply Subtype.ext
  change g.val=1
  rcases lpsGamma0_fixed_mapGL N hN δ hδ τ hfix with hp|hm
  · rw [←he,←hd,hp,Matrix.ProjGenLinGroup.mk_one]
  · rw [←he,←hd,hm]
    apply Matrix.ProjGenLinGroup.mk_eq_one.mpr
    apply UpperHalfPlane.forall_smul_eq_self_iff_mem_center.mp
    intro z
    simp only [UpperHalfPlane.neg_smul,one_smul]
instance lpsGamma0Projective_continuous (N : ℕ) :
    ContinuousConstSMul (lpsGamma0Projective N) ℍ where
  continuous_const_smul g := by
    obtain ⟨γ,hγ,he⟩ := g.property
    change Continuous (fun τ : ℍ => g.val • τ)
    rw [←he]
    simpa only [UpperHalfPlane.pglMk_smul] using
      (continuous_const_smul γ : Continuous (fun τ : ℍ => γ • τ))
instance lpsGamma0Projective_proper (N : ℕ) [NeZero N] :
    ProperlyDiscontinuousSMul (lpsGamma0Projective N) ℍ := by
  rw [Subgroup.properlyDiscontinuousSMul_iff]
  intro K L hK hL
  have hp : ProperlyDiscontinuousSMul
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ := inferInstance
  rw [Subgroup.properlyDiscontinuousSMul_iff] at hp
  refine ((hp hK hL).image Matrix.ProjGenLinGroup.mk).subset ?_
  rintro g ⟨hg,hgKL⟩
  obtain ⟨γ,hγ,he⟩ := hg
  refine ⟨γ,⟨hγ,?_⟩,he⟩
  rw [←he] at hgKL
  change (((fun τ : ℍ => Matrix.ProjGenLinGroup.mk γ • τ) '' K)∩L).Nonempty at hgKL
  change (((fun τ : ℍ => γ • τ) '' K)∩L).Nonempty
  simpa only [UpperHalfPlane.pglMk_smul] using hgKL
lemma lpsGamma0_quotientCover (N : ℕ) [NeZero N] (hN : 4∣N) :
    IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ))
      (lpsGamma0Projective N) := by
  let := lpsGamma0Projective_isCancelSMul N hN
  exact isQuotientMap_quotient_mk'.isQuotientCoveringMap_of_properlyDiscontinuousSMul
    (fun {τ σ} => Quotient.eq''.trans (lpsGamma0_projective_orbit_iff N τ σ).symm)
lemma lpsGamma0_quotient_localHomeomorph (N : ℕ) [NeZero N] (hN : 4∣N) :
    IsLocalHomeomorph
      (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)) :=
  (lpsGamma0_quotientCover N hN).isCoveringMap.isLocalHomeomorph
@[instance_reducible]
def lpsGamma0QuotientChartedSpace (N : ℕ) [NeZero N] (hN : 4∣N) :
    ChartedSpace ℂ (MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :=
  (lpsGamma0_quotient_localHomeomorph N hN).chartedSpace Quotient.mk_surjective
end
end QEC.Coding.TannerLiftedProduct


