-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TrivSymmApply
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TrivSymmApply
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T22:15:24.179647+00:00
-- url     : https://prove2.me/theorems/1c72e3f1-1658-4a71-a731-bd69265dbe09
-- title:
--   Triv Symm Apply
-- statement:
--   Definitions and structural lemmas for Triv Symm Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FrobeniusReciprocity/TrivSymmApply.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TensInduction
import Theorems.Thm_PositivityTheory_PfBern_Frob_intB_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_rtr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.PfBern.Frob.intB_apply
attribute [local simp] PositivityTheory.PfBern.Frob.rtr_apply


set_option autoImplicit false
noncomputable section
open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil
namespace PositivityTheory.PfBern.Frob
structure Sec {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) where

  s : G ⧸ H → G
  cont : Continuous s
  sec : ∀ c : G ⧸ H, ((s c : G) : G ⧸ H) = c
section Triv
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Subgroup G}
  {X : Type} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {p : X → G ⧸ H}
theorem Sec.inv_smul (σ : Sec H) (c : G ⧸ H) : (σ.s c)⁻¹ • c = ((1 : G) : G ⧸ H) := by
  have hc := σ.sec c
  calc (σ.s c)⁻¹ • c = (σ.s c)⁻¹ • ((σ.s c : G) : G ⧸ H) := by rw [hc]
    _ = ((1 : G) : G ⧸ H) := by rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]
theorem Sec.inv_mul_mem (σ : Sec H) (g : G) : (σ.s (g : G ⧸ H))⁻¹ * g ∈ H := by
  have hg := σ.sec (g : G ⧸ H)
  rwa [QuotientGroup.eq] at hg
variable (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (σ : Sec H)
def zpart (x : X) : Fib p :=
  ⟨(σ.s (p x))⁻¹ • x, by rw [hp]; exact σ.inv_smul (p x)⟩
@[simp]
theorem zpart_val (x : X) : (zpart hp σ x).1 = (σ.s (p x))⁻¹ • x := rfl
include hp in
theorem p_smul_fib (g : G) (z : Fib p) : p (g • z.1) = (g : G ⧸ H) := by
  have hz : p z.1 = ((1 : G) : G ⧸ H) := z.2
  rw [hp, hz, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
variable (hpc : Continuous p)
def triv : X × H ≃ₜ G × Fib p where
  toFun q := (σ.s (p q.1) * q.2, fibSmul hp q.2⁻¹ (zpart hp σ q.1))
  invFun r := (r.1 • r.2.1, ⟨(σ.s (r.1 : G ⧸ H))⁻¹ * r.1, σ.inv_mul_mem r.1⟩)
  left_inv q := by
    obtain ⟨x, h⟩ := q
    have e1 : ((σ.s (p x) * h : G) : G ⧸ H) = p x := by
      rw [QuotientGroup.mk_mul_of_mem _ h.2, σ.sec]
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show (σ.s (p x) * h) • (((h⁻¹ : H) : G) • ((σ.s (p x))⁻¹ • x)) = x
      rw [smul_smul, smul_smul, Subgroup.coe_inv]
      simp [mul_assoc]
    · show (σ.s ((σ.s (p x) * h : G) : G ⧸ H))⁻¹ * (σ.s (p x) * h) = h
      rw [e1, inv_mul_cancel_left]
  right_inv r := by
    obtain ⟨g, z⟩ := r
    have e2 := p_smul_fib hp g z
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show σ.s (p (g • z.1)) * ((σ.s (g : G ⧸ H))⁻¹ * g) = g
      rw [e2, mul_inv_cancel_left]
    · show (((⟨(σ.s (g : G ⧸ H))⁻¹ * g, σ.inv_mul_mem g⟩ : H)⁻¹ : H) : G) •
          ((σ.s (p (g • z.1)))⁻¹ • (g • z.1)) = z.1
      rw [e2, smul_smul, smul_smul, Subgroup.coe_inv]
      simp [mul_assoc]
  continuous_toFun := by
    refine Continuous.prodMk
      ((σ.cont.comp (hpc.comp continuous_fst)).mul (continuous_subtype_val.comp continuous_snd)) ?_
    exact Continuous.subtype_mk ((continuous_subtype_val.comp continuous_snd.inv).smul
      (((σ.cont.comp (hpc.comp continuous_fst)).inv).smul continuous_fst)) _
  continuous_invFun := by
    refine Continuous.prodMk (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) ?_
    exact Continuous.subtype_mk
      (((σ.cont.comp (QuotientGroup.continuous_mk.comp continuous_fst)).inv).mul continuous_fst) _
end Triv
section Fap
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {H : Subgroup G} [LocallyCompactSpace H]
  {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] [MulAction G X] [ContinuousSMul G X]
  {p : X → G ⧸ H} (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (σ : Sec H)
  (hpc : Continuous p) (μH : Measure H) [μH.IsHaarMeasure]
def avg [LocallyCompactSpace (Fib p)] : SB (G × Fib p) →ₗ[ℂ] SB X :=
  intB μH (fun _ => (1 : ℂ)) continuous_const ∘ₗ pullHomeo (triv hp σ hpc)
def fap [LocallyCompactSpace (Fib p)] (α : SB G) (φ : SB (Fib p)) : SB X :=
  avg hp σ hpc μH (tens α φ)
end Fap
end PositivityTheory.PfBern.Frob


