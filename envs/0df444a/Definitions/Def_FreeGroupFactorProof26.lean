-- Prove2me | Definitions.Def_FreeGroupFactorProof26
-- name    : FreeGroupFactorProof26
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T04:34:32.112524+00:00
-- url     : https://prove2.me/theorems/b14cc425-fd44-4bd0-b390-4d59cffb21b0
-- title:
--   Free group factors: supporting development, part 26
-- statement:
--   Part 26 of the supporting Lean development for the isomorphism of all interpolated free group factors. It continues the chain of earlier parts and contains proved upstream lemmas on the polynomial flow and on corners of the stabilization, with the declarations they rest on, in source order. No result is assumed.
--
--   **Formalization Note** Eight of these lemmas were first published as child theorems, but the platform's target-type check rejected their universe-polymorphic solutions even though the solution type and the published statement have the same elaborated term locally. They are therefore proved here, so that the parent theorems can use them. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof25

set_option linter.all false

section
namespace OAI

noncomputable section

universe uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain
open scoped ENNReal

variable {G : Type uG} [Group G]

theorem gaugedRepresentation_total (e : G ≃* G) (χ : G →* unitary ℂ) :
    ⊤ ≤ (Submodule.span ℂ (Set.range
      (fun g => groupL2 (gaugedRepresentation e χ g)))).topologicalClosure := by
  classical
  let K := (Submodule.span ℂ (Set.range
    (fun g => groupL2 (gaugedRepresentation e χ g)))).topologicalClosure
  apply group_single_total K (Submodule.isClosed_topologicalClosure _)
  intro g
  have hg : groupL2 (gaugedRepresentation e χ (e.symm g)) ∈ K :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨e.symm g,rfl⟩)
  have hs := K.smul_mem (star (χ (e.symm g) : ℂ)) hg
  simp only [gaugedRepresentation_apply, map_smul, groupL2_groupUnitary,
    e.apply_symm_apply, smul_smul, (χ (e.symm g)).property.1, one_smul] at hs
  exact hs

theorem gaugedIso (e : G ≃* G) (χ : G →* unitary ℂ) :
    ∃ Φ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann G,
      (∀ T, canonicalTrace (Φ T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology G) (groupUltraweakTopology G) Φ ∧
      @Continuous _ _ (groupUltraweakTopology G) (groupUltraweakTopology G) Φ.symm ∧
      ∀ g, Φ (groupUnitary g) = (χ g : ℂ) • groupUnitary (e g) := by
  classical
  obtain ⟨f,hδ,hρ,hVN⟩ := spatial_of_haar_total (gaugedRepresentation e χ)
    (gaugedRepresentation_star e χ) (gaugedRepresentation_trace e χ)
    (gaugedRepresentation_total e χ)
  refine ⟨spatialGroupIso f hVN, ?_, spatialGroupIso_normal f hVN,
    spatialGroupIso_symm_normal f hVN, ?_⟩
  · intro T
    rw [canonicalTrace_eq_inner, canonicalTrace_eq_inner]
    change inner ℂ deltaOne (f ((T : GroupOperator G) (f.symm deltaOne))) =
      inner ℂ deltaOne ((T : GroupOperator G) deltaOne)
    have hf : f.symm deltaOne = deltaOne := f.injective (by simpa only [f.apply_symm_apply] using hδ.symm)
    rw [hf]
    simpa only [hδ] using f.inner_map_map deltaOne ((T : GroupOperator G) deltaOne)
  · intro g
    apply Subtype.ext
    exact hρ g

variable {ι : Type uι}

def nielsenHom (w : FreeGroup ι) : FreeGroup (Option ι) →* FreeGroup (Option ι) :=
  FreeGroup.lift (fun j => j.elim (FreeGroup.of none * FreeGroup.map Option.some w)
    (fun j => FreeGroup.of (some j)))

@[simp] theorem nielsenHom_of_some (w : FreeGroup ι) (j : ι) :
    nielsenHom w (FreeGroup.of (some j)) = FreeGroup.of (some j) := by
  simp [nielsenHom]

@[simp] theorem nielsenHom_of_none (w : FreeGroup ι) :
    nielsenHom w (FreeGroup.of none) = FreeGroup.of none * FreeGroup.map Option.some w := by
  simp [nielsenHom]

@[simp] theorem nielsenHom_map_some (w v : FreeGroup ι) :
    nielsenHom w (FreeGroup.map Option.some v) = FreeGroup.map Option.some v := by
  have he : (nielsenHom w).comp (FreeGroup.map Option.some) = FreeGroup.map Option.some := by
    apply FreeGroup.ext_hom
    intro j
    simp
  exact DFunLike.congr_fun he v

theorem nielsenHom_inv_comp (w : FreeGroup ι) :
    (nielsenHom w⁻¹).comp (nielsenHom w) = MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro j
  cases j <;> simp [mul_assoc]

def nielsenEquiv (w : FreeGroup ι) : FreeGroup (Option ι) ≃* FreeGroup (Option ι) where
  toFun := nielsenHom w
  invFun := nielsenHom w⁻¹
  left_inv g := DFunLike.congr_fun (nielsenHom_inv_comp w) g
  right_inv g := by simpa using DFunLike.congr_fun (nielsenHom_inv_comp w⁻¹) g
  map_mul' := map_mul (nielsenHom w)

theorem gauged_nielsen_iso (w : FreeGroup ι) (z : unitary ℂ) :
    ∃ γ : groupVonNeumann (FreeGroup (Option ι)) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option ι)),
      (∀ T, canonicalTrace (γ T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option ι)))
        (groupUltraweakTopology (FreeGroup (Option ι))) γ ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option ι)))
        (groupUltraweakTopology (FreeGroup (Option ι))) γ.symm ∧
      (∀ j, γ (groupUnitary (FreeGroup.of (some j))) = groupUnitary (FreeGroup.of (some j))) ∧
      γ (groupUnitary (FreeGroup.of none)) =
        (z : ℂ) • (groupUnitary (FreeGroup.of none) * groupUnitary (FreeGroup.map Option.some w)) := by
  let χ : FreeGroup (Option ι) →* unitary ℂ := FreeGroup.lift (fun j => j.elim z (fun _ => 1))
  obtain ⟨γ,ht,hc,hci,hg⟩ := gaugedIso (nielsenEquiv w) χ
  refine ⟨γ,ht,hc,hci,?_,?_⟩
  · intro j
    rw [hg]
    change ((χ (FreeGroup.of (some j)) : unitary ℂ) : ℂ) •
      groupUnitary (nielsenHom w (FreeGroup.of (some j))) = _
    simp only [χ, FreeGroup.lift_apply_of, Option.elim_some, Submonoid.coe_one,
      nielsenHom_of_some, one_smul]
  · rw [hg]
    change ((χ (FreeGroup.of none) : unitary ℂ) : ℂ) •
      groupUnitary (nielsenHom w (FreeGroup.of none)) = _
    simp only [χ, FreeGroup.lift_apply_of, Option.elim_none, nielsenHom_of_none]
    congr 1
    exact Subtype.ext (leftRegular_mul _ _)

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.Generation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

variable {G : Type uG} [Group G]

theorem twoNorm_add_le (x y : groupVonNeumann G) : twoNorm (x+y) ≤ twoNorm x + twoNorm y := by
  change ‖groupL2 (x+y)‖ ≤ _
  rw [map_add]
  exact norm_add_le _ _

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain
open UnitaryEvaluation

theorem trace_symm {G : Type uG} [Group G]
    (γ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann G)
    (ht : ∀ T, canonicalTrace (γ T) = canonicalTrace T) (T : groupVonNeumann G) :
    canonicalTrace (γ.symm T) = canonicalTrace T := by
  simpa only [γ.apply_symm_apply] using (ht (γ.symm T)).symm

theorem norm_symm_sub {A : Type uA} [CStarAlgebra A]
    (γ : A ≃⋆ₐ[ℂ] A) (X Y : A) : ‖γ.symm X - Y‖ = ‖X - γ Y‖ := by
  have he : γ.symm (X - γ Y) = γ.symm X - Y := by simp only [map_sub,γ.symm_apply_apply]
  rw [← he,StarAlgEquiv.norm_map]

theorem twoNorm_symm_sub {G : Type uG} [Group G]
    (γ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann G)
    (ht : ∀ T, canonicalTrace (γ T) = canonicalTrace T) (X Y : groupVonNeumann G) :
    twoNorm (γ.symm X-Y) = twoNorm (X-γ Y) := by
  have he : γ.symm (X-γ Y) = γ.symm X-Y := by simp only [map_sub,γ.symm_apply_apply]
  rw [← he,twoNorm_iso γ.symm (trace_symm γ ht)]

theorem firstCoefficients_norm_le {n : ℕ} (h : Coeff (FreeGroup (Fin n))) (j : Fin n) :
    coefficientNorm (firstCoefficients h j) ≤ coefficientNorm h := by
  unfold firstCoefficients
  split_ifs
  · exact le_rfl
  · simp only [coefficientNorm,Finsupp.sum_zero_index,Real.sqrt_zero]
    exact Real.sqrt_nonneg _

theorem one_step_generator_estimate {G : Type uG} [Group G]
    (β γ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann G)
    (A : groupVonNeumann G) (hγ : γ A = A)
    {K ε c : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (hb : ‖β A-A‖ ≤ 3*K*c) (hc : c < (ε/2)/(3*K)) :
    ‖γ.symm (β A)-A‖ < ε := by
  rw [norm_symm_sub,hγ]
  have hd := (lt_div_iff₀ (by positivity : 0 < 3*K)).mp hc
  nlinarith

theorem one_step_word_estimate {G : Type uG} [Group G]
    (β γ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann G)
    (hγt : ∀ T, canonicalTrace (γ T) = canonicalTrace T)
    (C W : unitary (groupVonNeumann G)) (E : groupVonNeumann G) (z : unitary ℂ)
    (hγC : γ (C : groupVonNeumann G) = (z : ℂ) • ((C : groupVonNeumann G)*(W : groupVonNeumann G)))
    {K ε c : ℝ} (hK : 0 < K)
    (hb : ‖β (W : groupVonNeumann G)-E*(W : groupVonNeumann G)‖ ≤ 3*K*c)
    (hc : c < (ε/2)/(3*K)) (hze : twoNorm (E-(z : ℂ) • (C : groupVonNeumann G)) < ε/2) :
    twoNorm (γ.symm (β (W : groupVonNeumann G))-(C : groupVonNeumann G)) < ε := by
  rw [twoNorm_symm_sub γ hγt,hγC]
  have he : β (W : groupVonNeumann G) - (z : ℂ) • ((C : groupVonNeumann G)*(W : groupVonNeumann G)) =
      (β (W : groupVonNeumann G)-E*(W : groupVonNeumann G)) +
      (E-(z : ℂ) • (C : groupVonNeumann G))*(W : groupVonNeumann G) := by
    simp only [sub_mul,smul_mul_assoc]
    abel
  rw [he]
  have ht := Generation.twoNorm_add_le
    (β (W : groupVonNeumann G)-E*(W : groupVonNeumann G))
    ((E-(z : ℂ) • (C : groupVonNeumann G))*(W : groupVonNeumann G))
  rw [twoNorm_mul_unitary_right] at ht
  have hle := twoNorm_le_norm (β (W : groupVonNeumann G)-E*(W : groupVonNeumann G))
  have hd := (lt_div_iff₀ (by positivity : 0 < 3*K)).mp hc
  nlinarith

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

open scoped ContDiff BigOperators ENNReal
namespace FreeGroupFactorMain
theorem source_laurent_moments_bounded {ι : Type uι} [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (Y : ℝ → (Option ι × Bool) → groupVonNeumann (FreeGroup (Option ι)))
    (hY₀ : ∀ ib, Y 0 ib = groupUnitary (AlgebraPolynomial.signed ib))
    (hsmooth : ∀ ib, ContDiff ℝ ∞ (fun t => Y t ib))
    (hbounded : ∀ t ib, ‖Y t ib‖ ≤ 1)
    (hODE : ∀ t ib, HasDerivAt (fun s => Y s ib)
      (NCPolynomial.eval (Y t)
        (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) ib)) t)
    (J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hdeg : ∀ ib, NCPolynomial.degree (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) ib) ≤ J + 1)
    (hmass : ∀ ib, NCPolynomial.mass (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) ib) ≤ B)
    (p : NCPolynomial.Expr (Option ι × Bool)) (t : ℝ) :
    canonicalTrace (NCPolynomial.eval (Y t) p) =
      canonicalTrace (NCPolynomial.eval (Y 0) p) := by
  classical
  let V := AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l)
  have hinitial (q) : canonicalTrace (NCPolynomial.eval (Y 0) (NCPolynomial.delta V q)) = 0 := by
    have hinit : Y 0 = fun ib => groupUnitary (AlgebraPolynomial.signed ib) := funext hY₀
    rw [hinit, canonicalTrace_eval]
    exact AlgebraPolynomial.encoded_initial_trace h l q
  have hreal (L : ℂ →L[ℝ] ℝ) :
      L (canonicalTrace (NCPolynomial.eval (Y t) p)) =
      L (canonicalTrace (NCPolynomial.eval (Y 0) p)) := by
    let Lt := L.comp ((canonicalTraceCLM (G := FreeGroup (Option ι))).restrictScalars ℝ)
    apply NCPolynomial.polynomial_moments Y V Lt hsmooth hODE 1 le_rfl hbounded
      J B hB hdeg hmass
    intro q
    change L (canonicalTrace (NCPolynomial.eval (Y 0) (NCPolynomial.delta V q))) = 0
    rw [hinitial, map_zero]
  exact Complex.ext (hreal Complex.reCLM) (hreal Complex.imCLM)

end FreeGroupFactorMain
namespace FreeGroupFactorMain.UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain
open scoped ContDiff
open UnitaryEvaluation

end FreeGroupFactorMain

namespace FreeGroupFactorMain.UnitaryEvaluation
open scoped ContDiff
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} {κ : Type uκ}

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain.FiniteActive
open UnitaryEvaluation
open scoped ContDiff
variable {ι : Type uι} {κ : Type uκ}

end FreeGroupFactorMain.FiniteActive

namespace FreeGroupFactorMain
open UnitaryEvaluation
open scoped ENNReal

end FreeGroupFactorMain

end

end OAI
end


