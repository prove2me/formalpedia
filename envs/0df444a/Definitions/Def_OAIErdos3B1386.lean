-- Prove2me | Definitions.Def_OAIErdos3B1386
-- name    : OAIErdos3B1386
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T05:05:42.459454+00:00
-- url     : https://prove2.me/theorems/a5461244-dea5-4b6b-8613-d535e2cbacdf
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1387 of 1399
-- statement:
--   Definitions bundle 1387 of 1399 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1385`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1387 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.allocatedCoveredProfileDensity_measurable`, `OAI.Erdos3.VectorPolynomial.allocatedFixedPathSlicedPerturbation_chosen_tail`, `OAI.Erdos3.VectorPolynomial.allocatedFixedPathSlicedPerturbation_tail_of_inputCount`, `OAI.Erdos3.VectorPolynomial.allocatedFixedPathSlicedPerturbation_tail_uniform`, `OAI.Erdos3.VectorPolynomial.allocatedKernelSiteMask_bound`, `OAI.Erdos3.VectorPolynomial.allocatedLongJetMask_measurable`, `OAI.Erdos3.VectorPolynomial.allocatedLongJetMask_product_bound`, `OAI.Erdos3.VectorPolynomial.allocatedLongJetRealCoordinates_measurable`, `OAI.Erdos3.VectorPolynomial.allocatedLongProfileDensity_measurable`, `OAI.Erdos3.VectorPolynomial.allocatedMaskedTiltedConstant_ge_two`, `OAI.Erdos3.VectorPolynomial.allocatedProgressionCoveredIntegrand_integrable`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDeckSample_jet_measurable`, `OAI.Erdos3.complex_model_l1_le_of_bounded_tests`, `OAI.Erdos3.density_l1_triangle_bound_reverse`, `OAI.Erdos3.density_l1_triangle_le`, `OAI.Erdos3.finite_residue_error_common_gap_budget`, `OAI.Erdos3.finite_residue_error_le_of_common_gap`, `OAI.Erdos3.fixedPathSliceWidth_budget`, `OAI.Erdos3.fixedPathSliceWidth_lower`, `OAI.Erdos3.fixedPathSlicedGridMesh_scalar_of_floor`, `OAI.Erdos3.fixedPathSlicedPerturbation_tail`, `OAI.Erdos3.fixedPathSlicedSourceErrorBudget_of_floor`, `OAI.Erdos3.fixedPathSlicedSourceError_absorb`, `OAI.Erdos3.fixedPathSlicedSourceError_absorb_sharp`, `OAI.Erdos3.fixedPathSlicedSourceError_eq`, `OAI.Erdos3.fixedPathSlicedSourceError_le_prefactor`, `OAI.Erdos3.physicalBadProductAccuracy_inv`, `OAI.Erdos3.physicalBadProductAccuracy_pos`, `OAI.Erdos3.physicalBadProductGap_exp_bound`, `OAI.Erdos3.selectedColumn_sum`, `OAI.Erdos3.slicedEndpointUniformScale_exp_lower`, `OAI.Erdos3.slicedEndpointUniformScale_exp_tail_tolerance`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B145
import Definitions.Def_OAIErdos3B176
import Definitions.Def_OAIErdos3B1385

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FixedPathSlicedSourceErrorScalar
namespace OAI

section

namespace Erdos3

theorem fixedPathSlicedSourceError_eq (rP rG C K Kφ ε η ξ : ℝ) :
    fixedPathSlicedSourceError rP rG C K Kφ ε η ξ =
      (1 + 4 * C + 4 * K) * rP + (1 + 4 * C + 3 * Kφ) * rG +
        (2 * K) * ε + 2 * η + Kφ * ξ := by
  unfold fixedPathSlicedSourceError
  ring

theorem fixedPathSlicedSourceError_le_prefactor {P rP rG C K Kφ ε η ξ : ℝ}
    (hP : 0 ≤ P) (hC : C ≤ Real.exp P) (hK : K ≤ Real.exp P) (hφ : Kφ ≤ Real.exp P)
    (hrP : 0 ≤ rP) (hrG : 0 ≤ rG) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hξ : 0 ≤ ξ) :
    fixedPathSlicedSourceError rP rG C K Kφ ε η ξ ≤
      Real.exp (P + 4) * (rP + rG + ε + η + ξ) := by
  have hone : (1 : ℝ) ≤ Real.exp P := Real.one_le_exp hP
  have hnine : (9 : ℝ) ≤ Real.exp 4 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)
    norm_num at h
    linarith
  have hbudget : 9 * Real.exp P ≤ Real.exp (P + 4) := by
    rw [Real.exp_add]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hnine (Real.exp_nonneg P)
  have hp : 1 + 4 * C + 4 * K ≤ Real.exp (P + 4) :=
    (show 1 + 4 * C + 4 * K ≤ 9 * Real.exp P by linarith).trans hbudget
  have hg : 1 + 4 * C + 3 * Kφ ≤ Real.exp (P + 4) :=
    (show 1 + 4 * C + 3 * Kφ ≤ 9 * Real.exp P by linarith).trans hbudget
  have he : 2 * K ≤ Real.exp (P + 4) :=
    (show 2 * K ≤ 9 * Real.exp P by linarith).trans hbudget
  have hh : (2 : ℝ) ≤ Real.exp (P + 4) :=
    (show (2 : ℝ) ≤ 9 * Real.exp P by linarith).trans hbudget
  have hx : Kφ ≤ Real.exp (P + 4) :=
    (show Kφ ≤ 9 * Real.exp P by linarith).trans hbudget
  rw [fixedPathSlicedSourceError_eq]
  calc
    _ ≤ Real.exp (P + 4) * rP + Real.exp (P + 4) * rG +
        Real.exp (P + 4) * ε + Real.exp (P + 4) * η + Real.exp (P + 4) * ξ :=
      add_le_add (add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hp hrP) (mul_le_mul_of_nonneg_right hg hrG))
        (mul_le_mul_of_nonneg_right he hε)) (mul_le_mul_of_nonneg_right hh hη))
        (mul_le_mul_of_nonneg_right hx hξ)
    _ = _ := by ring

theorem fixedPathSlicedSourceError_absorb_sharp {P E rP rG C K Kφ ε η ξ : ℝ}
    (hP : 0 ≤ P) (hC : C ≤ Real.exp P) (hK : K ≤ Real.exp P) (hφ : Kφ ≤ Real.exp P)
    (hrP : 0 ≤ rP) (hrG : 0 ≤ rG) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hξ : 0 ≤ ξ)
    (hrPs : rP ≤ Real.exp (-(P + E + 7)))
    (hrGs : rG ≤ Real.exp (-(P + E + 7)))
    (hεs : ε ≤ Real.exp (-(P + E + 7)))
    (hηs : η ≤ Real.exp (-(P + E + 7)))
    (hξs : ξ ≤ Real.exp (-(P + E + 7))) :
    fixedPathSlicedSourceError rP rG C K Kφ ε η ξ ≤ Real.exp (-E) := by
  have hpre := fixedPathSlicedSourceError_le_prefactor hP hC hK hφ hrP hrG hε hη hξ
  have hsum : rP + rG + ε + η + ξ ≤ 5 * Real.exp (-(P + E + 7)) := by linarith
  have hfive : (5 : ℝ) ≤ Real.exp 3 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)
    norm_num at h
    linarith
  calc
    _ ≤ Real.exp (P + 4) * (5 * Real.exp (-(P + E + 7))) :=
      hpre.trans (mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _))
    _ = 5 * Real.exp (-(E + 3)) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp 3 * Real.exp (-(E + 3)) :=
      mul_le_mul_of_nonneg_right hfive (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem fixedPathSlicedSourceError_absorb {P E rP rG C K Kφ ε η ξ : ℝ}
    (hP : 0 ≤ P) (_hE : 0 ≤ E) (_hC0 : 0 ≤ C) (_hK0 : 0 ≤ K) (_hKφ0 : 0 ≤ Kφ)
    (hCP : C ≤ Real.exp P) (hKP : K ≤ Real.exp P) (hKφP : Kφ ≤ Real.exp P)
    (hrP : 0 ≤ rP) (hrG : 0 ≤ rG) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hξ : 0 ≤ ξ)
    (hrPs : rP ≤ Real.exp (-(P + E + 12)))
    (hrGs : rG ≤ Real.exp (-(P + E + 12)))
    (hεs : ε ≤ Real.exp (-(P + E + 12)))
    (hηs : η ≤ Real.exp (-(P + E + 12)))
    (hξs : ξ ≤ Real.exp (-(P + E + 12))) :
    fixedPathSlicedSourceError rP rG C K Kφ ε η ξ ≤ Real.exp (-E) := by
  have hbudget : Real.exp (-(P + E + 12)) ≤ Real.exp (-(P + E + 7)) :=
    Real.exp_le_exp.mpr (by linarith)
  exact fixedPathSlicedSourceError_absorb_sharp hP hCP hKP hKφP hrP hrG hε hη hξ
    (hrPs.trans hbudget) (hrGs.trans hbudget) (hεs.trans hbudget)
    (hηs.trans hbudget) (hξs.trans hbudget)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedUniformTailTolerance
namespace OAI

section

namespace Erdos3

theorem slicedEndpointUniformScale_exp_lower (N O m : ℕ)
    {a δ A η P : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) (hP : 0 ≤ P)
    (hN : (N : ℝ) + 1 ≤ Real.exp P) (hO : (O : ℝ) ≤ Real.exp P) (hm : (m : ℝ) ≤ Real.exp P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hAP : A ≤ Real.exp P) (hηP : η⁻¹ ≤ Real.exp P) :
    Real.exp (-(48 * ((3 * P + 4) * m + 5 * P + 10) + 2 * P + 2 * m + 47)) ≤
      slicedPolynomialScale N O N m m 1 1 a δ A η := by
  have hpos := (slicedEndpointUniformScale_spec N O m ha hδ hA hη).1
  have hinv := slicedEndpointUniformScale_inverse_le_exp N O m
    ha hδ hA hη hP hN hO hm haP hδP hAP hηP
  have h := one_div_le_one_div_of_le (inv_pos.mpr hpos) hinv
  simpa only [one_div, inv_inv, ← Real.exp_neg] using h

theorem slicedEndpointUniformScale_exp_tail_tolerance (N O m : ℕ)
    {a δ A η P : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) (hP : 0 ≤ P)
    (hN : (N : ℝ) + 1 ≤ Real.exp P) (hO : (O : ℝ) ≤ Real.exp P) (hm : (m : ℝ) ≤ Real.exp P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hAP : A ≤ Real.exp P) (hηP : η⁻¹ ≤ Real.exp P)
    (N' O' : ℕ) (hN' : N' ≤ N) (hO' : O' ≤ O) :
    Real.exp (-(48 * ((3 * P + 4) * m + 5 * P + 10) + 2 * P + 2 * m + 47)) *
        polynomialMassC2Budget N' m 1 ≤
      slicedPrincipalC2Tolerance N' O' m 1 a δ A η := by
  have hs := slicedEndpointUniformScale_exp_lower N O m
    ha hδ hA hη hP hN hO hm haP hδP hAP hηP
  have h := (slicedEndpointUniformScale_spec N O m ha hδ hA hη).2.2 N' O' hN' hO'
    (Real.exp (-(48 * ((3 * P + 4) * m + 5 * P + 10) + 2 * P + 2 * m + 47)))
    (by simpa only [abs_of_pos (Real.exp_pos _)] using hs)
  simpa only [abs_of_pos (Real.exp_pos _)] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedSourceErrorBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal Classical

theorem fixedPathSlicedPerturbation_tail
    (N O m : ℕ) {D P Pslice E a δ A η : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hPslice : 0 ≤ Pslice) (hE : 0 ≤ E)
    (hN : (N : ℝ) ≤ D) (hO : (O : ℝ) ≤ D)
    (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp Pslice)
    (hAP : A ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E)
    {N' O' : ℕ} (hNN : N' ≤ N) (hOO : O' ≤ O) {t : ℝ}
    (ht : |t| ≤ Real.exp (-fixedPathSlicedPerturbationLog D P Pslice E m)) :
    |t| * polynomialMassC2Budget N' m 1 ≤
      slicedPrincipalC2Tolerance N' O' m 1 a δ A η := by
  let Q := D + (P + Pslice) + E + m + 2
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hDQ : D ≤ Q := by dsimp only [Q]; linarith
  have hPQ : P ≤ Q := by dsimp only [Q]; linarith
  have hsQ : Pslice ≤ Q := by dsimp only [Q]; linarith
  have hEQ : E ≤ Q := by dsimp only [Q]; linarith
  have hmQ : (m : ℝ) ≤ Q := by dsimp only [Q]; linarith
  have hNQ : (N : ℝ) + 1 ≤ Real.exp Q :=
    ((show (N : ℝ) + 1 ≤ D + 1 by linarith).trans
      (Real.add_one_le_exp D)).trans (Real.exp_le_exp.mpr hDQ)
  have hOQ : (O : ℝ) ≤ Real.exp Q :=
    hO.trans ((by linarith [Real.add_one_le_exp D] : D ≤ Real.exp D).trans
      (Real.exp_le_exp.mpr hDQ))
  have hmexp : (m : ℝ) ≤ Real.exp Q :=
    (by linarith [Real.add_one_le_exp (m : ℝ)] : (m : ℝ) ≤ Real.exp m).trans
      (Real.exp_le_exp.mpr hmQ)
  have he := slicedEndpointUniformScale_exp_tail_tolerance N O m ha hδ hA hη hQ
    hNQ hOQ hmexp (haP.trans (Real.exp_le_exp.mpr hPQ))
    (hδP.trans (Real.exp_le_exp.mpr hsQ)) (hAP.trans (Real.exp_le_exp.mpr hPQ))
    (hηE.trans (Real.exp_le_exp.mpr hEQ)) N' O' hNN hOO
  have hmass : 0 ≤ polynomialMassC2Budget N' m 1 := by unfold polynomialMassC2Budget; positivity
  exact (mul_le_mul_of_nonneg_right ht hmass).trans
    (by simpa only [fixedPathSlicedPerturbationLog, fixedPathPerturbationLog, Q] using he)

theorem fixedPathSliceWidth_budget {cost : ℝ} (hcost : 0 ≤ cost) :
    0 < Real.exp (-cost) / 2 ∧ Real.exp (-cost) / 2 ≤ 1 ∧
      (Real.exp (-cost) / 2)⁻¹ ≤ Real.exp (cost + 1) := by
  have he : Real.exp (-cost) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hcost)
  refine ⟨by positivity, by linarith, ?_⟩
  rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg, Real.exp_add]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  exact (mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg cost)).trans_eq (mul_comm _ _)

theorem fixedPathSliceWidth_lower {cost : ℝ} {S step H : ℕ}
    (hS : 0 < S) (hstep : 0 < step) (hH : 2 ≤ H)
    (hdense : Real.exp (-cost) * S ≤ (H : ℝ)) :
    Real.exp (-cost) / 2 ≤ (step : ℝ) * ((H : ℝ) - 1) / S := by
  have hSr : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  have hHr : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hstepr : (1 : ℝ) ≤ step := by exact_mod_cast hstep
  apply (le_div_iff₀ hSr).mpr
  calc
    Real.exp (-cost) / 2 * S = (Real.exp (-cost) * S) / 2 := by ring
    _ ≤ (H : ℝ) / 2 := div_le_div_of_nonneg_right hdense (by norm_num)
    _ ≤ (H : ℝ) - 1 := by linarith
    _ ≤ (step : ℝ) * ((H : ℝ) - 1) :=
      le_mul_of_one_le_left (by linarith) hstepr

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem allocatedFixedPathSlicedPerturbation_tail_uniform
    {D P Pslice E δ η : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hPslice : 0 ≤ Pslice) (hE : 0 ≤ E)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hAxis : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (A : ℝ≥0) (hδ : 0 < δ) (hη : 0 < η)
    (haP : (unitProfilePrincipalLowerBound B)⁻¹ ≤ Real.exp P)
    (hδP : δ⁻¹ ≤ Real.exp Pslice) (hAP : (A : ℝ) ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E)
    {t : ℝ} (ht : |t| ≤ Real.exp (-fixedPathSlicedPerturbationLog D P Pslice E m))
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ) :
    let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
    let inputs := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)
    |t| * polynomialMassC2Budget (Fintype.card inputs) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card inputs) (Fintype.card {a // active a})
        m 1 (unitProfilePrincipalLowerBound B) δ A η := by
  intro active inputs
  exact fixedPathSlicedPerturbation_tail
    (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)))
    (Fintype.card (LayerSamplerAxis I n)) m hD hP hPslice hE hInput hAxis
    (unitProfilePrincipalLowerBound_pos B) hδ A.coe_nonneg hη haP hδP hAP hηE
    (allocatedOriginalSampleLiftInput_card_le_allAxis B U basis S)
    (Fintype.card_subtype_le _) ht

theorem allocatedFixedPathSlicedPerturbation_tail_of_inputCount
    {D P cost E η : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hcost : 0 ≤ cost) (hE : 0 ≤ E)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hAxis : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (A : ℝ≥0) (hη : 0 < η) (hAP : (A : ℝ) ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E)
    {t : ℝ}
    (ht : |t| ≤ Real.exp (-fixedPathSlicedPerturbationLog D (D + P + 4) (cost + 1) E m))
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ) :
    let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
    let inputs := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)
    |t| * polynomialMassC2Budget (Fintype.card inputs) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card inputs) (Fintype.card {a // active a})
        m 1 (unitProfilePrincipalLowerBound B) (Real.exp (-cost) / 2) A η := by
  exact allocatedFixedPathSlicedPerturbation_tail_uniform B U basis hD (by positivity)
    (by positivity) hE hInput hAxis A (fixedPathSliceWidth_budget hcost).1 hη
    ((allocatedUnitProfilePrincipalLowerBound_inv_le_exp B hInput).trans
      (Real.exp_le_exp.mpr (by linarith)))
    (fixedPathSliceWidth_budget hcost).2.2
    (hAP.trans (Real.exp_le_exp.mpr (by linarith))) hηE ht S

theorem allocatedFixedPathSlicedPerturbation_chosen_tail
    {D P cost E η : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hcost : 0 ≤ cost) (hE : 0 ≤ E)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hAxis : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (A : ℝ≥0) (hη : 0 < η) (hAP : (A : ℝ) ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E) :
    let Qσ := fixedPathSlicedPerturbationLog D (D + P + 4) (cost + 1) E m
    let t := Real.exp (-Qσ)
    0 < t ∧ t ≤ 1 ∧ ∀ {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ),
    let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
    let inputs := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)
    |t| * polynomialMassC2Budget (Fintype.card inputs) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card inputs) (Fintype.card {a // active a})
        m 1 (unitProfilePrincipalLowerBound B) (Real.exp (-cost) / 2) A η := by
  intro Qσ t
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr
    (fixedPathSlicedPerturbationLog_nonneg hD (by positivity) (by positivity) hE m)), ?_⟩
  intro R σ S
  exact allocatedFixedPathSlicedPerturbation_tail_of_inputCount B U basis hD hP hcost hE
    hInput hAxis A hη hAP hηE (by rw [abs_of_pos (Real.exp_pos _)]) S

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem fixedPathSlicedGridMesh_scalar_of_floor {D C V cost E : ℝ} {q S : ℕ}
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hq0 : 0 < q) (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : fixedPathSlicedGridMeshFloor D C V cost E ≤ S) :
    2 * Real.exp cost / S ≤ Real.exp (-E) := by
  have hS := (fixedPathSlicedGridMeshFloor_pos D C V cost E).trans_le hfloor
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have hr : 0 ≤ Real.exp cost * ((q : ℝ) / S) := by positivity
  calc
    _ ≤ 2 * (Real.exp cost * ((q : ℝ) / S)) := by
      rw [mul_div_assoc, ← mul_div_assoc (Real.exp cost)]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_right
        (le_mul_of_one_le_right (Real.exp_nonneg _) hq1) (Nat.cast_nonneg _)
    _ ≤ (D + C + 8) * (Real.exp cost * ((q : ℝ) / S)) :=
      mul_le_mul_of_nonneg_right (by linarith) hr
    _ ≤ Real.exp (-(E + 2)) := fixedPathSlicedGridMesh_prefactor hD hC hq hfloor
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem fixedPathSlicedSourceErrorBudget_of_floor
    {D P V cost E : ℝ} (hD : 0 ≤ D) (hP : 2 ≤ P) (hE : 0 ≤ E)
    {Input Kernel : Type*} [Fintype Input] [Fintype Kernel]
    (HP : Input → ℕ) (HG : Kernel → ℕ)
    (hInput : (Fintype.card Input : ℝ) ≤ D) (hKernel : (Fintype.card Kernel : ℝ) ≤ D)
    {q S : ℕ} (hq0 : 0 < q) (hq : (q : ℝ) ≤ Real.exp V)
    (hfloor : fixedPathSlicedGridMeshFloor D 4 V cost (P + E + 12) ≤ S)
    (hHP : ∀ i, Real.exp (-cost) * S ≤ (HP i : ℝ))
    (hHG : ∀ i, Real.exp (-cost) * S ≤ (HG i : ℝ))
    {K Kφ ξ : ℝ} (hK0 : 0 ≤ K) (hKφ0 : 0 ≤ Kφ) (hξ0 : 0 ≤ ξ)
    (hK : K ≤ Real.exp P) (hKφ : Kφ ≤ Real.exp P)
    (hξ : ξ ≤ Real.exp (-(P + E + 12))) :
    (∀ i, 2 ≤ HP i ∧ q ≤ HP i ∧
      scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HP i) < 1) ∧
    (∀ i, 2 ≤ HG i ∧ q ≤ HG i ∧
      scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG i) < 1) ∧
    fixedPathSlicedSourceError (∑ i, (q : ℝ) / HP i) (∑ i, (q : ℝ) / HG i)
      (scalarCubeGridBoundaryConstant Empty) K Kφ (2 * Real.exp cost / S)
      (Real.exp (-(P + E + 12))) ξ ≤ Real.exp (-E) := by
  have hP0 : 0 ≤ P := by linarith
  have hF : 0 ≤ P + E + 12 := by positivity
  have hPmesh := fixedPathSlicedGridMesh_of_floor hD (by norm_num : (0 : ℝ) ≤ 4) hF
    HP hInput hq0 hq hfloor hHP (fun _ => 2 * Real.exp cost / S) (fun _ => le_rfl)
  have hGmesh := fixedPathSlicedGridMesh_of_floor hD (by norm_num : (0 : ℝ) ≤ 4) hF
    HG hKernel hq0 hq hfloor hHG (fun _ => 2 * Real.exp cost / S) (fun _ => le_rfl)
  have hC : scalarCubeGridBoundaryConstant Empty = 4 := by
    norm_num [scalarCubeGridBoundaryConstant]
  have hCP : scalarCubeGridBoundaryConstant Empty ≤ Real.exp P := by
    rw [hC]
    have he := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at he
    exact (by linarith : (4 : ℝ) ≤ Real.exp 2).trans (Real.exp_le_exp.mpr hP)
  refine ⟨hPmesh.2.2.2, hGmesh.2.2.2, ?_⟩
  apply fixedPathSlicedSourceError_absorb hP0 hE
    (by rw [hC]; norm_num) hK0 hKφ0 hCP hK hKφ
    (by positivity) (by positivity) (by positivity) (Real.exp_nonneg _) hξ0
    hPmesh.1 hGmesh.1
    (fixedPathSlicedGridMesh_scalar_of_floor hD (by norm_num) hq0 hq hfloor)
    le_rfl hξ

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PhysicalBadProductErrorBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_residue_error_le_of_common_gap {ι : Type*} [Fintype ι]
    (width : ι → ℝ) {A cap W κ : ℝ} (hA : 0 < A) (hcap : 0 ≤ cap)
    (hW : 0 < W) (hwidth : ∀ i, 8 * A * W ≤ width i)
    (hbudget : 2 * (Fintype.card ι : ℝ) * cap ≤ κ * W) :
    (∑ i, 16 * A * cap / width i) ≤ κ := by
  have hterm (i : ι) : 16 * A * cap / width i ≤ 2 * cap / W := by
    calc
      _ ≤ 16 * A * cap / (8 * A * W) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (hwidth i)
      _ = 2 * cap / W := by field_simp; ring
  calc
    _ ≤ ∑ _i : ι, 2 * cap / W := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (2 * (Fintype.card ι : ℝ) * cap) / W := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ κ := (div_le_iff₀ hW).mpr hbudget

theorem finite_residue_error_common_gap_budget {ι : Type*} [Fintype ι]
    (width : ι → ℝ) {A cap W κ : ℝ} (hA : 0 < A) (hcap : 0 < cap)
    (hκ : 0 < κ) (hcapW : cap ≤ W) (hwidth : ∀ i, 8 * A * W ≤ width i)
    (hWbudget : 2 * (Fintype.card ι : ℝ) * cap / κ ≤ W) :
    (∀ i, 8 * A * cap ≤ width i) ∧ (∑ i, 16 * A * cap / width i) ≤ κ := by
  refine ⟨fun i => (mul_le_mul_of_nonneg_left hcapW (by positivity)).trans (hwidth i), ?_⟩
  apply finite_residue_error_le_of_common_gap width hA hcap.le (hcap.trans_le hcapW) hwidth
  have h := (div_le_iff₀ hκ).mp hWbudget
  simpa only [mul_comm] using h

theorem physicalBadProductAccuracy_pos (E Vlog : ℝ) :
    0 < physicalBadProductAccuracy E Vlog := Real.exp_pos _

theorem physicalBadProductAccuracy_inv (E Vlog : ℝ) :
    (physicalBadProductAccuracy E Vlog)⁻¹ = Real.exp (Vlog + 3 * E + 16) := by
  unfold physicalBadProductAccuracy
  rw [Real.exp_neg, inv_inv]

theorem physicalBadProductGap_exp_bound (N : ℕ) {E Vlog F : ℝ}
    (hE : 0 ≤ E) (hVlog : 0 ≤ Vlog) (hF : 0 ≤ F) (Q : ℕ)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog) (hN : (N : ℝ) ≤ Real.exp F) :
    physicalBadProductGap N E Vlog Q ≤ Real.exp (F + 2 * Vlog + 5 * E + 24) := by
  have hcap := (quantitativeBadPrimeRadius_witness_budget hE hVlog Q hQexp).1
  have he2 : (3 : ℝ) ≤ Real.exp 2 := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hh := mul_le_mul he1 he1 (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos 1).le
    have hid : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [hid]
    nlinarith
  have hn : 2 * (N : ℝ) + 1 ≤ Real.exp (F + 2) := by
    rw [Real.exp_add]
    have hf := Real.one_le_exp hF
    have hh := mul_le_mul_of_nonneg_left he2 (Real.exp_pos F).le
    nlinarith
  unfold physicalBadProductGap
  rw [div_eq_mul_inv, physicalBadProductAccuracy_inv]
  calc
    _ ≤ Real.exp (F + 2) * Real.exp (Vlog + 2 * E + 6) * Real.exp (Vlog + 3 * E + 16) := by
      gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CanonicalSpatialSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
theorem selectedColumn_sum (s : I ↪ J) (f : J → ℝ) :
    (∑ i, f (s i)) + (∑ j : UnselectedColumn s, f j.val) = ∑ j, f j := by
  calc
    _ = ∑ j : I ⊕ UnselectedColumn s, f (selectedColumnEquiv s j) := by
      rw [Fintype.sum_sum_type]
      rfl
    _ = _ := Equiv.sum_comp (selectedColumnEquiv s) f

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedActualProfileControl
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value

theorem allocatedLongJetRealCoordinates_measurable :
    Measurable (allocatedLongJetRealCoordinates B U basis S (O := O)) := by
  apply measurable_pi_iff.mpr
  intro q
  rcases q with ⟨⟨⟨j, i | i⟩, ha⟩, o⟩
  · exact (measurable_pi_apply o).comp
      (show Measurable (fun z : AllocatedLongJetRows B U basis S O =>
        z ⟨⟨j, .inl i⟩, ha⟩) from measurable_pi_apply _)
  · exact (measurable_of_countable
      (fun z : O j → ℤ => (z o : ℝ) / (basisAxisScale (basis j) i : ℝ))).comp
      (show Measurable (fun z : AllocatedLongJetRows B U basis S O =>
        z ⟨⟨j, .inr i⟩, ha⟩) from measurable_pi_apply _)

variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

theorem allocatedLongJetMask_measurable (a : {a // ¬grid a}) :
    Measurable (allocatedLongJetMask B U basis S x rows modulus residue a) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact measurable_const
  · change Measurable (allocatedIntegerKernelMask B U basis S x rows j modulus (residue j))
    exact measurable_of_countable _

omit [∀ j, Fintype (O j)] in
theorem allocatedLongJetMask_product_bound {C : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C)
    (z : AllocatedLongJetRows B U basis S O) :
    |∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)| ≤
      C ^ Fintype.card (LayerSamplerAxis I n) := by
  have hr (a : {a // ¬grid a}) :
      0 ≤ allocatedLongJetMask B U basis S x rows modulus residue a (z a) ∧
      allocatedLongJetMask B U basis S x rows modulus residue a (z a) ≤ C := by
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact ⟨zero_le_one, hC⟩
    · exact hm j _
  rw [abs_of_nonneg (Finset.prod_nonneg (fun a _ => (hr a).1))]
  calc
    _ ≤ ∏ _a : {a // ¬grid a}, C :=
      Finset.prod_le_prod (fun a _ => (hr a).1) (fun a _ => (hr a).2)
    _ = C ^ Fintype.card {a // ¬grid a} := by simp
    _ ≤ _ := pow_le_pow_right₀ hC (Fintype.card_subtype_le _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedLongIntegralMass
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

theorem allocatedLongProfileDensity_measurable (f : (output → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (allocatedLongProfileDensity B U b S x rows modulus residue f) := by
  have hm : Measurable (fun z : AllocatedLongJetRows B U b S O =>
      ∏ a, allocatedLongJetMask B U b S x rows modulus residue a (z a)) :=
    Finset.measurable_prod _ (fun a _ =>
      (allocatedLongJetMask_measurable B U b S x rows modulus residue a).comp (measurable_pi_apply a))
  exact (hm.mul (hf.comp (allocatedLongJetRealCoordinates_measurable B U b S))).div_const _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U b S.value

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))


variable (x : G → IntegerScalarCubeBox α S.value) (modulus : ℕ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCoveredSiteExpansion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))


include hΩ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory _root_.Set _root_.OAI.Set
open scoped Classical

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))


include hΩm hΩ

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))


variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "profile" => allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d Ω

include hΩm hΩ in
omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedCoveredProfileDensity_measurable
    (f : AllocatedLongJetRows B U b S O → ℝ) (hf : Measurable f) : Measurable (profile f) := by
  apply mixedCoveredJet_restrictedDensity_measurable U o b hb bW d Ω hΩm hΩ
  have hs : Measurable (fun z : MixedCoveredJetSource I O Q n d => split z.1) :=
    (split).measurable.comp measurable_fst
  have hd : Measurable (coefficientDeckJetDensity root dirs rows d : (∀ j, O j → Q j → ZMod d) → ℝ) :=
    measurable_of_finite _
  change Measurable (fun z : MixedCoveredJetSource I O Q n d =>
    (allocatedGridJetDensity B U b hR hσ S x u v rows ((split z.1).1) *
      coefficientDeckJetDensity root dirs rows d z.2 / coveredJetArrayScale (O := O) U) * f ((split z.1).2))
  exact (((allocatedGridJetDensity_measurable B U b hR hσ S x u v rows).comp
    (measurable_fst.comp hs)).mul (hd.comp measurable_snd)).div_const _ |>.mul (hf.comp (measurable_snd.comp hs))

variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))


variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))


variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "jetRows" => (fun j => (Subtype.val : jets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))
local notation "region" => (fun j (_ : jets j) => standardLatticeClosedQuarterBox (J j))

variable (modulus : ℕ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityComparisonComposition
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem density_l1_triangle_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g h : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, |f x - h x| ∂μ) ≤ (∫ x, |f x - g x| ∂μ) + ∫ x, |g x - h x| ∂μ := by
  rw [← integral_add (f := fun x => |f x - g x|) (g := fun x => |g x - h x|)
    (hf.sub hg).abs (hg.sub hh).abs]
  exact integral_mono (hf.sub hh).abs ((hf.sub hg).abs.add (hg.sub hh).abs)
    (fun x => abs_sub_le (f x) (g x) (h x))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem density_l1_triangle_bound_reverse {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g h : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ)
    {A B : ℝ} (hfg : (∫ x, |f x - g x| ∂μ) ≤ A)
    (hhg : (∫ x, |h x - g x| ∂μ) ≤ B) :
    (∫ x, |f x - h x| ∂μ) ≤ A + B := by
  apply (density_l1_triangle_le μ f g h hf hg hh).trans
  apply add_le_add hfg
  simpa only [abs_sub_comm] using hhg

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexSampledSquarePerturbation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem complex_model_l1_le_of_bounded_tests {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f μ) (hgi : Integrable g μ) {ε : ℝ}
    (he : ∀ φ : X → ℂ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      ‖(∫ x, f x * φ x ∂μ) - ∫ x, g x * φ x ∂μ‖ ≤ ε) :
    (∫ x, ‖f x - g x‖ ∂μ) ≤ ε := by
  let φ := fun x => (starRingEnd ℂ) (f x - g x) / (‖f x - g x‖ : ℂ)
  have hφ : Measurable φ := (Complex.continuous_conj.measurable.comp (hf.sub hg)).div (hf.sub hg).norm.complex_ofReal
  have hbound (x) : ‖φ x‖ ≤ 1 := by
    dsimp only [φ]
    rw [norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self_le_one _
  have hidentity (x) : (f x - g x) * φ x = (‖f x - g x‖ : ℂ) := by
    dsimp only [φ]
    rw [← mul_div_assoc, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_div]
    by_cases h : ‖f x - g x‖ = 0
    · simp [h]
    · rw [pow_two, mul_div_cancel_right₀ _ h]
  have hif := hfi.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hig := hgi.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have h := he φ hφ hbound
  rw [← integral_sub hif hig] at h
  simp_rw [← sub_mul, hidentity] at h
  rw [integral_complex_ofReal, Complex.norm_real,
    Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))] at h
  exact h

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights
end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredJetSampleMeasurable
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

variable {K α : Type*} [Fintype K] [Fintype α] [DecidableEq α]
variable {m : ℕ} {J I Q O : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable [∀ j, Fintype (Q j)] [∀ j, Fintype (O j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (root : K → ℤ) (dirs : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem canonicalCoefficientDeckSample_jet_measurable (d : ℕ) [NeZero d] :
    Measurable (fun p : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) Q d =>
      euclideanCoefficientJetMap U root dirs rows
        (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)) := by
  have hchart := (coveredJetChart_continuous (O := O) U b hb bW d).measurable.comp
    (mixedCoveredJetCoordinates_measurable (O := O) (B := Q) (n := n) U o d)
  have hjet := canonicalCoefficientJetArrays_measurable (I := I) (n := n) root dirs rows
  have hdeck : Measurable (coefficientDeckJetMap (B := Q) root dirs rows d) := measurable_of_finite _
  convert hchart.comp ((hjet.comp measurable_fst).prodMk (hdeck.comp measurable_snd)) using 1
  funext p
  exact canonicalCoefficientDeckSample_chart U o root dirs rows b hb bW d p.1 p.2

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelSiteMask
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rowMap" => (fun j : Fin m => (Subtype.val : rows j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable (x : G → IntegerScalarCubeBox α S.value) (modulus : ℕ)
variable (residue : ∀ j, Matrix {t : Finset α // t ∈ rowSets j}
  (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

variable {Q : Fin m → Type*}

omit [Fintype α] in
theorem allocatedKernelSiteMask_bound (period : ℕ)
    {C : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rowMap j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rowMap j modulus (residue j) z ≤ C)
    (r : Finset α → ∀ j, Fin (n j) → ZMod period) :
    |allocatedKernelSiteMask B U b S rowSets x modulus residue period r| ≤
      C ^ Fintype.card (LayerSamplerAxis I n) :=
  allocatedLongJetMask_product_bound B U b S x rowMap modulus residue hC hm _

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedJointMaskedDensityComparison
namespace OAI

section

namespace Erdos3
open MeasureTheory

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedMaskedTiltedConstant_ge_two (m : ℕ) :
    2 ≤ allocatedMaskedTiltedConstant m :=
  (Classical.choose_spec (exists_affine_coefficient_cover_tilted_family_comparison.{0, 0, 0, 0} m)).1

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedProgressionDensityIdentity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

variable {K : Type*} [Fintype K] {m : ℕ} {J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ)

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

omit [DecidableEq G] [∀ index, DecidableEq (B index)]
  [∀ index, DecidableEq (O index)] in
theorem allocatedProgressionCoveredIntegrand_integrable
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1) :
    Integrable (fun p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
      CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d =>
      F (((allocatedCoefficientSplit B U basis S) p.1).1,
        euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows
          (canonicalCoefficientDeckSample U bW basis hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
      ((source).prod (deck).toMeasure) := by
  let : IsProbabilityMeasure source := allocatedCoefficientSource_probability B U basis hR hσ S
  apply Integrable.of_bound (C := 1)
  · exact (hF.comp
      ((((allocatedCoefficientSplit B U basis S).measurable.comp measurable_fst).fst).prodMk
        (canonicalCoefficientDeckSample_jet_measurable U o (wholeRoot y) (wholeDirs y)
          rows basis hb bW d))).aestronglyMeasurable
  · exact ae_of_all _ (fun p => hFbound _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

end OAI

end


