-- Prove2me | solution 1 for AutomorphicForm.exists_forall_exists_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_norm_le_on_balls_and_of_re_mem_Icc_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/175b3a91-4a8a-5990-9f74-c6791e678280

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins

import Theorems.Thm_EisensteinGeneral_Piece_exists_forall_exists_factorizationDatum_one_uniform_of_flat_principalLevel_archCutSubmodule
import Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_factorizationDatum_one
import Theorems.Thm_EisensteinGeneral_LocalCorrection_norm_corrOff_le_of_le_re
import Theorems.Thm_EisensteinGeneral_LocalCorrection_exists_forall_norm_corrOn_le_of_le_re
import Definitions.Def_EisensteinGeneral_LocalCorrection
import Definitions.Def_EisensteinGeneral_FactorizationDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_exists_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_norm_le_on_balls_and_of_re_mem_Icc_of_flat
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace U1aStructAux

theorem two_le_absNorm {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem norm_le_sqrt_of_sq_le {z : ℂ} {C I : ℝ} (hC : 0 ≤ C) (hI : I ≤ 1) (hI0 : 0 ≤ I)
    (h : ‖z‖ ^ 2 ≤ C * I) : ‖z‖ ≤ Real.sqrt C := by
  have h2 : ‖z‖ ^ 2 ≤ C := h.trans (by nlinarith)
  calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt C := Real.sqrt_le_sqrt h2

end U1aStructAux

open AutomorphicForm U1aStructAux EisensteinGeneral.LocalCorrection in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (_hψ : IsGlobalAddChar K ψ)
    (ψv : (v : HeightOneSpectrum (𝓞 K)) → AddChar (v.adicCompletion K) ℂ)
    (nψ : HeightOneSpectrum (𝓞 K) → ℤ)
    (_hnψfin : (Function.support nψ).Finite)
    (_hψv : ∀ (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K),
      Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
    (_hψv' : ∀ v : HeightOneSpectrum (𝓞 K),
      ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (nψ v + 1) ∧ ψv v x ≠ 1)
    (_hψfin : ∀ x : FiniteAdeleRing (𝓞 K) K,
      ψ (AddMonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) x)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K), ψv v (x v))
    (θr : {w : InfinitePlace K // w.IsReal} → ℝ) (_hθr : ∀ i, θr i ≠ 0)
    (θc : {w : InfinitePlace K // w.IsComplex} → ℂ) (_hθc : ∀ w, θc w ≠ 0)
    (_hψarch : ∀ p : mixedEmbedding.mixedSpace K,
      ψ (AddMonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm p))
      = (∏ i : {w : InfinitePlace K // w.IsReal},
      Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
      * ∏ w : {w : InfinitePlace K // w.IsComplex},
      Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)))
    (σ₁ σ₂ : ℝ)
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (n₀ k₀ κ : ℕ) (t₀ : ℤ) (C₀ M : ℝ), SK ⊆ S ∧ 0 ≤ C₀ ∧ 0 ≤ M ∧
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (τμ τν : InfinitePlace K → ℝ)
      (_hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ v : ℝ) : ℂ) * Complex.I))
      (_hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν v : ℝ) : ℂ) * Complex.I))
      (mμ mν : InfinitePlace K → ℤ)
      (_hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
      (_hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v))
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
      (_hψfn : ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1)
      (ϖ : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ)
      (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)),
    let E : ℂ → AdelicGL2 (𝓞 K) K → ℂ := fun s h =>
      ψf s h + ∑' ξ : K, ψf s (adelicWeyl (𝓞 K) K *
        unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * h)
    let jR : ℤ → ℂ → ℝ → ℂ := fun k w t => ∫ x : ℝ,
      ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
          * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))
    let jC : ℕ → ℕ → ℂ → ℂ → ℂ := fun a b w ζ => ∫ z : ℂ,
      z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))
    ∃ (n : ℕ) (C : Fin n → ℂ → ℂ)
      (kdat : Fin n → {w : InfinitePlace K // w.IsReal} → ℤ)
      (τr : Fin n → {w : InfinitePlace K // w.IsReal} → ℝ)
      (abm : Fin n → {w : InfinitePlace K // w.IsComplex} → ℕ × ℕ × ℕ)
      (τc : Fin n → {w : InfinitePlace K // w.IsComplex} → ℝ)
      (a : (AdeleRing (𝓞 K) K)ˣ) (u : AdeleRing (𝓞 K) K)
      (thr : HeightOneSpectrum (𝓞 K) → ℤ)
      (Φ : Fin n → (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K → ℂ → ℂ),
      n ≤ n₀ ∧ a = 1 ∧ u = 0 ∧
      (∀ (j : Fin n) (i : {w : InfinitePlace K // w.IsReal}), τr j i = τμ i.1 - τν i.1) ∧
      (∀ (j : Fin n) (w : {w : InfinitePlace K // w.IsComplex}), τc j w = 2 * (τμ w.1 - τν w.1)) ∧
      (∀ (j : Fin n) (i : {w : InfinitePlace K // w.IsReal}), |kdat j i| ≤ (k₀ : ℤ)) ∧
      (∀ (j : Fin n) (w : {w : InfinitePlace K // w.IsComplex}), (abm j w).2.2 ≤ k₀) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), thr v ≤ t₀) ∧
      (∀ (j : Fin n) (s : ℂ), σ₁ ≤ s.re → s.re ≤ σ₂ → ‖C j s‖ ≤ C₀) ∧
      (∀ j, Differentiable ℂ (C j)) ∧
      (∀ (j : Fin n) (w : {w : InfinitePlace K // w.IsComplex}),
        (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2) ∧
      (∀ v ∉ S, thr v = 0) ∧
      (∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 K)) (w : v.adicCompletion K), Differentiable ℂ (Φ j v w)) ∧
      (∀ (j : Fin n), ∀ v ∉ S, ∀ (w : v.adicCompletion K) (s : ℂ), Valued.v w = 1 → Φ j v w s = 1) ∧
      (∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 K)) (w : v.adicCompletion K) (s : ℂ), w ≠ 0 →
        WithZero.exp (thr v) < Valued.v w → Φ j v w s = 0) ∧
      (∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 K))
        (w : v.adicCompletion K) (e : ℤ) (s : ℂ), σ₁ ≤ s.re → s.re ≤ σ₂ → Valued.v w = WithZero.exp e →
          ‖Φ j v w s‖ ≤ (if v ∈ S then M else 1) * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ κ) ∧
      (∀ R : ℝ, ∃ (M' : ℝ) (κ' : ℕ), 0 ≤ M' ∧ ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 K))
        (w : v.adicCompletion K) (e : ℤ) (s : ℂ), ‖s‖ ≤ R → Valued.v w = WithZero.exp e →
          ‖Φ j v w s‖ ≤ (if v ∈ S then M' else 1) * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ κ') ∧
      (∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 K)) (w₀ : v.adicCompletion K), w₀ ≠ 0 → ∃ δ : ℤ,
        ∀ (w : v.adicCompletion K) (s : ℂ), Valued.v (w - w₀) ≤ WithZero.exp δ → Φ j v w s = Φ j v w₀ s) ∧
      ∀ (s : ℂ), 1 < s.re → ∀ (ξ : K), ξ ≠ 0 → ∀ y : (AdeleRing (𝓞 K) K)ˣ,
        whittakerCoefficient K (productionPins K) ψ (E s) ξ (diagOne y)
          = ((ν y : ℂˣ) : ℂ) * ((cpowChar αm hαm (1 / 2 - s) y : ℂˣ) : ℂ)
            * ∑ j : Fin n, C j s
              * ((((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)
                  * ((((distribHaarChar (AdeleRing (𝓞 K) K) a : ℝ≥0) : ℝ) : ℂ)⁻¹
                  * ψ (algebraMap K (AdeleRing (𝓞 K) K) ξ * (y : AdeleRing (𝓞 K) K) * u)))
              * (∏ i : {w : InfinitePlace K // w.IsReal},
                  jR (kdat j i) (s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2)
                    (-(θr i * (InfiniteAdeleRing.ringEquiv_mixedSpace K
                      (algebraMap K (AdeleRing (𝓞 K) K) ξ * (y : AdeleRing (𝓞 K) K)
                        * ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1).1 i)))
              * (∏ w : {w : InfinitePlace K // w.IsComplex},
                  jC (abm j w).1 (abm j w).2.1
                    (2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2)
                    (-(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace K
                      (algebraMap K (AdeleRing (𝓞 K) K) ξ * (y : AdeleRing (𝓞 K) K)
                        * ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1).2 w)))
              * ((∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
                  (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                    * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))))
                * ∏ᶠ v : HeightOneSpectrum (𝓞 K),
                    Φ j v ((algebraMap K (AdeleRing (𝓞 K) K) ξ * (y : AdeleRing (𝓞 K) K)
                        * ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) s) := by
  intro αm

  obtain ⟨S₀, n₀, k₀, m₀, c₀, L, Amenu, Bmenu, C₀, hSK, hnψ0, hC₀, hm₀, hc₀, hAmenu, hBmenu, H1⟩ :=
    EisensteinGeneral.Piece.exists_forall_exists_factorizationDatum_one_uniform_of_flat_principalLevel_archCutSubmodule K SK ξK hξc hξt N hN tysK w hξw ψ _hψ ψv nψ _hnψfin _hψv _hψv' _hψfin θr _hθr θc _hθc _hψarch
  obtain ⟨d, μ𝒪, lam, hd, hμ𝒪, H2⟩ := AutomorphicForm.exists_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_factorizationDatum_one K
  have hN2 : ∀ v : HeightOneSpectrum (𝓞 K), 2 ≤ Ideal.absNorm v.asIdeal := two_le_absNorm
  have hN1' : ∀ v : HeightOneSpectrum (𝓞 K), (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℕ) := fun v => by
    exact_mod_cast le_trans (by norm_num) (hN2 v)

  set cA : HeightOneSpectrum (𝓞 K) → Fin L → ℝ := fun v l =>
    ∫ x in (v.adicCompletionIntegers K : Set (v.adicCompletion K)), ‖Amenu l v x‖ ∂(lam v) with hcA
  set bAB : HeightOneSpectrum (𝓞 K) → Fin L → Fin L → ℝ := fun v l l' =>
    ∫ x, (‖(v.adicCompletionIntegers K : Set (v.adicCompletion K)).indicator (Amenu l v) x‖
        + (v.adicCompletionIntegers K : Set (v.adicCompletion K))ᶜ.indicator
            (fun y => ((LanglandsTunnell.TateLocal.modulus y : ℝ))⁻¹ ^ 3 * ‖Bmenu l' v y⁻¹‖) x) ∂(lam v) with hbAB
  have hcA0 : ∀ v l, 0 ≤ cA v l := fun v l => integral_nonneg fun x => norm_nonneg _
  have hbAB0 : ∀ v l l', 0 ≤ bAB v l l' := fun v l l' =>
    integral_nonneg fun x => add_nonneg (norm_nonneg _)
      (Set.indicator_nonneg (fun y _ => mul_nonneg (pow_nonneg (inv_nonneg.mpr (NNReal.coe_nonneg _)) 3)
        (norm_nonneg _)) x)

  choose Efun κfun hE0 hE using fun (v : HeightOneSpectrum (𝓞 K)) (l : Fin L) (l' : Fin L) =>
    EisensteinGeneral.LocalCorrection.exists_forall_norm_corrOn_le_of_le_re (hN2 v) (nψ v) c₀ m₀ (hμ𝒪 v) (cA v l) (bAB v l l') (d v) σ₁ (hcA0 v l) (hbAB0 v l l') (hd v)
  set M : ℝ := 1 + ∑ v ∈ S₀, ∑ l : Fin L, ∑ l' : Fin L, Efun v l l' with hM
  have hM0 : 0 ≤ M := by
    have : 0 ≤ ∑ v ∈ S₀, ∑ l : Fin L, ∑ l' : Fin L, Efun v l l' :=
      Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun l' _ => hE0 v l l'
    linarith
  have hEM : ∀ v ∈ S₀, ∀ l l', Efun v l l' ≤ M := by
    intro v hv l l'
    have h1 : Efun v l l' ≤ ∑ l'' : Fin L, Efun v l l'' :=
      Finset.single_le_sum (fun l'' _ => hE0 v l l'') (Finset.mem_univ l')
    have h2 : (∑ l'' : Fin L, Efun v l l'') ≤ ∑ l₁ : Fin L, ∑ l'' : Fin L, Efun v l₁ l'' :=
      Finset.single_le_sum (fun l₁ _ => Finset.sum_nonneg fun l'' _ => hE0 v l₁ l'') (Finset.mem_univ l)
    have h3 : (∑ l₁ : Fin L, ∑ l'' : Fin L, Efun v l₁ l'') ≤ ∑ v' ∈ S₀, ∑ l₁ : Fin L, ∑ l'' : Fin L, Efun v' l₁ l'' :=
      Finset.single_le_sum (fun v' _ => Finset.sum_nonneg fun l₁ _ => Finset.sum_nonneg fun l'' _ => hE0 v' l₁ l'') hv
    linarith
  set k' : ℕ := ⌈2 * max 0 (-σ₁)⌉₊ with hk'
  have hk'R : 2 * max 0 (-σ₁) ≤ k' := Nat.le_ceil _
  set κ : ℕ := max (k' + 1)
    ((S₀ ×ˢ (Finset.univ ×ˢ Finset.univ)).sup fun p : HeightOneSpectrum (𝓞 K) × (Fin L × Fin L) => κfun p.1 p.2.1 p.2.2)
    with hκ
  have hκle : ∀ v ∈ S₀, ∀ l l', κfun v l l' ≤ κ := by
    intro v hv l l'
    have h1 : (fun p : HeightOneSpectrum (𝓞 K) × (Fin L × Fin L) => κfun p.1 p.2.1 p.2.2) (v, (l, l'))
        ≤ (S₀ ×ˢ (Finset.univ ×ˢ Finset.univ)).sup
            (fun p : HeightOneSpectrum (𝓞 K) × (Fin L × Fin L) => κfun p.1 p.2.1 p.2.2) :=
      Finset.le_sup (f := fun p : HeightOneSpectrum (𝓞 K) × (Fin L × Fin L) => κfun p.1 p.2.1 p.2.2)
        (Finset.mem_product.mpr ⟨hv, Finset.mem_product.mpr ⟨Finset.mem_univ l, Finset.mem_univ l'⟩⟩)
    exact h1.trans (le_max_right _ _)
  set t₀ : ℤ := ((S₀.sup fun v => (nψ v).toNat : ℕ) : ℤ) + ((max m₀ c₀ : ℕ) : ℤ) with ht₀
  have ht₀0 : 0 ≤ t₀ := by rw [ht₀]; positivity
  refine ⟨S₀, n₀, k₀, κ, t₀, Real.sqrt C₀, M, hSK, Real.sqrt_nonneg _, hM0, ?_⟩
  intro hαm μ ν hμ hν hμic hνic hμc hνc hμν τμ τν hτμ hτν mμ mν hmμ hmν ψf hψf hψfK hψff hψfjc hψfhol hψfKu
    hψfflat hψflev hψfty hψfn ϖ hϖ E jR jC
  by_cases hne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 K) K), ψf s g ≠ 0
  ·
    obtain ⟨D, hDn, hDa, hDu, hDm, hDc, hτr, hτc, hk, habm2, hAD, hBD, hCconst, hCbd⟩ :=
      H1 hαm μ ν hμ hν hμic hνic hμc hνc hμν τμ τν hτμ hτν mμ mν hmμ hmν ψf hψf hψfK hψff hψfjc hψfhol hψfKu
        hψfflat hψflev hψfty hψfn hne ϖ hϖ S₀ (Finset.Subset.refl S₀)
    have hflat' : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 K) K),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ w' : InfinitePlace K, IsRowIsometry (archComponent K w' (glArch (𝓞 K) K k))) →
        ψf s k = ψf s' k := by
      intro s s' k h1 h2
      have e1 := hψfflat s ⟨k, ⟨h1, h2⟩⟩
      have e2 := hψfflat s' ⟨k, ⟨h1, h2⟩⟩
      exact e1.trans e2.symm
    obtain ⟨Φ, hoff, hon, hCd, habm, hthr0, hΦd, hΦ1, hΦ0, hdisc, hΦloc, hform⟩ :=
      H2 hαm μ ν hμ hν hμic hνic ψ _hψ ψv nψ _hnψfin _hψv _hψv' _hψfin θr _hθr θc _hθc _hψarch ϖ hϖ
        ψf hψf hψfK hψff hψfjc hψfhol hflat' hne S₀ D
    refine ⟨D.n, D.C, D.kdat, D.τr, D.abm, D.τc, D.a, D.u,
      (fun v => if v ∈ S₀ then nψ v + ((max D.mS (D.cS v) : ℕ) : ℤ) else 0), Φ,
      hDn, hDa, hDu, hτr, hτc, hk, habm2, ?_, ?_, hCd, habm, ?_, hΦd, hΦ1, ?_, ?_, ?_, hΦloc, hform⟩
    ·
      intro v
      by_cases hv : v ∈ S₀
      · simp only [hv, ↓reduceIte]
        rw [hDm, hDc v hv, ht₀]
        have h1 : ((nψ v).toNat : ℕ) ≤ S₀.sup fun v => (nψ v).toNat :=
          Finset.le_sup (f := fun v => (nψ v).toNat) hv
        have h2 : nψ v ≤ ((nψ v).toNat : ℤ) := Int.self_le_toNat _
        have h3 : (((nψ v).toNat : ℕ) : ℤ) ≤ ((S₀.sup fun v => (nψ v).toNat : ℕ) : ℤ) := by exact_mod_cast h1
        linarith
      · simp only [hv, ↓reduceIte]; exact ht₀0
    ·
      intro j s _ _
      rw [hCconst j s]
      have hI0 : 0 ≤ ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) :=
        integral_nonneg fun k => by positivity
      exact norm_le_sqrt_of_sq_le hC₀ hψfn hI0 (hCbd j)
    ·
      intro v hv; simp only [hv, ↓reduceIte]
    ·
      intro j v w' s hw hlt
      exact hΦ0 j v w' s hw (by convert hlt using 3; beta_reduce; congr)
    ·
      intro j v w' e s hs₁ _ he
      have hw0 : w' ≠ 0 := by
        intro h0; rw [h0, map_zero] at he; exact WithZero.zero_ne_coe he
      have hwe : WithZero.log (Valued.v w') = e := by rw [he, WithZero.log_exp]
      have hpow1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat := one_le_pow₀ (hN1' v)
      by_cases hv : v ∈ S₀
      · rw [if_pos hv]
        obtain ⟨γ₀, sh, hγ₀, hsh, hrep⟩ := hon j v hv w'
        obtain ⟨l, hl⟩ := hAD j v
        obtain ⟨l', hl'⟩ := hBD j v
        rw [hrep s, hwe, hDm, hDc v hv]
        have hγ₀' : ‖γ₀‖ ≤ cA v l := by rw [hcA]; simpa only [hl] using hγ₀
        have hsh' : ∀ k : ℕ, 1 ≤ k → ‖sh k‖ ≤ bAB v l l' * d v ^ k := by
          intro k hk; rw [hbAB]; simpa only [hl, hl'] using hsh k hk
        calc _ ≤ Efun v l l' * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ κfun v l l' :=
              hE v l l' c₀ m₀ e γ₀ sh s le_rfl le_rfl hγ₀' hsh' hs₁
          _ ≤ M * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ κ :=
              mul_le_mul (hEM v hv l l') (pow_le_pow_right₀ hpow1 (hκle v hv l l')) (by positivity) hM0
      · rw [if_neg hv, one_mul, hoff j v hv w' s, hwe]
        calc _ ≤ (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ (k' + 1) :=
              EisensteinGeneral.LocalCorrection.norm_corrOff_le_of_le_re (D.hχϖ v) (hN2 v) e k' hk'R hs₁
          _ ≤ (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ κ :=
              pow_le_pow_right₀ hpow1 (le_max_left _ _)
    ·
      intro R
      obtain ⟨M', κ', hM', h⟩ := hdisc R
      exact ⟨M', κ', hM', fun j v w' e s hs he => by convert h j v w' e s hs he using 3⟩
  ·
    push Not at hne
    have hE0 : ∀ s, E s = fun _ => (0 : ℂ) := by
      intro s; funext h
      show ψf s h + ∑' ξ : K, ψf s (adelicWeyl (𝓞 K) K *
        unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * h) = 0
      simp [hne]
    refine ⟨0, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j,
      fun j => Fin.elim0 j, 1, 0, fun _ => 0, fun j => Fin.elim0 j,
      Nat.zero_le _, rfl, rfl, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j,
      fun _ => ht₀0, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun _ _ => rfl,
      fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, ?_, fun j => Fin.elim0 j, ?_⟩
    · intro R; exact ⟨0, 0, le_rfl, fun j => Fin.elim0 j⟩
    · intro s _ ξ _ y
      rw [hE0 s, whittakerCoefficient_zero]
      simp

end S_AutomorphicForm_exists_forall_exists_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_norm_le_on_balls_and_of_re_mem_Icc_of_flat
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_exists_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_norm_le_on_balls_and_of_re_mem_Icc_of_flat (solution)
