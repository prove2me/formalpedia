-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
-- name    : Formalism_QuotientMetricDivisors_EigenRatHermLcv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:34.041386+00:00
-- url     : https://prove2.me/theorems/7418ff78-0fa0-4250-aac3-ff79aaf68c0d
-- title:
--   Eigen Rat Herm Lcv
-- statement:
--   Definitions and structural lemmas for Eigen Rat Herm Lcv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/EigenRatHermLcv.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.DivisionValues
def extSpan {K Ω : Type} [Field K] [Field Ω] {n : ℕ} (j : K →+* Ω) (Z : Submodule K (Fin n → K)) :
    Submodule Ω (Fin n → Ω) :=
  Submodule.span Ω ((fun z i => j (z i)) '' (Z : Set (Fin n → K)))
def simEig {K Ω : Type} [Field K] [Field Ω] {n : ℕ} (j : K →+* Ω)
    (𝒯 : Set (Matrix (Fin n) (Fin n) K)) (χ : Matrix (Fin n) (Fin n) K → Ω) :
    Submodule Ω (Fin n → Ω) where
  carrier := {x | ∀ T ∈ 𝒯, (T.map j).mulVec x = χ T • x}
  add_mem' := by
    intro x y hx hy T hT
    rw [Matrix.mulVec_add, hx T hT, hy T hT, smul_add]
  zero_mem' := by
    intro T _
    rw [Matrix.mulVec_zero, smul_zero]
  smul_mem' := by
    intro a x hx T hT
    rw [Matrix.mulVec_smul, hx T hT, smul_comm]
def IsFullEigSum {K Ω : Type} [Field K] [Field Ω] {n : ℕ} (j : K →+* Ω)
    (𝒯 : Set (Matrix (Fin n) (Fin n) K)) (Z : Submodule K (Fin n → K)) : Prop :=
  ∃ S : Set (Matrix (Fin n) (Fin n) K → Ω), extSpan j Z = ⨆ χ ∈ S, simEig j 𝒯 χ
def IsAdjStable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (𝒯 : Set (Matrix (Fin n) (Fin n) K)) : Prop :=
  ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, ∀ x y : Fin n → K, hform H (T.mulVec x) y = hform H x (T'.mulVec y)
def IsCommStable {K : Type} [Field K] {n : ℕ} (𝒯 : Set (Matrix (Fin n) (Fin n) K))
    (Z : Submodule K (Fin n → K)) : Prop :=
  ∀ B : Matrix (Fin n) (Fin n) K, (∀ T ∈ 𝒯, B * T = T * B) → ∀ z ∈ Z, B.mulVec z ∈ Z
def EigenTwist : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ 𝒯 : Set (Matrix (Fin n) (Fin n) K), (∀ T ∈ 𝒯, ∀ i j, T i j ∈ K0) →
    (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T * T' = T' * T) → IsAdjStable H 𝒯 →
    ∀ (Z : Submodule K (Fin n → K)) (Ω : Type) [Field Ω] (j : K →+* Ω), IsFullEigSum j 𝒯 Z →
    ∀ σ : K →+* ℂ, embSpan σ Z = embSpan (twist σ) Z
def FullEigComm : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] (j : K →+* Ω) (n : ℕ) (𝒯 : Set (Matrix (Fin n) (Fin n) K))
    (Z : Submodule K (Fin n → K)), IsFullEigSum j 𝒯 Z → IsCommStable 𝒯 Z
def CommTwist : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ 𝒯 : Set (Matrix (Fin n) (Fin n) K), (∀ T ∈ 𝒯, ∀ i j, T i j ∈ K0) →
    (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T * T' = T' * T) → IsAdjStable H 𝒯 →
    ∀ Z : Submodule K (Fin n → K), IsCommStable 𝒯 Z →
    ∀ σ : K →+* ℂ, embSpan σ Z = embSpan (twist σ) Z
def CommFullEig : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ 𝒯 : Set (Matrix (Fin n) (Fin n) K), (∀ T ∈ 𝒯, ∀ i j, T i j ∈ K0) →
    (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T * T' = T' * T) → IsAdjStable H 𝒯 →
    ∀ Z : Submodule K (Fin n → K), IsCommStable 𝒯 Z →
    ∀ σ : K →+* ℂ, IsFullEigSum σ 𝒯 Z
def EigenAdjConj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ 𝒯 : Set (Matrix (Fin n) (Fin n) K), (∀ T ∈ 𝒯, ∀ i j, T i j ∈ K0) →
    ∀ (σ : K →+* ℂ) (χ : Matrix (Fin n) (Fin n) K → ℂ) (x : Fin n → ℂ), x ∈ simEig σ 𝒯 χ → x ≠ 0 →
    ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯,
      (∀ u v : Fin n → K, hform H (T.mulVec u) v = hform H u (T'.mulVec v)) →
      χ T' = starRingEnd ℂ (χ T)
def EigenRatHermLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    IsRatHerm K0 H X →
    ∀ 𝒯 : Set (Matrix (Fin n) (Fin n) K), (∀ T ∈ 𝒯, ∀ i j, T i j ∈ K0) →
    (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T * T' = T' * T) → IsAdjStable H 𝒯 →
    ∀ (Z : Submodule K (Fin n → K)) (Ω : Type) [Field Ω] (j : K →+* Ω), IsFullEigSum j 𝒯 Z →
    ∃ (d : ℕ) (z : Fin d → Fin n → K) (XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ),
      LinearIndependent K z ∧ Submodule.span K (Set.range z) = Z ∧
      (∀ a i, z a i ∈ cmMax K) ∧
      IsRatHerm (cmMax K) (gramMat H z) XT ∧
      (∀ (v : InfinitePlace K) (x y : Fin d → K),
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) XT v x y =
          Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v (comb z x) (comb z y)) ∧
      (∀ x y : Fin d → K, hform (gramMat H z) x y = hform H (comb z x) (comb z y)) ∧
      ∀ T : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K T →
        (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
          lw w * (jw (gramMat H z) w T : ℝ)).Finite ∧
        lcv XT T = - ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (jw (gramMat H z) w T : ℝ)
end Formalism.DivisionValues


