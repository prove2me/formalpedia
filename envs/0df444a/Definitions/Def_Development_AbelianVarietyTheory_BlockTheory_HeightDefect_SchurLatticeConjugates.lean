-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SchurLatticeConjugates
-- name    : Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SchurLatticeConjugates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:17.092805+00:00
-- url     : https://prove2.me/theorems/3ee82d29-2e6a-46fb-9522-1ad4b235ab69
-- title:
--   Schur Lattice Conjugates
-- statement:
--   Definitions and structural lemmas for Schur Lattice Conjugates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SchurLatticeConjugates.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
namespace GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
noncomputable def ord_vw {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K)) : ℕ :=
  multiplicity la.asIdeal I
noncomputable def conjDifferent {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) : Ideal (𝓞 K) :=
  (differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom σ)
noncomputable def defectAt_vw {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K)) : ℕ :=
  a * max (ord_vw la (conjDifferent σ)) (ord_vw la (Ideal.span {((n' : ℕ) : 𝓞 K)}))
noncomputable def defect_vw (E : Type) {K : Type} [Field E] [NumberField E] [Field K]
    [NumberField K] (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Finset.univ.sup fun σ : E →+* K => defectAt_vw σ n' a la
noncomputable def lrd (E : Type) [Field E] [NumberField E] : ℝ :=
  Real.log (rootDiscr E)
noncomputable def logNorm {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm la.asIdeal)
noncomputable def normSum {K : Type} [Field K] [NumberField K]
    (b : HeightOneSpectrum (𝓞 K) → ℕ) : ℝ :=
  (∑ᶠ la, (b la : ℝ) * logNorm la) / (Module.finrank ℚ K : ℝ)
def DefectAtSumBound : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) (n' : ℕ+) (a : ℕ) (κ : ℝ), (a : ℝ) ≤ κ →
    (Function.support (defectAt_vw σ n' a)).Finite ∧
      normSum (defectAt_vw σ n' a) ≤ (lrd E + Real.log ((n' : ℕ) : ℝ)) * κ
def DefectSumBound : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K],
    Nonempty (E →+* K) → ∀ (n' : ℕ+) (a : ℕ) (κ : ℝ), (a : ℝ) ≤ κ →
    (Function.support (defect_vw E (K := K) n' a)).Finite ∧
      normSum (defect_vw E (K := K) n' a) ≤ (lrd E + Real.log ((n' : ℕ) : ℝ)) * κ
end GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects


