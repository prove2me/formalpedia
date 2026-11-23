-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:25.167218+00:00
-- url     : https://prove2.me/theorems/70972ade-f32f-4293-b6d6-5888a04117ab
-- title:
--   Second Countable Herm C
-- statement:
--   Definitions and structural lemmas for Second Countable Herm C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SecondCountableHermC.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
open MeasureTheory
open scoped Matrix ComplexConjugate
def hermC (n : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) ℂ) := selfAdjoint _
theorem isClosed_hermC (n : ℕ) : IsClosed (hermC n : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hset : (hermC n : Set (Matrix (Fin n) (Fin n) ℂ)) = {b | star b = b} := rfl
  rw [hset]
  exact isClosed_eq continuous_star continuous_id
instance measHermC (n : ℕ) : MeasurableSpace (hermC n) := borel _
instance borelHermC (n : ℕ) : BorelSpace (hermC n) := ⟨rfl⟩
instance locCompactHermC (n : ℕ) : LocallyCompactSpace (hermC n) :=
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  (isClosed_hermC n).isClosedEmbedding_subtypeVal.locallyCompactSpace
instance secondCountableHermC (n : ℕ) : SecondCountableTopology (hermC n) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _
def detW {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) : ℝ := (Matrix.det (1 + b * b)).re
def gramC {n M : ℕ} (J : Matrix (Fin M) (Fin M) ℂ) (X : Fin n → Fin M → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun a c => ∑ i, ∑ j, conj (X a i) * J i j * X c j
def phaseM {W : Type} [Fintype W] {n M : ℕ} (J : W → Matrix (Fin M) (Fin M) ℂ)
    (B : W → Matrix (Fin n) (Fin n) ℂ) (X : W → Fin n → Fin M → ℂ) : ℝ :=
  ∑ w, (Matrix.trace (B w * gramC (J w) (X w))).re
def coreC {W : Type} [Fintype W] {n M : ℕ} (J : W → Matrix (Fin M) (Fin M) ℂ)
    (μ : Measure (W → Fin n → Fin M → ℂ)) (g : (W → Fin n → Fin M → ℂ) → ℂ) (b : W → hermC n) : ℂ :=
  ∫ X, g X * Complex.exp (2 * Real.pi * Complex.I *
    ((phaseM J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) X : ℝ) : ℂ)) ∂μ
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch


