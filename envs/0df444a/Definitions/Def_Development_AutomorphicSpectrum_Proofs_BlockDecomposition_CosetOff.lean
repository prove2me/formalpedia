-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:06.243937+00:00
-- url     : https://prove2.me/theorems/0ac574f8-e6b3-4418-9ca2-e1bb34408e62
-- title:
--   Coset Off
-- statement:
--   Definitions and structural lemmas for Coset Off, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetOff.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped Classical
namespace GlobalTheory.CompanionTheory.Equi
variable {F : Type} [Field F] [NumberField F]
def LocMem (I : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) (z : F) : Prop :=
  ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ ∃ y ∈ I, (s : F) * z = (y : F)
def cosetOff {ι : Type} (S : Finset (HeightOneSpectrum (𝓞 F))) (I : Ideal (𝓞 F)) (x0 : ι → F) : Set (ι → F) :=
  {x | ∀ v, v ∉ S → ∀ i, LocMem I v (x i - x0 i)}
def latCoset {ι : Type} (I : Ideal (𝓞 F)) (x0 : ι → F) : Set (ι → F) :=
  {x | ∀ i, ∃ y ∈ I, (y : F) = x i - x0 i}
def ballV (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) : Set (Fv F v) :=
  {z | Valued.v z ≤ WithZero.exp (-(k : ℤ))}
def boxInd {ι : Type} (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) (c y : ι → Fv F v) : ℝ :=
  if ∀ i, y i - c i ∈ ballV v k then 1 else 0
def term {ι : Type} (θ : ℝ →+* Ainf F) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (ι → Ainf F) → ℝ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), (ι → Fv F v) → ℝ) (ε : ℝ) (x : ι → F) : ℝ :=
  φ (fun i => θ ε * algebraMap F (Ainf F) (x i)) * ∏ v ∈ S, ψ v fun i => algebraMap F (Fv F v) (x i)
end GlobalTheory.CompanionTheory.Equi
end


