-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsLab
-- name    : Formalism_LocalToGlobal_GaloisLevelStructure_DefsLab
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T17:55:13.142449+00:00
-- url     : https://prove2.me/theorems/7bdacb18-8b52-40f4-b302-fcc4df725517
-- title:
--   Defs Lab
-- statement:
--   Definitions and structural lemmas for Defs Lab, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GaloisLevelStructure/DefsLab.lean

import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
namespace Formalism.L2.NG
section lab
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {p : ℕ} [Fact p.Prime]
def TameVal (A : ValuationSubring Ω) (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p) (σ : Ω ≃ₐ[E] Ω) (d : ℕ)
    (z : Formalism.CyclotomicNorms.Fbar p) : Prop :=
  ∀ y : Ω, y ^ (p ^ d - 1) = (p : Ω) → NT.redThrough A κ (σ y / y) = z
def labPol (teich : Formalism.CyclotomicNorms.Fbar p →* ℂ) (f : (ZMod p)[X]) (j : ℕ) : ℂ[X] :=
  ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (teich x ^ j)).prod
def LevelOf (f : (ZMod p)[X]) (d : ℕ) : Prop := 0 < d ∧ ∀ x ∈ Formalism.CyclotomicNorms.rootsBar f, x ^ (p ^ d - 1) = 1
def IsLabelOf (A : ValuationSubring Ω) (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar p)
    (teich : Formalism.CyclotomicNorms.Fbar p →* ℂ) (I : Set (Ω ≃ₐ[E] Ω)) (n : ℕ) (P : (Ω ≃ₐ[E] Ω) → ℂ[X]) (f : (ZMod p)[X]) : Prop :=
  f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0 ∧
    ∀ σ ∈ I, ∀ d j, LevelOf f d → TameVal A κ σ d (ζ d ^ j) → P σ = labPol teich f j
variable {A : ValuationSubring Ω} {κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p} {ζ : ℕ → Formalism.CyclotomicNorms.Fbar p}
  {teich : Formalism.CyclotomicNorms.Fbar p →* ℂ} {I : Set (Ω ≃ₐ[E] Ω)} {n : ℕ} {P : (Ω ≃ₐ[E] Ω) → ℂ[X]} {f f' : (ZMod p)[X]}
end lab
end Formalism.L2.NG


