-- Prove2me | Definitions.Def_ConnesGreen_original_quartet
-- name    : ConnesGreen_original_quartet
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-08T06:21:02.987421+00:00
-- url     : https://prove2.me/theorems/004b605b-701d-4ff1-8d1d-ae8bbf13ec2c
-- title:
--   Original actual-zero reflection/conjugation quartet and packet values
-- statement:
--   Exact unchanged native conjugateZero, quartet and packetValues bodies. Analytic conjugation proof uses existing certified Zeta23 Schwarz reflection; subtype proof terms are proof-irrelevant. The actual zeta-zero carrier, native reflectedZero and orbit are preserved. No separation or RH premise.
-- source:
--   WeilDefect/Connes/QuartetSeparation.lean at 68011f0aa80779d1735ecbe344b0314d03cd3de5; exact definition bodies.

import Definitions.Def_ConnesGreen_RG0_original_actors
set_option autoImplicit false
open Complex ConnesRZ ConnesRZFrontier
noncomputable section
namespace ConnesRZQuartet
lemma critical_conj (s : ℂ) (hs : IsCriticalZero s) : IsCriticalZero ((starRingEnd ℂ) s) := by
  have hne : s ≠ 1 := by
    intro h
    have hh := hs.2.2
    simp [h] at hh
  refine ⟨?_, ?_, ?_⟩
  · rw [Zeta23.riemannZeta_conj hne, hs.1]
    simp
  · simpa using hs.2.1
  · simpa using hs.2.2

def conjugateZero (ρ : CriticalZeros) : CriticalZeros :=
  ⟨(starRingEnd ℂ) ρ.1, critical_conj ρ.1 ρ.2⟩

@[simp] lemma conjugateZero_val (ρ : CriticalZeros) :
    (conjugateZero ρ).1 = (starRingEnd ℂ) ρ.1 := rfl

@[simp] lemma conjugateZero_involutive (ρ : CriticalZeros) :
    conjugateZero (conjugateZero ρ) = ρ := by
  apply Subtype.ext
  simp

lemma reflection_conjugation (ρ : CriticalZeros) :
    reflectedZero (conjugateZero ρ) = conjugateZero (reflectedZero ρ) := by
  apply Subtype.ext
  simp [mirror]

/-- The selected actor is exactly the reflection/conjugation orbit of the actual
zeta zero. It is fixed throughout interpolation and convolution amplification. -/
def quartet (ρ : CriticalZeros) : Finset CriticalZeros :=
  {ρ, conjugateZero ρ, reflectedZero ρ, conjugateZero (reflectedZero ρ)}

lemma mem_quartet (ρ : CriticalZeros) : ρ ∈ quartet ρ := by simp [quartet]

lemma quartet_reflection_closed (ρ : CriticalZeros) :
    ∀ τ ∈ quartet ρ, reflectedZero τ ∈ quartet ρ := by
  intro τ hτ
  simp only [quartet, Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl
  · simp [quartet]
  · simp [quartet, reflection_conjugation]
  · simp [quartet]
  · simp [quartet, reflection_conjugation]

/-- Real prescribed values, conjugation compatible and opposite on reflected pairs. -/
def packetValues (s z : ℂ) : ℂ := if z.re = s.re then 1 else -1


end ConnesRZQuartet


