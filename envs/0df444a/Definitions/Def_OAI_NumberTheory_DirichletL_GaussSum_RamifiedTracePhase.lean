-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
-- name    : OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:15:50.100202+00:00
-- url     : https://prove2.me/theorems/43717d09-d7b5-44a3-924b-da45301b4e05
-- title:
--   Ramified Trace Phase
-- statement:
--   Definitions and structural lemmas for Ramified Trace Phase, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/RamifiedTracePhase.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_traceLambda
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span

set_option autoImplicit false
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
namespace TraceLambdaPhase
open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped ComplexConjugate
end TraceLambdaPhase
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE TraceLambdaPhase
theorem traceLambda_ne_zero : traceLambda ≠ 0 := by
  intro h
  have hh := congrArg eisEmbedding h
  rw [eisEmbedding_traceLambda, map_zero] at hh
  exact eisLam_ne_zero hh
noncomputable def quadraticGammaTraceLambda : ℂ := by
  let c : O := traceLambda
  let hc : c ≠ 0 := traceLambda_ne_zero
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  exact (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) / (‖eisEmbedding c‖ : ℂ)
end ActualEisensteinCubic
namespace PoissonFirstLocal
open scoped Classical
def quotientUnitMask {R : Type*} [CommRing R] (z : R) : ℂ :=
  if IsUnit z then 1 else 0
def oldFactorRing {R : Type*} [CommRing R]
    (side parityBit ε₁ ε₂ : Bool) (z : R) (χ : MulChar R ℂ) : ℂ :=
  let q := χ z
  quotientUnitMask z * q ^ (4 * bit (if side then ε₂ else ε₁)) *
    q ^ (if side then cExp₂ parityBit ε₁ ε₂ else cExp₁ parityBit ε₁ ε₂) *
    q ^ EExp parityBit ε₁ ε₂
def newFactorRing {R : Type*} [CommRing R]
    (parityBit ε₁ ε₂ : Bool) (z : R) (χ : MulChar R ℂ) : ℂ :=
  if retained parityBit ε₁ ε₂ then (χ z) ^ 4 else quotientUnitMask z
end PoissonFirstLocal
namespace ActualEisensteinCubic
section
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE TraceLambdaPhase
noncomputable def quadraticGammaNegTraceLambda : ℂ := by
  let c : O := -traceLambda
  let hc : c ≠ 0 := neg_ne_zero.mpr traceLambda_ne_zero
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  exact (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) / (‖eisEmbedding c‖ : ℂ)
end
noncomputable def finiteSquarefreeRow
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (u : O) : ℂ :=
  ∏ i ∈ S, canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) u)
end ActualEisensteinCubic
namespace AnalyticBridge
end AnalyticBridge
namespace ShortDraftCusp
variable {R : Type*} [CommRing R]
def cuspMatrix (a b c d : R) : Matrix (Fin 2) (Fin 2) R := !![a,b;c,d]
def unramifiedH (u : R) : Matrix (Fin 2) (Fin 2) R := U u * E
def unramifiedHInv (u : R) : Matrix (Fin 2) (Fin 2) R := !![0,1;-1,u]
end ShortDraftCusp
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
noncomputable def breveGaussianFourTerms (a b : ℤ) : ℂ :=
  let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
  (ShortDraftTrace.breveE (0 : ℂ) +
      ShortDraftTrace.breveE (((-c) / eisLam) / 4) +
      ShortDraftTrace.breveE (((-c * omega3 ^ 2) / eisLam) / 4) +
      ShortDraftTrace.breveE (((-c * (1 + omega3) ^ 2) / eisLam) / 4)) / 2
end ActualEisensteinCubic
end
end OAI


