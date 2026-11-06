-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
-- name    : OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:12:58.635468+00:00
-- url     : https://prove2.me/theorems/21a578f0-b3ea-4351-818c-62d4c9f0cecd
-- title:
--   Local Product Assembly
-- statement:
--   Definitions and structural lemmas for Local Product Assembly, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
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
namespace ActualEisensteinCubic
open ConcreteTraceCRT
open scoped ComplexConjugate
end ActualEisensteinCubic
namespace FourierBridge
open scoped ContDiff FourierTransform SchwartzMap
end FourierBridge
namespace AnalyticBridge
end AnalyticBridge
namespace FourierBridge
open scoped FourierTransform SchwartzMap
end FourierBridge
namespace AnalyticBridge
open scoped FourierTransform SchwartzMap
end AnalyticBridge
namespace PowerExtraction
end PowerExtraction
namespace ActualEisensteinCubic
section
open AddChar MulChar
noncomputable def localA5Kernel (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ)
    (j : ℕ) (σ : (O ⧸ P)ˣ) (ε x h : O ⧸ P) : ℂ :=
  let χ := canonicalSextic P hgood
  let q : ℂ := Nat.card (O ⧸ P)
  if h = 0 then (if j = 0 then 1 - q⁻¹ else 0)
  else q⁻¹ *
    (∑ t : O ⧸ P, (χ ^ j) t * ψ (-(h * t))) *
    (((χ⁻¹) ^ 2) ((σ : O ⧸ P) * h)) *
    ψ ((ε * x) * h⁻¹)
noncomputable def localA5Output (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ)
    (j : ℕ) (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) : ℂ :=
  let χ := canonicalSextic P hgood
  let q : ℂ := Nat.card (O ⧸ P)
  if j = 0 then
    -(((χ⁻¹) ^ 2) σ) *
      (q⁻¹ * ((χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x))
  else if j = 4 then
    (((χ⁻¹) ^ 2) σ) *
      (q⁻¹ * gaussSum (χ ^ 4) (ψ.mulShift (-1)) *
        (if ε * x = 0 then (Fintype.card (O ⧸ P)ˣ : ℂ) else -1))
  else
    ((χ⁻¹) ^ 2) σ *
      (q⁻¹ * gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        gaussSum (χ ^ (j + 2)) ψ * (χ ^ (j + 2))⁻¹ ε) *
      (χ ^ (j + 2))⁻¹ x
@[instance_reducible] noncomputable def crtIntersectionFintype
    {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hdistinct : Function.Injective (fun i => Ideal.span {p i})) :
    Fintype (O ⧸ ⨅ i, Ideal.span {p i}) := by
  classical
  letI (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  have hcop : Pairwise
      (fun i k => IsCoprime (Ideal.span {p i}) (Ideal.span {p k})) := by
    intro i k hik
    exact Ideal.isCoprime_of_isMaximal (hdistinct.ne hik)
  let e := Ideal.quotientInfRingEquivPiQuotient
    (fun i => Ideal.span {p i}) hcop
  exact Fintype.ofEquiv (∀ i, O ⧸ Ideal.span {p i}) e.symm.toEquiv
end
end ActualEisensteinCubic
namespace PoissonFirstLocal
def localA (ε : Bool) (p : ℕ) : ℕ := if ε then p else 1
def localC (parityBit ε₁ ε₂ : Bool) (p : ℕ) : ℕ :=
  if localE parityBit ε₁ ε₂ = 0 then 1 else p
def localCorrectionE (parityBit ε₁ ε₂ : Bool) (p : ℕ) : ℕ :=
  if parityBit then localA ε₁ p * localA ε₂ p else 1
def localS (parityBit : Bool) (p : ℕ) : ℕ := if parityBit then p else 1
def localJ2 (parityBit ε₁ ε₂ : Bool) (p : ℕ) : ℕ :=
  if !parityBit && ε₁ && ε₂ then p else 1
end PoissonFirstLocal
end
end OAI


