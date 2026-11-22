-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:36:21.568724+00:00
-- url     : https://prove2.me/theorems/03a8123c-6e11-4082-9bcd-83b5c3bedbb3
-- title:
--   Moderate Coefficient Positivity
-- statement:
--   Definitions and structural lemmas for Moderate Coefficient Positivity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ModerateCoefficientPositivity.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MeasureTheory
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Data
variable {r : ℕ} (X : Data E r)
def flowMatV (e : Fin r → ℂ) (τ : X.Ψ) (s : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => (if a = b then 1 else 0) -
    I * X.c τ * s * e a * ∑ k, τ.1 (X.Gm b k) * conj (e k)
def flowV (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => (X.flowMatV (e τ) τ (s τ) * mat x τ : Matrix (Fin r) (Fin r) ℂ)
def ttV (e : X.Ψ → Fin r → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) : ℝ := 1 / (X.c τ * X.maj x τ (e τ))
def IsIsoV (e : X.Ψ → Fin r → ℂ) : Prop := ∀ τ : X.Ψ, hermC τ.1 X.Gm (e τ) (e τ) = 0 ∧ e τ ≠ 0
def IsIso (ξ : Fin r → E) : Prop := ξ ∈ X.Λ ∧ herm X.Gm ξ ξ = 0 ∧ ξ ≠ 0
def nfac (la : Wt X.Ψ r) (x : Frame X.Ψ r) : ℝ :=
  ∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)
def spread (la : Wt X.Ψ r) (τ : X.Ψ) : ℝ :=
  ((⨆ i, (la τ i : ℝ)) - ⨅ i, (la τ i : ℝ))
def chiOrd (la : Wt X.Ψ r) : ℕ := (X.χ_fin la).choose
def periods (la : Wt X.Ψ r) : AddSubgroup (X.Ψ → ℝ) :=
  AddSubgroup.closure {p | ∃ a : E, cc a = a ∧ IsIntegral ℤ a ∧
    p = fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re}
open Classical in

def fj (la : Wt X.Ψ r) (ξ : Fin r → E) (ν : X.Ψ → ℝ) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℂ :=
  if (∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k) then
  if h : ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧ IsAddFundamentalDomain (X.periods la) D volume ∧
      0 < volume D ∧ volume D < ⊤ then
    ((volume h.choose).toReal : ℂ)⁻¹ * ∫ s in h.choose,
      P (X.flow ξ (fun τ => (s τ : ℂ)) x) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)
  else 0
  else 0
def IsModerate (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∃ C A : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C * X.la1 x ^ (-A)
def IsBddSec (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  X.IsSec la P ∧ ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C
def SS (la : Wt X.Ψ r) : Set (Frame X.Ψ r → ℂ) :=
  {P | X.IsBddSec la P ∧ ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, X.fj la ξ 0 P x = 0}
def SSgt (la : Wt X.Ψ r) (c : ℝ) : Set (Frame X.Ψ r → ℂ) :=
  {P | P ∈ X.SS la ∧ ∀ ξ, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∑ τ, ν τ ≤ c → ∀ x ∈ X.dom, X.fj la ξ ν P x = 0}
end Data
def FlowDomainCriterion : Prop :=
  ∀ (r : ℕ) (X : Data E r) (e : X.Ψ → Fin r → ℂ), X.IsIsoV e → ∀ x ∈ X.dom, ∀ s : X.Ψ → ℂ,
    (X.flowV e s x ∈ X.dom ↔ ∀ τ, 0 < 1 + (s τ).im / X.ttV e x τ) ∧
    (X.flowV e s x ∈ X.dom → ∀ τ, X.ttV e (X.flowV e s x) τ = X.ttV e x τ + (s τ).im)
def FlowNormRatio : Prop :=
  ∀ (r : ℕ) (X : Data E r) (e : X.Ψ → Fin r → ℂ), X.IsIsoV e → ∀ (la : Wt X.Ψ r), ∀ x ∈ X.dom,
    ∀ s : X.Ψ → ℂ, X.flowV e s x ∈ X.dom →
    let q := fun τ => 1 + (s τ).im / X.ttV e x τ
    (∏ τ, min (q τ) (q τ)⁻¹ ^ (X.spread la τ / 2) ≤ X.nfac la x / X.nfac la (X.flowV e s x)) ∧
    X.nfac la x / X.nfac la (X.flowV e s x) ≤ ∏ τ, max (q τ) (q τ)⁻¹ ^ (X.spread la τ / 2)
def FourierJacobiExpansion : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P →
    ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, ∀ s : X.Ψ → ℂ, X.flow ξ s x ∈ X.dom →
      HasSum (fun ν : X.Ψ → ℝ => X.fj la ξ ν P x * cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ))
        (P (X.flow ξ s x))
def FlowMinimumLowerBound : Prop :=
  ∀ (r : ℕ) (X : Data E r) (B : ℝ), 0 ≤ B → ∃ C : ℝ, 0 < C ∧
    ∀ ξ : Fin r → E, X.IsIso ξ → ∀ x ∈ X.dom, (∀ τ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1) → ∀ s : X.Ψ → ℂ,
      (∀ τ, |(s τ).re| ≤ B) → X.flow ξ s x ∈ X.dom → ∀ μ : ℝ, 0 ≤ μ →
      (∀ τ, μ ≤ min (1 + (s τ).im / X.tt ξ x τ) (1 + (s τ).im / X.tt ξ x τ)⁻¹) →
      C⁻¹ * X.la1 x * Real.sqrt μ ≤ X.la1 (X.flow ξ s x)
def ModerateCoefficientPositivity : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (C A : ℝ), X.IsSec la P →
    (∀ x ∈ X.dom, X.pnorm la P x ≤ C * X.la1 x ^ (-A)) →
    (∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom, X.fj la ξ ν P x ≠ 0 → ∀ τ, 0 ≤ ν τ) ∧
    ∀ η : ℝ, 0 < η → η < 1 → ∃ Cη : ℝ, ∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom,
      (∀ τ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1) →
      ‖X.fj la ξ ν P x‖ * X.nfac la x ≤
        Cη * X.la1 x ^ (-A) * Real.exp (-4 * Real.pi * (1 - η) * ∑ τ, ν τ * X.tt ξ x τ)
def CoefficientConvolution : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la la' : Wt X.Ψ r) (P Q : Frame X.Ψ r → ℂ),
    X.IsSec la P → X.IsSec la' Q → X.IsModerate la P → X.IsModerate la' Q →
    ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, ∀ ν : X.Ψ → ℝ,
      HasSum (fun ν' : X.Ψ → ℝ => X.fj la ξ ν' P x * X.fj la' ξ (ν - ν') Q x)
        (X.fj (la + la') ξ ν (P * Q) x)
def SiegelSpaceAlgebra : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la la' : Wt X.Ψ r) (c : ℝ),
    (0 ∈ X.SS la ∧ (∀ P ∈ X.SS la, ∀ Q ∈ X.SS la, P + Q ∈ X.SS la) ∧
      ∀ (a : ℂ), ∀ P ∈ X.SS la, a • P ∈ X.SS la) ∧
    (∀ P ∈ X.SS la, ∀ Q, X.IsBddSec la' Q → P * Q ∈ X.SS (la + la')) ∧
    (0 ∈ X.SSgt la c ∧ (∀ P ∈ X.SSgt la c, ∀ Q ∈ X.SSgt la c, P + Q ∈ X.SSgt la c) ∧
      ∀ (a : ℂ), ∀ P ∈ X.SSgt la c, a • P ∈ X.SSgt la c) ∧
    ∀ P ∈ X.SSgt la c, ∀ Q, X.IsBddSec la' Q → P * Q ∈ X.SSgt (la + la') c
end
end ReciprocityTheory.ChartRestriction.G.FD


