-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RealMpData
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_RealMpData
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:54.252245+00:00
-- url     : https://prove2.me/theorems/0476d9a9-27bb-4b88-b6d2-01e1581aee59
-- title:
--   Real Mp Data
-- statement:
--   Definitions and structural lemmas for Real Mp Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/RealMpData.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix
open scoped Real SchwartzMap ComplexConjugate ContDiff
namespace GlobalTheory.CompanionTheory.Hypotheses₂
open GlobalTheory.RealWeil
variable {l : Type} [Fintype l] [DecidableEq l]
def RealMpData {G : Type} [Group G] [TopologicalSpace G]
    (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l))
    (omS : G →* (Sch l →L[ℂ] Sch l)) : Prop :=
  (IsCoveringMap pr ∧ Function.Surjective pr ∧
    ∃ ε : G, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f) ∧
  (∀ f : L2 l, Continuous fun g => om g f) ∧
  (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
    om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) ∧
  (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) ∧
  (∀ (k : ℕ) (γ : (Fin k → ℝ) → G), Continuous γ →
    (∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b) →
    ∀ f : Sch l, ContDiff ℝ ∞ fun t => om (γ t) (f.toLp 2)) ∧
  (∀ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∃ γ : ℝ → G, Continuous γ ∧ γ 0 = 1 ∧ (∀ s t, γ (s + t) = γ s * γ t) ∧
    (∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) ∧
    ∀ f : Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2)) ((quad X f).toLp 2) 0)
def FlowOf {G : Type} [Group G] [TopologicalSpace G] (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l))
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (γ : ℝ → G) : Prop :=
  Continuous γ ∧ γ 0 = 1 ∧ (∀ s t, γ (s + t) = γ s * γ t) ∧
    ∀ f : Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2)) ((quad X f).toLp 2) 0
omit [DecidableEq l] in

def gaussFun (Z : Matrix l l ℂ) (x : EuclideanSpace ℝ l) : ℂ :=
  cexp (-(π : ℂ) * ∑ j, ∑ k, Z j k * (x j : ℂ) * (x k : ℂ))
omit [DecidableEq l] in

def GaussAdm (Z : Matrix l l ℂ) : Prop := Zᵀ = Z ∧ (Z.map Complex.re).PosDef
omit [Fintype l] [DecidableEq l] in

def realify (Z : Matrix l l ℂ) : Matrix (l ⊕ l) (l ⊕ l) ℝ :=
  fromBlocks (Z.map Complex.re) (-(Z.map Complex.im)) (Z.map Complex.im) (Z.map Complex.re)
omit [Fintype l] [DecidableEq l] in

def dilX (S : Matrix l l ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ := fromBlocks S 0 0 (-S)
omit [Fintype l] [DecidableEq l] in

def chirpX (C : Matrix l l ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ := fromBlocks 0 0 C 0
end GlobalTheory.CompanionTheory.Hypotheses₂


