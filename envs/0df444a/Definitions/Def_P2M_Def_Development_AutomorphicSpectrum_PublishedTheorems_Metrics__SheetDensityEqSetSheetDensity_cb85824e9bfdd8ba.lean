-- Prove2me | Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__SheetDensityEqSetSheetDensity_cb85824e9bfdd8ba
-- name    : P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__SheetDensityEqSetSheetDensity_cb85824e9bfdd8ba
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:57.088093+00:00
-- url     : https://prove2.me/theorems/cdcd0145-1a61-4bd4-8a0c-21e2278580c7
-- title:
--   Sheet Density Eq Set Sheet Density
-- statement:
--   Definitions and structural lemmas for Sheet Density Eq Set Sheet Density, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Metrics₂/SheetDensityEqSetSheetDensity.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Pub
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
namespace CxInt
section Integral
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
def setFibre (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (y : Fin e → ℂ) : Set (((k : K) → ι k) → ℂ) :=
  {w | ∃ z ∈ S, segre z = w ∧ Ψ w = Fin.cons 1 y}
def IsSetSheet (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) : Prop :=
  segre (γ y) = w ∧ ∀ᶠ y' in 𝓝 y,
    DifferentiableAt ℂ γ y' ∧ γ y' ∈ S ∧ Ψ (segre (γ y')) = Fin.cons 1 y'
def setSheetDensity (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : ℝ := by
  classical
  exact if hγ : ∃ γ, IsSetSheet S Ψ y w γ then
    g (hγ.choose y) * maDensity (fun j y' => φ j (hγ.choose y')) y
  else 0
def setIntegralAt (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) : ℝ :=
  ∫ y, ∑ᶠ w ∈ setFibre S Ψ y, setSheetDensity S Ψ φ g y w
def IsSetGoodProj (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Prop :=
  ∀ z ∈ S, Ψ (segre z) ≠ 0
def setIntegral (S : Set ((Σ k, ι k) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : ℝ := by
  classical
  exact if hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsSetGoodProj S Ψ then
    setIntegralAt S hΨ.choose φ g
  else 0
def logNormC (A : HermLine ι) (s : MRingOver ℂ ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log (‖eval z s‖ / A.h z)
def IsCxVar (Q : Ideal (MRingOver ℂ ι)) (d : ℕ) : Prop :=
  Nonempty K ∧ IsMultiProjPrime Q ∧
    ringKrullDim (MRingOver ℂ ι ⧸ Q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)
end Integral
end CxInt
open CxInt in

def PoincareLelongC : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRingOver ℂ ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A B : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → (∀ k, A.a k = a k) → IsMultiHomog s a → s ∉ Q →
    setIntegral (ReciprocityTheory.AnForm.R.conePts Q) (Fin.cons (fun z => Real.log (B.h z)) (pot L))
        (logNormC A s) =
      (∑ᶠ W ∈ divSupp Q s,
          (multAt (Q ⊔ Ideal.span {s}) W : ℝ) *
            setIntegral (ReciprocityTheory.AnForm.R.conePts W) (pot L) (fun z => Real.log (B.h z))) -
        setIntegral (ReciprocityTheory.AnForm.R.conePts Q) (Fin.cons (fun z => Real.log (A.h z)) (pot L))
          (fun z => Real.log (B.h z))
end GlobalTheory.CompanionTheory.Ar.Pub


