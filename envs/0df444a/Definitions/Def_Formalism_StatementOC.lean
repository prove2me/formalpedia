-- Prove2me | Definitions.Def_Formalism_StatementOC
-- name    : Formalism_StatementOC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:55.610827+00:00
-- url     : https://prove2.me/theorems/3d4a178d-fca3-465c-8a81-65979296b5ae
-- title:
--   Statement OC
-- statement:
--   Definitions and structural lemmas for Statement OC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/StatementOC.lean

import Definitions.Def_Formalism_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace Formalism
open ArithmeticFunction in

def Sz (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1)
def Gz (x : ℝ) : ℝ := Sz x - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x
open ArithmeticFunction in

def Schi {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (χ n).re * (x / n - 1)
def Gchi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  Schi χ x + (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re * x
def OCStep : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → (∀ n : ℕ, (χ n).im = 0) →
  ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → -C * x ^ θ ≤ Gz x - Gchi χ x) →
  (∀ σ : ℝ, θ < σ → σ < 1 → DirichletCharacter.LFunction χ σ ≠ 0) ∧
  ∀ s : ℂ, θ < s.re → s ≠ 1 →
    analyticOrderAt riemannZeta s = analyticOrderAt (DirichletCharacter.LFunction χ) s
def OCStepUpper : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → (∀ n : ℕ, (χ n).im = 0) →
  ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∀ σ : ℝ, θ < σ → σ < 1 → DirichletCharacter.LFunction χ σ ≠ 0) →
  (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → Gz x - Gchi χ x ≤ C * x ^ θ) →
  ∀ s : ℂ, θ < s.re → s ≠ 1 →
    analyticOrderAt riemannZeta s = analyticOrderAt (DirichletCharacter.LFunction χ) s
def OCAvg : Prop :=
  ∀ (ι : Type) [Fintype ι] (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ),
  (∀ i, χ i ≠ 1) → (∀ i (n : ℕ), (χ i n).im = 0) → (∀ i, 0 ≤ w i) → 0 < ∑ i, w i →
  ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → -C * x ^ θ ≤ ∑ i, w i * (Gz x - Gchi (χ i) x)) →
  (∀ i, 0 < w i → ∀ σ : ℝ, θ < σ → σ < 1 → DirichletCharacter.LFunction (χ i) σ ≠ 0) ∧
  ∀ s : ℂ, θ < s.re → s ≠ 1 →
    analyticOrderAt riemannZeta s ≠ ⊤ ∧
    (∀ i, analyticOrderAt (DirichletCharacter.LFunction (χ i)) s ≠ ⊤) ∧
    (∑ i, w i) * (analyticOrderNatAt riemannZeta s : ℝ) =
      ∑ i, w i * (analyticOrderNatAt (DirichletCharacter.LFunction (χ i)) s : ℝ)
def OCAvgUpper : Prop :=
  ∀ (ι : Type) [Fintype ι] (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ),
  (∀ i, χ i ≠ 1) → (∀ i (n : ℕ), (χ i n).im = 0) → (∀ i, 0 ≤ w i) → 0 < ∑ i, w i →
  ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∀ i, 0 < w i → ∀ σ : ℝ, θ < σ → σ < 1 → DirichletCharacter.LFunction (χ i) σ ≠ 0) →
  (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → ∑ i, w i * (Gz x - Gchi (χ i) x) ≤ C * x ^ θ) →
  ∀ s : ℂ, θ < s.re → s ≠ 1 →
    analyticOrderAt riemannZeta s ≠ ⊤ ∧
    (∀ i, analyticOrderAt (DirichletCharacter.LFunction (χ i)) s ≠ ⊤) ∧
    (∑ i, w i) * (analyticOrderNatAt riemannZeta s : ℝ) =
      ∑ i, w i * (analyticOrderNatAt (DirichletCharacter.LFunction (χ i)) s : ℝ)
def RiemannHypothesisOfLowerBounds : Prop :=
  ∀ (ι : Type) (N : ι → ℕ) [∀ i, NeZero (N i)] (χ : (i : ι) → DirichletCharacter ℂ (N i)),
  (∀ i, χ i ≠ 1) → (∀ i (n : ℕ), (χ i n).im = 0) →
  (∀ i, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      -C * x ^ ((1 : ℝ) / 2 + ε) ≤ Gz x - Gchi (χ i) x) →
  (∀ s : ℂ, 1 / 2 < s.re → ∃ i, DirichletCharacter.LFunction (χ i) s ≠ 0) →
  RiemannHypothesis
end Formalism


