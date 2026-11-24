-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:31.730919+00:00
-- url     : https://prove2.me/theorems/68f0cc42-3ab3-41c1-968a-751e67680cdf
-- title:
--   Cls Gain St
-- statement:
--   Definitions and structural lemmas for Cls Gain St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainSt.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
namespace PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
abbrev MC (n : ℕ) := Fin n → Fin n → ℂ
def eU (a b : Fin n) : MC n := fun i j => if i = a ∧ j = b then 1 else 0
def cay (F : MC n → ℂ) (B : MC n) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * iteratedFDeriv ℂ n F B (fun k => eU (σ k) k)
def OmS (s : ℂ) : Set (MC n) :=
  {B | (1 - (Complex.I * s) • Matrix.of B).det ≠ 0 ∧ (1 + (Complex.I * s) • Matrix.of B).det ≠ 0 ∧
    (1 + Matrix.of B * Matrix.of B).det ∈ Complex.slitPlane}
def clsC (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (B : MC n) : ℂ :=
  Complex.exp (-z * Complex.log (1 + Matrix.of B * Matrix.of B).det) *
    ((1 - (Complex.I * s) • Matrix.of B)⁻¹).det ^ p * ((1 + (Complex.I * s) • Matrix.of B)⁻¹).det ^ q *
    MvPolynomial.eval (fun k => if k.1 then (1 + (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2
      else (1 - (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2) R
def Ext : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → IsOpen (OmS (n := n) s) ∧ (∀ y : E n, (herm y : MC n) ∈ OmS s) ∧
    ∀ (z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ),
      AnalyticOnNhd ℂ (clsC s z p q R) (OmS s) ∧ ∀ y, clsC s z p q R (herm y) = cls s z p q R y
def Chain : Prop :=
  ∀ (n : ℕ) (U : Set (MC n)) (F : MC n → ℂ), IsOpen U → (∀ y : E n, (herm y : MC n) ∈ U) → AnalyticOnNhd ℂ F U →
    ∀ N y, (Delta^[N] (fun y : E n => F (herm y))) y = (cay^[N] F) (herm y)
def ZPoly : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (p q N : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ),
    ∃ c : ℕ → MC n → ℂ, (∀ j, AnalyticOnNhd ℂ (c j) (OmS s)) ∧ ∀ (z : ℂ) (B : MC n), B ∈ OmS s →
      (cay^[N] (clsC s z p q R)) B =
        Complex.exp (-z * Complex.log (1 + Matrix.of B * Matrix.of B).det) * ∑ j ∈ Finset.range (n * N + 1), z ^ j * c j B
def aff (B₀ : MC n) (A₁ A₂ : Matrix (Fin n) (Fin n) ℂ) (K : MC n) : MC n := fun i j => B₀ i j + (A₁ * Matrix.of K * A₂) i j
def Scale : Prop :=
  ∀ (n : ℕ) (F : MC n → ℂ) (B₀ : MC n) (A₁ A₂ : Matrix (Fin n) (Fin n) ℂ) (U V : Set (MC n)), IsOpen U → IsOpen V →
    AnalyticOnNhd ℂ F U → (∀ K ∈ V, aff B₀ A₁ A₂ K ∈ U) →
    ∀ N, ∀ K ∈ V, (cay^[N] (fun K : MC n => F (aff B₀ A₁ A₂ K))) K =
      (A₁.det * A₂.det) ^ N * (cay^[N] F) (aff B₀ A₁ A₂ K)
def Cauchy : Prop :=
  ∀ (n N : ℕ) (ρ : ℝ), 0 < ρ → ∃ C : ℝ, ∀ (G : MC n → ℂ) (U : Set (MC n)) (M : ℝ), IsOpen U →
    {K : MC n | ∀ i j, ‖K i j‖ ≤ ρ} ⊆ U → AnalyticOnNhd ℂ G U → (∀ K : MC n, (∀ i j, ‖K i j‖ ≤ ρ) → ‖G K‖ ≤ M) →
      ‖(cay^[N] G) 0‖ ≤ C * M
def Sup : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∃ ρ : ℝ, 0 < ρ ∧ ∀ (z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ),
    ∃ C : ℝ, ∀ y : E n, ∃ A : Matrix (Fin n) (Fin n) ℂ, A.det ^ 2 = ((dP y : ℝ) : ℂ) ^ ((1 : ℂ) / 2) ∧
      ∃ U : Set (MC n), IsOpen U ∧ {K : MC n | ∀ i j, ‖K i j‖ ≤ ρ} ⊆ U ∧
        (∀ K ∈ U, aff (herm y) A A K ∈ OmS s) ∧
        ∀ K : MC n, (∀ i j, ‖K i j‖ ≤ ρ) →
          ‖clsC s z p q R (aff (herm y) A A K)‖ ≤
            C * (dP y) ^ (-(z.re + (p + q : ℝ) / 2))
end PositivityTheory.Rg.Sw.WR.Z


