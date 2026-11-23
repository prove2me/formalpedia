-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:32.59131+00:00
-- url     : https://prove2.me/theorems/3f44e622-03bb-4768-aabc-d349539c5349
-- title:
--   Cls Gain BSt
-- statement:
--   Definitions and structural lemmas for Cls Gain BSt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainBSt.lean

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
open Matrix
namespace PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
abbrev Mc (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
def cpart (i j : Fin n) (F : Mc n → ℂ) : Mc n → ℂ := fun b => fderiv ℂ F b (Matrix.single i j 1)
def word (L : List (Fin n × Fin n)) (F : Mc n → ℂ) : Mc n → ℂ := L.foldr (fun ij g => cpart ij.1 ij.2 g) F
def DeltaC (F : Mc n → ℂ) : Mc n → ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.finRange n).foldr (fun k g => cpart (σ k) k g) F
def Fr (s : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (b : Mc n) : ℂ :=
  (1 - (Complex.I * s) • b)⁻¹.det ^ p * (1 + (Complex.I * s) • b)⁻¹.det ^ q *
    MvPolynomial.eval (fun k => if k.1 then (1 + (Complex.I * s) • b)⁻¹ k.2.1 k.2.2 else (1 - (Complex.I * s) • b)⁻¹ k.2.1 k.2.2) R
def Ugood (s : ℂ) : Set (Mc n) := {b | IsUnit (1 - (Complex.I * s) • b).det ∧ IsUnit (1 + (Complex.I * s) • b).det}
def pdisc (b₀ : Mc n) (ρ : Fin n → Fin n → ℝ) : Set (Mc n) := {b | ∀ i j, ‖b i j - b₀ i j‖ ≤ ρ i j}
def CauchyW : Prop :=
  ∀ (n : ℕ) (F : Mc n → ℂ) (U : Set (Mc n)), IsOpen U → ContDiffOn ℂ (⊤ : ℕ∞) F U →
    ∀ (b₀ : Mc n) (ρ : Fin n → Fin n → ℝ), (∀ i j, 0 < ρ i j) → pdisc b₀ ρ ⊆ U →
    ∀ M : ℝ, (∀ b ∈ pdisc b₀ ρ, ‖F b‖ ≤ M) → ∀ L : List (Fin n × Fin n),
      ‖word L F b₀‖ ≤ (L.map fun ij => (L.length : ℝ) / ρ ij.1 ij.2).prod * M
def Invar : Prop :=
  ∀ (n : ℕ) (F : Mc n → ℂ) (U : Set (Mc n)), IsOpen U → ContDiffOn ℂ (⊤ : ℕ∞) F U →
    ∀ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ N : ℕ, ∀ b, k * b * kᴴ ∈ U →
      (DeltaC^[N] (fun c => F (k * c * kᴴ))) b = (DeltaC^[N] F) (k * b * kᴴ)
def PBound : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ),
    IsOpen (Ugood (n := n) s) ∧ ContDiffOn ℂ (⊤ : ℕ∞) (Fr s p q R) (Ugood s) ∧
    ∃ (c₀ C : ℝ), 0 < c₀ ∧ ∀ (k : Mc n), k ∈ Matrix.unitaryGroup (Fin n) ℂ → ∀ (lam : Fin n → ℝ),
      ∀ b ∈ pdisc (Matrix.diagonal fun i => (lam i : ℂ)) (fun i j => c₀ * Real.sqrt ((1 + |lam i|) * (1 + |lam j|))),
        k * b * kᴴ ∈ Ugood s ∧ ‖Fr s p q R (k * b * kᴴ)‖ ≤ C * (∏ i, (1 + |lam i|)) ^ (-((p + q : ℕ) : ℝ))
def Link : Prop :=
  ∀ (n : ℕ) (F : Mc n → ℂ) (U : Set (Mc n)), IsOpen U → ContDiffOn ℂ (⊤ : ℕ∞) F U → (∀ y, herm y ∈ U) →
    (∀ N y, (Delta^[N] (fun y => F (herm y))) y = (DeltaC^[N] F) (herm y)) ∧
    ∀ N : ℕ, ∀ b ∈ U, (DeltaC^[N] F) b = ∑ τ : Fin N → Equiv.Perm (Fin n),
      ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ) *
        word ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)) F b
end PositivityTheory.Rg.Sw.WR.K.GB


