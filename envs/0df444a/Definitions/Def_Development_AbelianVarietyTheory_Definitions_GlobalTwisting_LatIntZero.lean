-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LatIntZero
-- name    : Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LatIntZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:34.078744+00:00
-- url     : https://prove2.me/theorems/084ab575-2e40-436e-8c4f-a4d867913e9b
-- title:
--   Lat Int Zero
-- statement:
--   Definitions and structural lemmas for Lat Int Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LatIntZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.MomN
open GlobalTheory.MomOne
variable {q : ℕ} [Fact q.Prime] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
def IsMom (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] (v : κ → V) (G : V → ℂ) (μ : C(κ → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]) : Prop :=
  ∀ (k : ℕ) (j : Fin k → κ) (f : C(κ → ℤ_[q], ℂ_[q])), (∀ a, f a = ∏ l, zc (a (j l))) →
    ι (iteratedFDeriv ℂ k G 0 fun l => v (j l)) = μ f
def MomInt (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] (v : κ → V) (G : V → ℂ) : Prop :=
  ∃ μ : C(κ → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q], ‖μ‖ ≤ 1 ∧ IsMom ι v G μ
def LatInt (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (Λ : AddSubgroup V) (G : V → ℂ) : Prop :=
  ∀ (κ : Type) [Fintype κ] (v : κ → V), (∀ i, v i ∈ Λ) → MomInt ι (fun i => ι.symm ω • v i) G
def monoJet {κ : Type} [Fintype κ] (v : κ → V) (G : V → ℂ) (m : κ →₀ ℕ) : ℂ :=
  iteratedFDeriv ℂ m.toMultiset.toList.length G 0 fun l => v (m.toMultiset.toList.get l)
def mahler {κ : Type} [Fintype κ] (v : κ → V) (G : V → ℂ) (n : κ → ℕ) : ℂ :=
  let P : MvPolynomial κ ℂ :=
    ∏ i, MvPolynomial.C (((n i).factorial : ℂ)⁻¹) * Polynomial.aeval (MvPolynomial.X i : MvPolynomial κ ℂ) (descPochhammer ℂ (n i))
  ∑ m ∈ P.support, P.coeff m * monoJet v G m
def Per (d : ℕ) (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]) : Prop :=
  IsTh d θ ∧ δ₀ ^ 12 = discr d ∧ δ₀ ≠ 0 ∧
  (∀ ι' : ℂ ≃+* ℂ_[q], ∃ Ω' : ℂ_[q], ‖Ω'‖ = 1 ∧ ThetaLaws ι' d (Ω' / ι' δ₀) θ) ∧
  ‖Ω‖ = 1 ∧ ThetaLaws ι d (Ω / ι δ₀) θ ∧ ∃ M : Mdl q, M.ι = ι ∧ IsOK d M.L ∧ M.MChart (Ω / ι δ₀)
end GlobalTheory.MomN


