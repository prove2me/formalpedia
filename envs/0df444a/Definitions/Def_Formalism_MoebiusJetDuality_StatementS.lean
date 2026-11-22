-- Prove2me | Definitions.Def_Formalism_MoebiusJetDuality_StatementS
-- name    : Formalism_MoebiusJetDuality_StatementS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:03.209794+00:00
-- url     : https://prove2.me/theorems/de46259d-db77-451a-86ef-e37b9cdb5b6a
-- title:
--   Statement S
-- statement:
--   Definitions and structural lemmas for Statement S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MoebiusJetDuality/StatementS.lean

import Definitions.Def_Formalism_MoebiusJetDuality_EvDualJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MJ
open MvPolynomial
def partialD {n : ℕ} (i : Fin n) (f : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  fun z => deriv (fun t => f (Function.update z i t)) (z i)
def partialPow {n : ℕ} (α : Fin n →₀ ℕ) (f : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  (List.finRange n).foldr (fun i g => (partialD i)^[α i] g) f
def ajetCoeff {n : ℕ} (f : (Fin n → ℂ) → ℂ) (α : Fin n →₀ ℕ) : ℂ :=
  partialPow α f 0 / (mfac α : ℂ)
def aevOp {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (f : (Fin n → ℂ) → ℂ) : ℂ :=
  ∑ α ∈ P.support, coeff α P * partialPow α f 0
def AJetPoly : Prop :=
  ∀ (n : ℕ) (F : MvPolynomial (Fin n) ℂ) (α : Fin n →₀ ℕ),
    ajetCoeff (fun z => eval z F) α = coeff α F
def AEvPoly : Prop :=
  ∀ (n : ℕ) (P F : MvPolynomial (Fin n) ℂ),
    aevOp P (fun z => eval z F) = evOp P F
def AEvSubst : Prop :=
  ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℂ),
    AnalyticAt ℂ f 0 →
      aevOp P (fun z => f (g.mulVec z)) = aevOp (linSubst g.transpose P) f
def AJetMul : Prop :=
  ∀ (n : ℕ) (f h : (Fin n → ℂ) → ℂ) (α : Fin n →₀ ℕ),
    AnalyticAt ℂ f 0 → AnalyticAt ℂ h 0 →
      ajetCoeff (fun z => f z * h z) α =
        ∑ βγ ∈ Finset.HasAntidiagonal.antidiagonal α, ajetCoeff f βγ.1 * ajetCoeff h βγ.2
def AJetInjective : Prop :=
  ∀ (n : ℕ) (f : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)),
    IsOpen U → IsPreconnected U → (0 : Fin n → ℂ) ∈ U → AnalyticOnNhd ℂ f U →
      (∀ α : Fin n →₀ ℕ, partialPow α f 0 = 0) → Set.EqOn f 0 U
end Formalism.MJ


