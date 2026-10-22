-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P14
-- name    : QAlgorithms_Papers_Independent_Gap20_P14
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T20:29:31.641319+00:00
-- url     : https://prove2.me/theorems/0f9216f6-57e4-4a4e-a218-5954b8715797
-- title:
--   Definitions for Fundamental rate-loss tradeoff for optical quantum key distribution
-- statement:
--   The objects the formalized statements of *Fundamental rate-loss tradeoff for optical quantum key distribution* (arXiv:1504.06390) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `FiveBasis`: PDF p.4, Lemma 2, and p.10, Supplementary Note 1: the full five-register basis, with no independence or product restriction.
--   - `honestReduction`: PDF pp.4,10: the A,(B1,B2) reduction of the supplied five-party state. Both environment registers are traced out, each exactly once.
--   - `firstLinkReduction`: PDF pp.4,10: the (A,B2,E2),B1 reduction. E1 alone is traced out; E2 remains in the first legitimate party.
--   - `secondLinkReduction`: PDF pp.4,10: the (A,B1,E1),B2 reduction. E2 alone is traced out; E1 remains in the first legitimate party.
--   - `channelSquashedValues`: PDF p.3, definition discussion before Eq.(3): output squashed-entanglement values from all normalized mixed inputs, with a reference copy of the input. The imported state quantity is half the infimum of bit-valued CQMI over all positive finite extension dimensions, equivalent to all squashing channels of a fixed purification. No capacity or optimizing value is supplied as a parameter.
--   - `channelSquashedEntanglement`: PDF p.3, Eq.(3): the computed finite-input optimization. For the CPTP channels on positive finite systems in the theorem, its value set is nonempty and bounded by log2(dim I), so the real supremum has no junk-value behavior. Attainment and the pure-input reduction are conclusions of the theorem.
--   - `rateLossCurve`: PDF pp.2,5,6: the numerical upper-bound curve, in secret bits per mode. Its physical finite-formula domain is 0 <= eta < 1. At eta=1 this real formula has no asserted meaning; the singular endpoint is not used in any theorem here.
--   - `reverseCoherentCurve`: PDF p.5, Eq.(7), and p.6: the cited reverse-coherent-information lower curve in bits. This scalar expression is not a definition of an operational capacity. Its finite-formula domain is 0 <= eta < 1.
-- source:
--   Fundamental rate-loss tradeoff for optical quantum key distribution, arXiv:1504.06390v1, https://arxiv.org/abs/1504.06390v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

/-!
Takeoka, Guha, Wilde, arXiv:1504.06390v1.
Finite-dimensional entropic statements and the scalar high-loss asymptotics.
The operational and oscillator statements deferred in HARD.md are not modeled
by scalar capacity parameters or by finite-dimensional replacements.
Compilation is pending the authorized batch compilation stage.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P14

open Filter
open QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P12 (squashedEntanglement)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, Lemma 2, and p.10, Supplementary Note 1:
the full five-register basis, with no independence or product restriction. -/
abbrev FiveBasis (A B1 E1 B2 E2 : Type) := A × (B1 × (E1 × (B2 × E2)))

/-- PDF pp.4,10: the A,(B1,B2) reduction of the supplied five-party state.
Both environment registers are traced out, each exactly once. -/
def honestReduction {A B1 E1 B2 E2 : Type} [Fintype E1] [Fintype E2]
    (rho : Matrix (FiveBasis A B1 E1 B2 E2) (FiveBasis A B1 E1 B2 E2) ℂ) :
    Matrix (A × (B1 × B2)) (A × (B1 × B2)) ℂ :=
  fun x y => ∑ e1, ∑ e2,
    rho (x.1, (x.2.1, (e1, (x.2.2, e2))))
      (y.1, (y.2.1, (e1, (y.2.2, e2))))

/-- PDF pp.4,10: the (A,B2,E2),B1 reduction.
E1 alone is traced out; E2 remains in the first legitimate party. -/
def firstLinkReduction {A B1 E1 B2 E2 : Type} [Fintype E1]
    (rho : Matrix (FiveBasis A B1 E1 B2 E2) (FiveBasis A B1 E1 B2 E2) ℂ) :
    Matrix ((A × (B2 × E2)) × B1) ((A × (B2 × E2)) × B1) ℂ :=
  fun x y => ∑ e1,
    rho (x.1.1, (x.2, (e1, x.1.2))) (y.1.1, (y.2, (e1, y.1.2)))

/-- PDF pp.4,10: the (A,B1,E1),B2 reduction.
E2 alone is traced out; E1 remains in the first legitimate party. -/
def secondLinkReduction {A B1 E1 B2 E2 : Type} [Fintype E2]
    (rho : Matrix (FiveBasis A B1 E1 B2 E2) (FiveBasis A B1 E1 B2 E2) ℂ) :
    Matrix ((A × (B1 × E1)) × B2) ((A × (B1 × E1)) × B2) ℂ :=
  fun x y => ∑ e2,
    rho (x.1.1, (x.1.2.1, (x.1.2.2, (x.2, e2))))
      (y.1.1, (y.1.2.1, (y.1.2.2, (y.2, e2))))

/-- PDF p.3, definition discussion before Eq.(3): output squashed-entanglement
values from all normalized mixed inputs, with a reference copy of the input.
The imported state quantity is half the infimum of bit-valued CQMI over all
positive finite extension dimensions, equivalent to all squashing channels of
a fixed purification. No capacity or optimizing value is supplied as a parameter. -/
def channelSquashedValues {I O : Type} [Fintype I] [Fintype O]
    (N : Superop I O) : Set ℝ :=
  {v | ∃ rho : Matrix (I × I) (I × I) ℂ,
    IsDensityMatrix rho ∧ v = squashedEntanglement (idTensorSuperop N rho)}

/-- PDF p.3, Eq.(3): the computed finite-input optimization. For the CPTP
channels on positive finite systems in the theorem, its value set is nonempty
and bounded by log2(dim I), so the real supremum has no junk-value behavior.
Attainment and the pure-input reduction are conclusions of the theorem. -/
def channelSquashedEntanglement {I O : Type} [Fintype I] [Fintype O]
    (N : Superop I O) : ℝ := sSup (channelSquashedValues N)

/-- PDF pp.2,5,6: the numerical upper-bound curve, in secret bits per mode.
Its physical finite-formula domain is 0 <= eta < 1. At eta=1 this real formula
has no asserted meaning; the singular endpoint is not used in any theorem here. -/
def rateLossCurve (eta : ℝ) : ℝ :=
  Real.log ((1 + eta) / (1 - eta)) / Real.log 2

/-- PDF p.5, Eq.(7), and p.6: the cited reverse-coherent-information lower
curve in bits. This scalar expression is not a definition of an operational
capacity. Its finite-formula domain is 0 <= eta < 1. -/
def reverseCoherentCurve (eta : ℝ) : ℝ :=
  -Real.log (1 - eta) / Real.log 2

/-- Sanity: tracing one-dimensional environments retains every honest entry. -/
example {A B1 B2 : Type}
    (rho : Matrix (FiveBasis A B1 Unit B2 Unit) (FiveBasis A B1 Unit B2 Unit) ℂ)
    (x y : A × (B1 × B2)) :
    honestReduction rho x y =
      rho (x.1, (x.2.1, ((), (x.2.2, ()))))
        (y.1, (y.2.1, ((), (y.2.2, ())))) := by
  simp [honestReduction]

/-- Sanity: the first grouping retains all E2 coherences. -/
example {A B1 B2 E2 : Type}
    (rho : Matrix (FiveBasis A B1 Unit B2 E2) (FiveBasis A B1 Unit B2 E2) ℂ)
    (x y : (A × (B2 × E2)) × B1) :
    firstLinkReduction rho x y =
      rho (x.1.1, (x.2, ((), x.1.2))) (y.1.1, (y.2, ((), y.1.2))) := by
  simp [firstLinkReduction]

/-- Sanity: the second grouping retains all E1 coherences. -/
example {A B1 E1 B2 : Type}
    (rho : Matrix (FiveBasis A B1 E1 B2 Unit) (FiveBasis A B1 E1 B2 Unit) ℂ)
    (x y : (A × (B1 × E1)) × B2) :
    secondLinkReduction rho x y =
      rho (x.1.1, (x.1.2.1, (x.1.2.2, (x.2, ()))))
        (y.1.1, (y.1.2.1, (y.1.2.2, (y.2, ())))) := by
  simp [secondLinkReduction]

/-- Sanity: the identity channel preserves all reference off-diagonal blocks. -/
example {I : Type} (rho : Matrix (I × I) (I × I) ℂ) :
    idTensorSuperop (fun X : Matrix I I ℂ => X) rho = rho := by
  ext x y
  rfl

/-- Sanity: both scalar curves vanish at total loss. -/
example : rateLossCurve 0 = 0 ∧ reverseCoherentCurve 0 = 0 := by
  simp [rateLossCurve, reverseCoherentCurve]

end QAlgorithms.Papers.Independent.Gap20.P14


