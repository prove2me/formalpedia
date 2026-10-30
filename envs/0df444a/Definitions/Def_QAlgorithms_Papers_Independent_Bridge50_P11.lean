-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P11
-- name    : QAlgorithms_Papers_Independent_Bridge50_P11
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T12:24:05.820663+00:00
-- url     : https://prove2.me/theorems/d3574bad-ed63-416a-a91d-66c4d6c6d4ff
-- title:
--   Definitions for Trace- and improved data processing inequalities for von Neumann algebras
-- statement:
--   The objects the formalized statements of *Trace- and improved data processing inequalities for von Neumann algebras* (arXiv:2102.07479) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `measuredObjective`: PDF p.16, Eq.(80): the variational objective for measured relative entropy. For a self-adjoint h and normal state sigma, sigma(exp h) is strictly positive and equals the squared Hilbert norm of exp(h/2) applied to any unit vector representing sigma. Thus this is precisely the printed objective. ENNReal.log retains log(0) = -infinity outside that domain; Real.log(0) is never used. A von Neumann algebra is norm closed, so its exponential series converges in its own subtype; no type I, finite-dimensional, or trace assumption is used.
--   - `measuredEntropy`: PDF p.16, Eq.(80): supremum over ALL bounded self-adjoint algebra elements, with values in the extended reals. For normal states the index set contains zero, whose objective is zero, and an unbounded supremum is +infinity. The definition imposes neither faithfulness nor entropy finiteness.
-- source:
--   Trace-and improved data processing inequalities for von Neumann algebras, arXiv:2102.07479v2, https://arxiv.org/abs/2102.07479v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06

/-!
Statements from Hollands, arXiv:2102.07479v2. All page citations are PDF pages.
Accepted Claimed50.P06 standard forms, normal states, sigma-finiteness,
faithfulness and unsquared fidelity are reused under the independent-paper
workflow override. All new definitions belong to this paper.

This draft contains Proposition 1 and Lemma 7. Other planned nodes have explicit
entries in HARD.md and GAPS.json; in particular no general von Neumann algebra
is replaced by a matrix algebra. Compilation and independent moderation are
pending. No claimed supporting-paper gap is certified resolved.
-/

noncomputable section

open Filter
open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Bridge50.P11

open QAlgorithms.Papers.Independent.Claimed50.P06
  (StandardForm IsNormalState IsFaithful IsSigmaFinite vectorFunctional vectorFidelity)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.16, Eq.(80): the variational objective for measured relative entropy.
For a self-adjoint h and normal state sigma, sigma(exp h) is strictly positive
and equals the squared Hilbert norm of exp(h/2) applied to any unit vector
representing sigma. Thus this is precisely the printed objective. ENNReal.log
retains log(0) = -infinity outside that domain; Real.log(0) is never used.
A von Neumann algebra is norm closed, so its exponential series converges in
its own subtype; no type I, finite-dimensional, or trace assumption is used. -/
def measuredObjective (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (rho sigma : A →L[ℂ] ℂ) (h : A) : EReal :=
  ((rho h).re : EReal) -
    ENNReal.log (ENNReal.ofReal ((sigma (NormedSpace.exp h)).re))

/-- PDF p.16, Eq.(80): supremum over ALL bounded self-adjoint algebra elements,
with values in the extended reals. For normal states the index set contains
zero, whose objective is zero, and an unbounded supremum is +infinity.
The definition imposes neither faithfulness nor entropy finiteness. -/
def measuredEntropy (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (rho sigma : A →L[ℂ] ℂ) : EReal :=
  ⨆ h : {h : A // IsSelfAdjoint h}, measuredObjective A rho sigma h.val

example (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (rho sigma : A →L[ℂ] ℂ) (hSigma : sigma 1 = 1) :
    measuredObjective A rho sigma 0 = 0 := by
  simp [measuredObjective, hSigma]

example (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    measuredEntropy A 0 0 = ⊤ := by
  have hzero : IsSelfAdjoint (0 : A) := by simp [IsSelfAdjoint]
  apply top_unique
  calc
    (⊤ : EReal) = measuredObjective A 0 0 0 := by simp [measuredObjective]
    _ ≤ measuredEntropy A 0 0 :=
      le_iSup_of_le ⟨0, hzero⟩ le_rfl

end QAlgorithms.Papers.Independent.Bridge50.P11


