-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasCandidateSparse
-- name    : CK_GeneralCK_ReflectionSmallBiasCandidateSparse
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:01:31.170495+00:00
-- url     : https://prove2.me/theorems/1e0958dc-6fa3-478e-88f2-d7f7357170d7
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasCandidateSparse` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasCandidateSparse` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasCandidateSparse` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasCandidateSparse (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasCandidateSparse.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasCandidate
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasPolynomialCertificate

-- ===== source module GeneralCK.ReflectionSmallBiasCandidateSparse =====
section

/-! The factored candidate expressed in the sparse Laurent-polynomial verifier. -/

namespace GeneralCK.Reflection.SmallBiasCandidateSparse

open SmallBiasPolynomial SmallBiasCoefficientBounds

def liftCoefficient (i j : ℕ) : List PowerTerm → List Term
  | [] => []
  | t :: ts => ⟨2*i,2*j,-(t.n:ℤ),t.c⟩ :: liftCoefficient i j ts

def rawQuotient : List CoefficientRow → List Term
  | [] => []
  | r :: rs => liftCoefficient r.i r.j r.coefficients ++ rawQuotient rs

def factor : List Term := [⟨5,1,0,1⟩,⟨3,3,0,-2⟩,⟨1,5,0,1⟩]

def rawCandidate : List Term := rawMul factor (rawQuotient SmallBiasCoefficientData.rows)

theorem eval_liftCoefficient (k : ℂ) (i j : ℕ) (ts : List PowerTerm) (z : ℂ × ℂ) :
    SmallBiasPolynomial.eval k (liftCoefficient i j ts) z =
      SmallBiasCoefficientBounds.eval ts k⁻¹*z.1^(2*i)*z.2^(2*j) := by
  induction ts with
  | nil => simp [liftCoefficient,SmallBiasPolynomial.eval,SmallBiasCoefficientBounds.eval]
  | cons t ts ih =>
    simp only [liftCoefficient,SmallBiasPolynomial.eval,evalTerm,SmallBiasCoefficientBounds.eval,
      zpow_neg,zpow_natCast,inv_pow,ih]
    ring

theorem eval_rawQuotient (rs : List CoefficientRow) (z : ℂ × ℂ) :
    SmallBiasPolynomial.eval (Real.log 2:ℂ) (rawQuotient rs) z =
      SmallBiasCandidate.quotient rs z := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hc : SmallBiasCoefficientBounds.eval r.coefficients (Real.log 2:ℂ)⁻¹ =
        (SmallBiasCandidate.coefficient r:ℂ) := by
      unfold SmallBiasCandidate.coefficient
      rw [← Complex.ofReal_inv]
      exact SmallBiasCoefficientBounds.eval_complex_ofReal r.coefficients ((Real.log 2)⁻¹)
    rw [rawQuotient,eval_append,eval_liftCoefficient,hc,ih]
    rfl

theorem eval_factor (k : ℂ) (z : ℂ × ℂ) :
    SmallBiasPolynomial.eval k factor z = z.1*z.2*(z.1^2-z.2^2)^2 := by
  norm_num [factor,SmallBiasPolynomial.eval,evalTerm]
  <;> ring

theorem eval_rawCandidate (z : ℂ × ℂ) :
    SmallBiasPolynomial.eval (Real.log 2:ℂ) rawCandidate z = SmallBiasCandidate.polynomial z := by
  have hk : (Real.log 2:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  rw [rawCandidate,eval_rawMul hk,eval_factor,eval_rawQuotient]
  rfl

end GeneralCK.Reflection.SmallBiasCandidateSparse


end


