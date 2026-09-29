-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasPolynomialCertificate
-- name    : CK_GeneralCK_ReflectionSmallBiasPolynomialCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:51:34.519259+00:00
-- url     : https://prove2.me/theorems/078f31bf-171e-4adc-8eca-208515514249
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasPolynomialCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasPolynomialCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasPolynomialCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasPolynomialCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasPolynomialCertificate.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasPolynomial

-- ===== source module GeneralCK.ReflectionSmallBiasPolynomialCertificate =====
section

/-! # Exact equality certificates for the reflection polynomial arithmetic -/

namespace GeneralCK.Reflection.SmallBiasPolynomial

def equalityCheck (p q : List Term) : Bool := decide (normalize (p ++ scale (-1) q) = [])

theorem equalityCheck_sound {p q : List Term} (h : equalityCheck p q = true)
    (k : ℂ) (z : ℂ × ℂ) : eval k p z = eval k q z := by
  have hh : normalize (p ++ scale (-1) q) = [] := by
    simpa only [equalityCheck, decide_eq_true_eq] using h
  have he := congrArg (fun ts => eval k ts z) hh
  rw [eval_normalize, eval_append, eval_scale] at he
  simpa only [eval, Rat.cast_neg, Rat.cast_one, neg_one_mul, ← sub_eq_add_neg,
    sub_eq_zero] using he

end GeneralCK.Reflection.SmallBiasPolynomial

end


