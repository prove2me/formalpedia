-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasFineCertificate
-- name    : CK_GeneralCK_ReflectionSmallBiasFineCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:43:24.163376+00:00
-- url     : https://prove2.me/theorems/9e04a06e-1897-46cb-88d7-90b3bcac0896
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasFineCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasFineCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasFineCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasFineCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasFineCertificate.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasExponentCertificate

-- ===== source module GeneralCK.ReflectionSmallBiasFineCertificate =====
section

/-! Exact finite coverage by first exponent and entropy-exponent parity. -/

namespace GeneralCK.Reflection.SmallBiasPolynomial

def fineDegree (t : Term) : ℕ := 2*t.a + t.k.natAbs % 2

def finePart (d : ℕ) (p : List Term) : List Term := p.filter (fun t => fineDegree t=d)

def fineBound (n : ℕ) (p : List Term) : Bool := p.all (fun t => decide (fineDegree t<n))

theorem fineBound_sound {n : ℕ} {p : List Term} (h : fineBound n p = true) :
    ∀ t ∈ p, fineDegree t<n := by
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp h t ht)

theorem eval_finePart_cons (d : ℕ) (k : ℂ) (t : Term) (ts : List Term) (z : ℂ × ℂ) :
    eval k (finePart d (t::ts)) z =
      (if fineDegree t=d then evalTerm k t z else 0)+eval k (finePart d ts) z := by
  by_cases h : fineDegree t=d
  · simp [finePart,eval,h]
  · simp [finePart,eval,h]

theorem sum_eval_fineParts (n : ℕ) (k : ℂ) (p : List Term) (z : ℂ × ℂ)
    (hp : ∀ t ∈ p, fineDegree t<n) :
    (∑ d ∈ Finset.range n, eval k (finePart d p) z) = eval k p z := by
  induction p with
  | nil => simp [finePart,eval]
  | cons t ts ih =>
    have ht := hp t (by simp)
    have hts := ih (fun r hr => hp r (by simp [hr]))
    simp_rw [eval_finePart_cons]
    rw [Finset.sum_add_distrib,hts]
    simp [eval,ht]

theorem eval_eq_of_fineParts (n : ℕ) (k : ℂ) (p q : List Term) (z : ℂ × ℂ)
    (hp : ∀ t ∈ p, fineDegree t<n) (hq : ∀ t ∈ q, fineDegree t<n)
    (he : ∀ d<n, equalityCheck (finePart d p) (finePart d q) = true) :
    eval k p z = eval k q z := by
  rw [← sum_eval_fineParts n k p z hp,← sum_eval_fineParts n k q z hq]
  apply Finset.sum_congr rfl
  intro d hd
  exact equalityCheck_sound (he d (Finset.mem_range.mp hd)) k z

end GeneralCK.Reflection.SmallBiasPolynomial


end


