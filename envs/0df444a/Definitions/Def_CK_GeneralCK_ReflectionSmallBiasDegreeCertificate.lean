-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasDegreeCertificate
-- name    : CK_GeneralCK_ReflectionSmallBiasDegreeCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:00:47.42922+00:00
-- url     : https://prove2.me/theorems/b0653ca1-f756-4023-9ba8-dafbb83ea15a
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasDegreeCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasDegreeCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasDegreeCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasDegreeCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasDegreeCertificate.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasPolynomialCertificate

-- ===== source module GeneralCK.ReflectionSmallBiasDegreeCertificate =====
section

/-! Degree-wise exact checks keep polynomial certificates within a fixed memory budget. -/

namespace GeneralCK.Reflection.SmallBiasPolynomial

def degreePart (d : ℕ) (p : List Term) : List Term := p.filter (fun t => t.a+t.b=d)

def degreeBound (n : ℕ) (p : List Term) : Bool := p.all (fun t => decide (t.a+t.b<n))

theorem degreeBound_sound {n : ℕ} {p : List Term} (h : degreeBound n p = true) :
    ∀ t ∈ p, t.a+t.b<n := by
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp h t ht)

theorem eval_degreePart_cons (d : ℕ) (k : ℂ) (t : Term) (ts : List Term) (z : ℂ × ℂ) :
    eval k (degreePart d (t::ts)) z =
      (if t.a+t.b=d then evalTerm k t z else 0)+eval k (degreePart d ts) z := by
  by_cases h : t.a+t.b=d
  · simp [degreePart,eval,h]
  · simp [degreePart,eval,h]

theorem sum_eval_degreeParts (n : ℕ) (k : ℂ) (p : List Term) (z : ℂ × ℂ)
    (hp : ∀ t ∈ p, t.a+t.b<n) :
    (∑ d ∈ Finset.range n, eval k (degreePart d p) z) = eval k p z := by
  induction p with
  | nil => simp [degreePart,eval]
  | cons t ts ih =>
    have ht := hp t (by simp)
    have hts := ih (fun r hr => hp r (by simp [hr]))
    simp_rw [eval_degreePart_cons]
    rw [Finset.sum_add_distrib,hts]
    simp [eval,ht]

theorem eval_eq_of_degrees (n : ℕ) (k : ℂ) (p q : List Term) (z : ℂ × ℂ)
    (hp : ∀ t ∈ p, t.a+t.b<n) (hq : ∀ t ∈ q, t.a+t.b<n)
    (he : ∀ d<n, equalityCheck (degreePart d p) (degreePart d q) = true) :
    eval k p z = eval k q z := by
  rw [← sum_eval_degreeParts n k p z hp,← sum_eval_degreeParts n k q z hq]
  apply Finset.sum_congr rfl
  intro d hd
  exact equalityCheck_sound (he d (Finset.mem_range.mp hd)) k z

end GeneralCK.Reflection.SmallBiasPolynomial


end


