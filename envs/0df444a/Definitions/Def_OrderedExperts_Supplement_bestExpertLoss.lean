-- Prove2me | Definitions.Def_OrderedExperts_Supplement_bestExpertLoss
-- name    : OrderedExperts_Supplement_bestExpertLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-18T06:38:54.244403+00:00
-- url     : https://prove2.me/theorems/7ff6a215-1de7-4460-b2f9-555b3462b9b0
-- title:
--   Best expert loss in hindsight
-- statement:
--   For a nonempty finite expert class, the **best expert loss in hindsight** is
--
--   $$
--   \min_{f\in F}\sum_{t=1}^{T}\ell_t(a_{t,f}).
--   $$
--
--   It is the comparator subtracted from each learner's expected paid loss.
--
--   **Formalization Note** The minimum is an attained finite-set minimum, not a real infimum with an empty-set or unbounded-set default value.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version), Sec. 2.2, p. 6

import Mathlib

open Finset

namespace OrderedExperts.Supplement

/-- **Loss of the best expert in hindsight.**
Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission
(held version), Sec. 2.2, p. 6.

**Formalization Note.** `Finset.inf'` is the genuine attained minimum over the finite nonempty
expert class.  It has no empty-set or unbounded-set default value. -/
noncomputable def bestExpertLoss {A : Type*} {n : ℕ} [NeZero n] (T : ℕ)
    (rec : ℕ → Fin n → A) (loss : ℕ → A → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun f ↦ ∑ t ∈ Finset.range T, loss t (rec t f))

end OrderedExperts.Supplement


