-- Prove2me | Definitions.Def_FewExperts_softmin
-- name    : FewExperts_softmin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:21.205564+00:00
-- url     : https://prove2.me/theorems/6ab30b0b-f609-407a-a0ae-37c5e3657726
-- title:
--   Softmin potential $S=-\frac1\eta\ln\sum_i e^{-\eta a^i}$
-- statement:
--   For a learning rate $\eta$ and reals $a^1,\dots,a^N$, the **softmin** is
--
--   $$
--   S=-\frac{1}{\eta}\ln\Bigl(\sum_{i=1}^N e^{-\eta a^i}\Bigr).
--   $$
--
--   Applied to the shifted advantages $a_t^i$ of the main algorithm, it is the potential (14) whose growth drives the analysis of Section 4.2.
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), §2.4, p.8 (PDF p.9) and (14), p.19 (PDF p.20)

import Mathlib

namespace FewExperts

/-- **The softmin potential `S = −(1/η) ln ∑_i e^{−η a_i}`.**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), §2.4, p.8 (PDF 9), and (14), p.19 (PDF 20):
"S_t = −(1/η) ln(∑_i exp(−η a_t^i))", the softmin of the shifted advantages `a_t^i` with learning
rate `η`.

**Formalization Note** `ln` is `Real.log`; the family is indexed by `Fin N`. -/
noncomputable def softmin {N : ℕ} (η : ℝ) (a : Fin N → ℝ) : ℝ :=
  -(1 / η) * Real.log (∑ i, Real.exp (-η * a i))

end FewExperts


