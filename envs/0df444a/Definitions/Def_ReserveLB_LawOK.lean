-- Prove2me | Definitions.Def_ReserveLB_LawOK
-- name    : ReserveLB_LawOK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:51.0639+00:00
-- url     : https://prove2.me/theorems/8b321ea4-87ca-43ca-bfc8-faa0b9832926
-- title:
--   Finite law listed by its atoms
-- statement:
--   A **listed finite law** of a nonnegative size is a finite list of atoms $(a_\ell, p_\ell)$, $\ell = 1, \dots, L$, of rational values and probabilities such that
--   $$
--   L \ge 1,\qquad a_\ell \ge 0,\qquad p_\ell > 0,\qquad \sum_{\ell} p_\ell = 1 .
--   $$
--   The random size takes the value $a_\ell$ with probability $p_\ell$; when a value is listed several times its probabilities add up.
--
--   These are the marginal laws of the original sizes $X_j$ in the input of Theorem 1.1: every probability is positive, and no lower bound on the probabilities or on the speed ratios is assumed.
--
--   **Formalization Note** A law is a `List (ℚ × ℚ)`; repeated values are allowed.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 1, p.2 (explicitly listed finite rational laws)

import Mathlib

namespace ReserveLB

/-- **A finite law listed by its atoms.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 1, p.2: "Finite marginal laws are explicitly listed rationals";
p.2: "Speed ratios and positive probabilities are unrestricted".

`LawOK μ` says that the list `μ` of atoms `(value, probability)` is a finite probability law of a
nonnegative size: it is nonempty, every value is `≥ 0`, every probability is `> 0`, and the
probabilities sum to one.

**Formalization Note.** A law is a list of rational pairs, as in the binary input. Repeated values
are allowed; the law is then the sum of the listed atoms. -/
def LawOK (μ : List (ℚ × ℚ)) : Prop :=
  μ ≠ [] ∧ (∀ a ∈ μ, 0 ≤ a.1 ∧ 0 < a.2) ∧ (μ.map Prod.snd).sum = 1

end ReserveLB


