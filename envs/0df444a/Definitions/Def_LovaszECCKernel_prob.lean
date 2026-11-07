-- Prove2me | Definitions.Def_LovaszECCKernel_prob
-- name    : LovaszECCKernel_prob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:55:55.986904+00:00
-- url     : https://prove2.me/theorems/dd1a71d7-b390-4dc7-b0a8-db8768305b7b
-- title:
--   Probability over $T$ fair random bits
-- statement:
--   For an event $E$ on bit strings $r\in\{0,1\}^T$,
--   $$\Pr[E]=\frac{|\{r\in\{0,1\}^T : E(r)\}|}{2^T},$$
--   the probability under $T$ independent fair bits. Randomized runs draw their random bits from this distribution.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), p.4 and Proposition 1, p.17 (= PDF pp.4, 17)

import Mathlib

set_option autoImplicit false

namespace LovaszECCKernel

open Classical in
/-- The **probability** of an event over `T` independent fair random bits (Fomin, Golovach,
Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic Extensions of the Lovász
and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript sha256 a9d53ab8…), p.4 and
Proposition 1, p.17 (= PDF pp.4, 17): "with probability at least 1 − n^{−C}", "with probability at
least 1 − 1/n").

**Formalization Note** The fraction of the `2^T` bit strings `r : Fin T → Bool` that satisfy `E`
(the uniform distribution; no measure theory). -/
noncomputable def prob (T : ℕ) (E : (Fin T → Bool) → Prop) : ℝ :=
  ((Finset.univ.filter E).card : ℝ) / 2 ^ T

end LovaszECCKernel


