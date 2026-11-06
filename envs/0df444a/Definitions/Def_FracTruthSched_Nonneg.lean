-- Prove2me | Definitions.Def_FracTruthSched_Nonneg
-- name    : FracTruthSched_Nonneg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:15.82712+00:00
-- url     : https://prove2.me/theorems/92243990-c3b1-447a-9527-1a77f7379693
-- title:
--   Nonnegative input $t\in\mathbb R_{\ge0}^{n\times\tau}$
-- statement:
--   An input $t=(t_{ij})$ is **nonnegative** if every entry is a nonnegative real number,
--   $$t_{ij}\ge 0\qquad\text{for all machines } i \text{ and tasks } j.$$
--   The paper's inputs are exactly these: "All inputs are finite matrices with nonnegative real entries." Zero values are allowed and essential to the lower-bound construction.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, §2, p.3, and §2.2, Conventions, p.4

import Mathlib

set_option autoImplicit false

namespace FracTruthSched

/-- An input with **nonnegative real entries** (Anastasiadis et al., arXiv:2611.06642v1, §2,
p.3: "Each task j ∈ M has a processing time (or value) t_ij ∈ R≥0", and §2.2, p.4, Conventions:
"All inputs are finite matrices with nonnegative real entries").

**Formalization Note.** Zero entries are allowed; the lower-bound proof needs them. -/
def Nonneg {n : ℕ} {τ : Type*} (t : Fin n → τ → ℝ) : Prop :=
  ∀ i j, 0 ≤ t i j

end FracTruthSched


