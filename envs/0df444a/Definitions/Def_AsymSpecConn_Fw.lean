-- Prove2me | Definitions.Def_AsymSpecConn_Fw
-- name    : AsymSpecConn_Fw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:02.111327+00:00
-- url     : https://prove2.me/theorems/a6d00900-d276-4807-9002-d9146844265d
-- title:
--   The normalised supremum $F_w$
-- statement:
--   For $w:\mathcal A\to\mathbb R_{\ge0}$ and $s\in\mathcal S$,
--   $$F_w(s)=\sup\{w(a)^{1/n}:n\ge1,\ a\in\mathcal A,\ a\le s^n\}\in[0,\infty].$$
--   It is the candidate spectral point built from the values of $w$ on $\mathcal A$.
--
--   **Formalization Note** The value lies in $[0,\infty]$, where the supremum of the empty set is $0$, the source's convention (p.12). Only the values of $w$ on $\mathcal A$ enter.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Definition 2.3, p.14

import Mathlib

set_option autoImplicit false

open scoped NNReal ENNReal

namespace AsymSpecConn

/-- **The normalised supremum `F_w`** (Definition 2.3, p.14 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)):
`F_w(s) := sup{w(a)^{1/n} : n ≥ 1, a ∈ A, a ≤ sⁿ} ∈ [0, ∞]`.

**Formalization Note** Valued in `ℝ≥0∞`, where the supremum of the empty set is `0`, matching the
paper's convention `sup ∅ = 0 in [0, ∞]` (p.12). Only the values of `w` on `A` enter. -/
noncomputable def Fw {S : Type*} [CommSemiring S] (P : Preorder S) (A : Set S) (w : S → ℝ≥0)
    (s : S) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (_ : 1 ≤ n) (a : S) (_ : a ∈ A) (_ : P.le a (s ^ n)),
    ((w a : ℝ≥0) : ℝ≥0∞) ^ ((1 : ℝ) / n)

end AsymSpecConn


