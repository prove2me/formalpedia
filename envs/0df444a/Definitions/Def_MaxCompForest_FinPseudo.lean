-- Prove2me | Definitions.Def_MaxCompForest_FinPseudo
-- name    : MaxCompForest_FinPseudo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:11.314921+00:00
-- url     : https://prove2.me/theorems/60a702e7-fe5c-4465-99f0-e16acbf5fb3b
-- title:
--   A finite pseudometric on the row labels
-- statement:
--   A function $\rho$ on pairs of labels is a **finite pseudometric** when it is real and non-negative, vanishes on the diagonal, is symmetric, and satisfies the triangle inequality. Distinct labels may be at distance zero.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma 2.2, p.7

import Mathlib

namespace MaxCompForest

variable {V : Type*}

/-- **`ρ` is a finite pseudometric on the labels**: real, non-negative, zero on the diagonal, symmetric,
and satisfying the triangle inequality. Distinct labels may be at distance zero.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Lemma 2.2, p.7. -/
def FinPseudo (ρ : V → V → ℝ) : Prop :=
  (∀ u v, 0 ≤ ρ u v) ∧ (∀ v, ρ v v = 0) ∧ (∀ u v, ρ u v = ρ v u) ∧
    ∀ u v w, ρ u w ≤ ρ u v + ρ v w

end MaxCompForest


