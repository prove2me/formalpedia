-- Prove2me | Definitions.Def_LawLocalComp_RobustContract
-- name    : LawLocalComp_RobustContract
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:12:31.562262+00:00
-- url     : https://prove2.me/theorems/70a00698-f703-452b-8c3b-b108a2aae23d
-- title:
--   Robust maximum-norm comparison (14)
-- statement:
--   A map $\Phi$ satisfies the **robust comparison** with resource $R$, input class $\mathcal C$ and factor $\kappa$ if for every admitted selection of rational laws in $\mathcal C$ with nonnegative directions,
--   $$\kappa^{-1}\,\mathbb E\|L\|_\infty\le\mathbb E\|\tilde L\|_\infty\le\kappa\,\mathbb E\|L\|_\infty .$$
--   (14) is $\kappa=1+\varepsilon$. Outputs are arbitrary laws: means may be biased and constant inputs may have nonconstant outputs.
--
--   **Formalization Note** $\|\cdot\|_\infty$ is Mathlib's sup norm on `Fin d → ℝ`.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), (14), p.8

import Mathlib
import Definitions.Def_LawLocalComp_IsRatLaw
import Definitions.Def_LawLocalComp_expNorm
import Definitions.Def_LawLocalComp_dirRank
import Definitions.Def_LawLocalComp_Resource_admits

namespace LawLocalComp

/-- **The robust two-sided maximum-norm comparison (14) with factor `κ`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), (14), p.8: `(1 + ε)⁻¹ E‖L‖∞ ≤ E‖L̃‖∞ ≤ (1 + ε) E‖L‖∞`; Theorem 1.1, p.2 ("robust lower
comparison allows biased means and arbitrary outputs on constant inputs").

`RobustContract Φ R cls κ`: for every admitted selection of rational laws in `cls` with nonnegative
directions, `κ⁻¹ E‖L‖∞ ≤ E‖L̃‖∞ ≤ κ E‖L‖∞`, where `‖·‖` is the maximum norm. (14) is
`κ = 1 + ε`.

**Formalization Note.** `‖·‖` on `Fin d → ℝ` is Mathlib's sup norm `max_i |v_i|`. The output
`Φ X` is an arbitrary real law: no rationality, no conditional-mean property and no mean
preservation are required. -/
def RobustContract (Φ : Law → Law) (R : Resource) (cls : Law → Prop) (κ : ℝ) : Prop :=
  ∀ (d n : ℕ) (X : Fin n → Law) (a : Fin n → Fin d → ℝ), (∀ j, IsRatLaw (X j) ∧ cls (X j)) →
    (∀ j, 0 ≤ a j) → R.admits n (dirRank a) →
      κ⁻¹ * expNorm (fun v : Fin d → ℝ => ‖v‖) X a ≤ expNorm (fun v => ‖v‖) (fun j => Φ (X j)) a ∧
        expNorm (fun v : Fin d → ℝ => ‖v‖) (fun j => Φ (X j)) a ≤ κ * expNorm (fun v => ‖v‖) X a

end LawLocalComp


