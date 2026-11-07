-- Prove2me | Definitions.Def_RandOrderCSP_HasIntegralityGap
-- name    : RandOrderCSP_HasIntegralityGap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:08:49.31728+00:00
-- url     : https://prove2.me/theorems/fee060b3-4b6d-4f4f-836e-b9ed1fb1c54b
-- title:
--   Integrality gap of the basic LP
-- statement:
--   $\text{MAX-CSP}_{\beta,\gamma}(\Gamma)$ **has an integrality gap** if some instance $\Phi$ of $\mathrm{CSP}(\Gamma)$ has $\mathrm{opt}^{LP}_\Phi\ge\gamma$ and $\mathrm{opt}_\Phi\le\beta$; otherwise it is **roundable**.
--
--   The absence of "the LP solves" implies this condition, and the gap instance is what the lower bound's reduction starts from.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), §3.3, p.14

import Mathlib
import Definitions.Def_RandOrderCSP_optLP

namespace RandOrderCSP

/-- **Integrality gap of the basic LP** (§3.3, p.14).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), p.14: "we say that the problem MAX-CSP_{β,γ}(Γ)
has an integrality gap (for the basic LP) if there exists an instance Φ of CSP(Γ) such that
opt^LP_Φ ≥ γ and opt_Φ ≤ β, and otherwise we say that MAX-CSP_{β,γ}(Γ) is roundable (for the basic
LP)." Roundable is `¬ HasIntegralityGap Γ β γ`.

**Formalization Note.** The instance has a finite vertex set and a finite nonempty edge set (p.13). -/
def HasIntegralityGap {k : ℕ} {Sig : Type} [Fintype Sig] [DecidableEq Sig]
    (Γ : Set ((Fin k → Sig) → Bool)) (β γ : ℝ) : Prop :=
  ∃ (V E : Type) (_ : Fintype V) (_ : DecidableEq V) (_ : Fintype E) (_ : Nonempty E)
    (Φ : CSP k Sig V E), Φ.IsInstanceOf Γ ∧ Φ.opt ≤ β ∧ γ ≤ optLP Φ

end RandOrderCSP


