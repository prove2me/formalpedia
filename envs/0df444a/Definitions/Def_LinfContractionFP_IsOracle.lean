-- Prove2me | Definitions.Def_LinfContractionFP_IsOracle
-- name    : LinfContractionFP_IsOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:20.345619+00:00
-- url     : https://prove2.me/theorems/71bb3416-939e-412c-9479-d085002981bf
-- title:
--   An Oracle of the extremal amplification game (Problem 1)
-- statement:
--   In the **extremal amplification game**, an Oracle holds a secret $\sigma\in\mathbb R^n$. On a shift vector $b$, $\mathrm{Oracle}(b)$ either declares defeat, or returns a labeling in $\{-1,+1\}^n$ that tags with $-1$ every coordinate $i$ with $\sigma_i+b_i$ within $\rho$ of $\min(\sigma+b)$ and with $+1$ every coordinate within $\rho$ of $\max(\sigma+b)$. A map $O$ is an Oracle for $\sigma$ at accuracy $\rho$ if every labeling it returns is valid in this sense.
--
--   ThinLabel, run on shifted boxes, is such an Oracle for the face slacks (Remark 4).
--
--   **Formalization Note** The Oracle is adversarial and adaptive: its answer may depend on the index $t$ of the call as well as on $b$, which against the deterministic Amplify covers every history-dependent strategy; a stateless Oracle such as ThinLabel is the case $O(t,b)=O'(b)$. A defeat carries a payload, which for Algorithm 4 is the approximate fixed point returned by ThinLabel. Defeat is always allowed.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Problem 1, p.11

import Mathlib
import Definitions.Def_LinfContractionFP_IsAccurate

namespace LinfContractionFP

/-- `O` is an Oracle of the extremal amplification game (Problem 1) for the secret vector `σ` at
accuracy `ρ`: at its `t`-th call (`t = 0, 1, …`) on a shift vector `b`, `O t b` either declares
defeat (`Sum.inl a`, with a payload `a`) or returns a labeling (`Sum.inr ℓ`) that tags with `−1`
(`lo`) every coordinate of `σ + b` within `ρ` of its minimum and with `+1` (`hi`) every
coordinate within `ρ` of its maximum.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Problem 1, p.11: "Given the
vector b, Oracle(b) can either: 1. declare defeat; or 2. return a labeling {−1, +1}^n that must
tag with −1 all the coordinates i such that σ_i + b_i is within distance ρ of the minimum of
σ + b, and as +1 all those within distance ρ of the maximum of σ + b; all other coordinates can
be labeled either way."

**Formalization Note.** The Oracle is adversarial and adaptive: its answer may depend on the
index `t` of the call as well as on the query `b`. Against a deterministic caller (Amplify) this
covers every history-dependent strategy, since the history before the `t`-th call is determined
by the strategy's own earlier answers; a stateless Oracle (ThinLabel, Algorithm 4) is the case
`O t b = O' b`. Defeat is always allowed. The payload `a : α` of a defeat is what the caller
receives (for Algorithm 4 it is the approximate fixed point returned by ThinLabel); labels `lo`,
`hi` stand for `−1`, `+1`. -/
def IsOracle {κ α : Type} [Fintype κ] (σ : κ → ℝ) (ρ : ℝ) (O : ℕ → (κ → ℝ) → α ⊕ (κ → Lbl)) :
    Prop :=
  ∀ t b ℓ, O t b = Sum.inr ℓ → IsAccurate ρ (σ + b) ℓ

end LinfContractionFP


