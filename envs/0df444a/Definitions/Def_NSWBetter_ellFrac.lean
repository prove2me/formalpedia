-- Prove2me | Definitions.Def_NSWBetter_ellFrac
-- name    : NSWBetter_ellFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:54:14.858498+00:00
-- url     : https://prove2.me/theorems/5995b323-6626-4a0f-bee0-ffe2193f230c
-- title:
--   Large good amount $\ell_i$ (Definition 4.9)
-- statement:
--   $\ell_i=\sum_{g\in L_i}x_{ig}$, the amount of large goods allocated to agent $i$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Definition 4.9, p.21

import Mathlib
import Definitions.Def_NSWBetter_largeSet

namespace NSWBetter

/-- **Large good amount ℓ_i (Definition 4.9).**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Definition 4.9, p.21: "the amount of large goods allocated to agent i, denoted ℓi, is defined as the value Σ_(g∈Li) xig." -/
noncomputable def ellFrac {n m : ℕ} (v : Fin n → Fin m → ℝ) (x : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  ∑ g ∈ largeSet v x i, x i g

end NSWBetter


