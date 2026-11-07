-- Prove2me | Definitions.Def_RandOrderCSP_IsOneWiseUniform
-- name    : RandOrderCSP_IsOneWiseUniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:08:59.919248+00:00
-- url     : https://prove2.me/theorems/a1e33496-dca4-493d-b020-d624b083a2f4
-- title:
--   One-wise uniform distribution on $\mathbb Z_q^k$
-- statement:
--   A distribution on $\mathbb Z_q^k$ is **one-wise uniform** when each of its $k$ coordinate marginals is uniform on $\mathbb Z_q$. The set of these is $\Delta_1(\mathbb Z_q^k)$.
--
--   These are the colors of DIHP gadgets: each single coordinate of a row reveals nothing about the hidden signal.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), §3, p.11

import Mathlib
import Definitions.Def_RandOrderCSP_optLP

namespace RandOrderCSP

/-- **One-wise uniform distribution** (§3, p.11).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), p.11: "A distribution on a product set S^k is
one-wise uniform when each of its k coordinate marginals is uniform on S. Δ₁(S^k) denotes the set of
all one-wise uniform distributions on S^k."

**Formalization Note.** Here `S = ℤ_q` (`ZMod q`, `q ≥ 2` is the paper's standing convention, p.10);
a distribution is a probability vector on `ℤ_q^k = Fin k → ZMod q`. -/
def IsOneWiseUniform {k q : ℕ} [NeZero q] (Y : (Fin k → ZMod q) → ℝ) : Prop :=
  IsDistr Y ∧ ∀ (ℓ : Fin k) (a : ZMod q), marginal Y ℓ a = 1 / (q : ℝ)

end RandOrderCSP


