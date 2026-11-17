-- Prove2me | Definitions.Def_HypRecov_Supplement_FinalRecoveryScheme
-- name    : HypRecov_Supplement_FinalRecoveryScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:26:00.753188+00:00
-- url     : https://prove2.me/theorems/0ed0fde1-f150-4940-b9b0-c1ba20faaa3c
-- title:
--   Randomized $s$-bit final-state schemes for recovering $\mathcal B_k(H)$
-- statement:
--   An **$s$-bit final-state recovery scheme** maps a simple $r$-uniform hypergraph to one of at most $2^s$ states and decodes the complete family $\mathcal B_k(H)$. Encoder, public and decoder randomness are bundled into one finite uniform tape. The success requirement is per input and at least $2/3$.
--
--   This information-theoretic object is independent of the streaming observation model. It is the class quantified over by Theorem 10.1's exact output-information lower bound.
--
--   **Formalization Note** The state type is `Fin (2^s)`. The coin alphabet is explicitly nonempty, avoiding the zero-probability empty-space convention.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem 10.1 and proof, pp.27-28 (PDF pp.28-29)

import Mathlib
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_HypRecov_crisp
import Definitions.Def_HypRecov_Supplement_IsCutDegenerate

set_option autoImplicit false

namespace HypRecov.Supplement

/-- An `s`-bit randomized final-state recovery scheme.  Public coins, encoder coins and decoder
coins are bundled into one finite uniform tape; the state space has cardinality exactly `2^s`, hence
at most `2^s` states may be used. -/
structure FinalRecoveryScheme (n r k s : ℕ) where
  N : ℕ
  M : ℕ
  M_pos : 1 ≤ M
  encode : (Fin N → Fin M) → Finset (Finset (Fin n)) → Fin (2 ^ s)
  decode : (Fin N → Fin M) → Fin (2 ^ s) → Finset (Finset (Fin n))

/-- The scheme recovers `B_k(H)` with probability at least `2/3` for every simple `r`-uniform
input hypergraph. -/
noncomputable def FinalRecovers {n r k s : ℕ} (A : FinalRecoveryScheme n r k s) : Prop :=
  ∀ E : Finset (Finset (Fin n)), IsUniform r E →
    PunctSketch.coinProb (fun omega : Fin A.N → Fin A.M =>
      A.decode omega (A.encode omega E) ≠ HypRecov.crisp E k) ≤ 1 / 3

/-- `ceil(3n/4)` as a natural number. -/
def threeQuarterCeil (n : ℕ) : ℕ := (3 * n + 3) / 4

/-- The exact real-valued information lower bound from Theorem 10.1. -/
noncomputable def informationLowerBound (n r k : ℕ) : ℝ :=
  let c := threeQuarterCeil n
  let Nr := c.choose (r - 1)
  ((n - c : ℕ) : ℝ) * Real.logb 2 (Nr.choose (k - 1)) + Real.logb 2 (2 / 3)

end HypRecov.Supplement


