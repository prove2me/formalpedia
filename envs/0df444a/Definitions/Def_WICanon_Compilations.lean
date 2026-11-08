-- Prove2me | Definitions.Def_WICanon_Compilations
-- name    : WICanon_Compilations
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:06:49.464747+00:00
-- url     : https://prove2.me/theorems/ace95333-ab3a-4ab2-97f5-4faf7b2661f3
-- title:
--   The conclusions of Theorem 3.1 and Lemma 3.2 as predicates
-- statement:
--   Two predicates shared by the variants of a theorem.
--
--   1. The **deterministic-prover compilation** of Theorem 3.1: $\hat P$ is a deterministic polynomial-time algorithm; $(\hat P,\hat V)$ has the same number of rounds and is honest-verifier $\gamma$-SWI with $\gamma=k\cdot\ell_P\cdot3\varepsilon+1/q$ and $(1-\alpha-1/q)$-completeness; $\hat P$ has the per-round bound $\ell_P$; public coin is preserved.
--   2. The **round collapse** of Lemma 3.2: a two-message public-coin deterministic-prover protocol, honest-verifier $\delta T$-SWI and $(1-\alpha T)$-complete, with total communication $\ell T$, for a factor $T$; the factor is $T=(\ell_P(n)+\lceil\log_2 n\rceil+2)^{ck}$.
--
--   **Formalization Note** The exponent $c$ is a parameter here, quantified in Lemma 3.2.
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Theorem 3.1, pp.16–17; Lemma 3.2, p.17

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_WICanon_PolyBounds
import Definitions.Def_WICanon_IsNPRelation
import Definitions.Def_WICanon_ProtocolProps
import Definitions.Def_WICanon_Soundness
import Definitions.Def_WICanon_WitnessIndist

set_option autoImplicit false

namespace WICanon

/-- Everything alternative 2 of Theorem 3.1 (Arnon, Mazor, Pass, Silbak, STOC 2027 submission
manuscript, sha256 3f78ec3d…, pp.16–17) asserts about `pvHat` other than soundness, for the polynomial
`q`: `P̂` is a deterministic polynomial-time algorithm, `(P̂, V̂)` has the same number of rounds, is an
honest-verifier `γ`-SWI protocol with `γ = k · ℓP · 3ε + 1/q` and `(1 − α − 1/q)`-completeness, `P̂` has the
per-round bound `ℓP` of `P`, and public coin is preserved. -/
def IsDetProverCompilation (pv pvHat : Protocol) (R : Relation) (ε α : ℕ → ℝ) (ℓP : ℕ → ℕ)
    (q : Polynomial ℕ) : Prop :=
  pvHat.IsEfficient ∧ pvHat.IsDeterministicProver ∧ pvHat.rounds = pv.rounds ∧
  HonestSWI pvHat R (fun n =>
    (pv.rounds n : ℝ) * (ℓP n : ℝ) * 3 * ε n + oneOver q n) ∧
  CompleteAt pvHat R (fun n => α n + oneOver q n) ∧
  pvHat.PerRoundProverBound R ℓP ∧
  (pv.IsPublicCoin → pvHat.IsPublicCoin)

/-- The factor `poly(ℓP, log n)^k` of Lemma 3.2, p.17: `(ℓP(n) + ⌈log₂ n⌉ + 2)^{c·k}`. -/
noncomputable def collapseFactor (c k : ℕ) (ℓP : ℕ → ℕ) (n : ℕ) : ℝ :=
  (((ℓP n + Nat.clog 2 n + 2 : ℕ) : ℝ)) ^ (c * k)

/-- Everything the conclusion of Lemma 3.2, p.17 asserts about `pvHat` other than soundness: a two-message
(one round: verifier first) public-coin deterministic-prover protocol, honest-verifier
`(δ · T)`-SWI and `(1 − α · T)`-complete, of total communication `ℓ · T`, for `T` the factor above. -/
def IsRoundCollapse (pvHat : Protocol) (R : Relation) (δ α : ℕ → ℝ) (ℓ : ℕ → ℕ) (T : ℕ → ℝ) : Prop :=
  pvHat.IsEfficient ∧ pvHat.IsPublicCoin ∧ pvHat.IsDeterministicProver ∧
  pvHat.rounds = (fun _ => 1) ∧
  HonestSWI pvHat R (fun n => δ n * T n) ∧
  CompleteAt pvHat R (fun n => α n * T n) ∧
  ∀ n x w rP rV, x.length = n → R x w → rP.length = pvHat.coinsP n → rV.length = pvHat.coinsV n →
    (((pvHat.transcript x w rP rV).map List.length).sum : ℝ) ≤ (ℓ n : ℝ) * T n

end WICanon


