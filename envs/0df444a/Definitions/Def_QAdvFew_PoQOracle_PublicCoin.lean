-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_PublicCoin
-- name    : QAdvFew_PoQOracle_PublicCoin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:06.67987+00:00
-- url     : https://prove2.me/theorems/a93ade1c-b138-41cf-bd94-f8742b46d370
-- title:
--   Public-coin verifier
-- statement:
--   A proof of quantumness with a classical verifier is **public coin** if every verifier message consists of fresh uniformly random bits, and the verifier's final decision is a deterministic function of $1^n$, the transcript and $O$.
--
--   **Formalization Note** On input $1^n$ the coins are $R(n)\ell(n)$ bits and the message of round $j$ is the $j$-th block of coins. The decision is computed without the coins by a clocked oracle machine on $(1^n,\text{transcript})$, so it is deterministic polynomial time.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Remark 3.27, p. 19 (PDF p. 21)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_CVerifier

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- A classical verifier is **public coin** relative to `O` (Goldin, Lombardi, Morimae, *Quantum
Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Remark 3.27, p. 19 (PDF p. 21):
"every verifier message consists of fresh uniformly random bits, and the verifier's final decision
is a deterministic function of `1^n`, the transcript, and `O`"; [AGKZ20, Definition 7.1]).

**Formalization Note** On input `1^n` the coins are `R(n) · ℓ(n)` bits, the message of round `j` is
the `j`-th block of `ℓ(n)` coins, and the decision is the first output bit of a clocked oracle
machine `D` run on `(1^n, transcript)`, so it is computed in deterministic polynomial time without
the coins. -/
def PublicCoin (O : Oracle) (V : CVerifier) : Prop :=
  (∀ n : ℕ, V.coins.eval n = V.R.eval n * V.ℓ.eval n) ∧
  (∀ (n : ℕ) (r : Fin (V.coins.eval n) → Bool) (τ : Transcript (V.R.eval n) (V.ℓ.eval n))
      (j : Fin (V.R.eval n)),
    V.msg O (unary n) n (List.ofFn r) τ j = fun i : Fin (V.ℓ.eval n) =>
      (List.ofFn r).getD (j * V.ℓ.eval n + i) false) ∧
  ∃ (D : OTM) (q : Polynomial ℕ), ∀ (n : ℕ) (r : Fin (V.coins.eval n) → Bool)
      (τ : Transcript (V.R.eval n) (V.ℓ.eval n)),
    V.dec O (unary n) n (List.ofFn r) τ =
      (D.output O (tup (unary n :: τ.all)) (q.eval (tup (unary n :: τ.all)).length)).headD false

end QAdvFew.PoQOracle


