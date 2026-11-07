-- Prove2me | Definitions.Def_LaconicBarrier_InIP
-- name    : LaconicBarrier_InIP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:38.401677+00:00
-- url     : https://prove2.me/theorems/0c6db6c9-5384-4dd2-a0ee-193bc13ef208
-- title:
--   The classes $\mathsf{IP}(\cdots)$ and $\mathsf{AM}(\cdots)$ with named parameters
-- statement:
--   $(L_{\mathrm{yes}}, L_{\mathrm{no}}) \in \mathsf{IP}(\text{rounds} = k, \text{verifier time} = T, \text{prover comm} = \ell_P, \text{verifier comm} = \ell_V, \text{verifier randomness} = r, \text{completeness} \ge 1-\epsilon_c, \text{soundness} \le \epsilon_s)$ if there is a $k$-round verifier with
--
--   1. verifier time $O(T)$, for all coins and all prover messages;
--   2. at most $r$ random bits and at most $\ell_V$ verifier bits in total, for all coins and all prover messages;
--   3. at most $\ell_P$ prover bits in total;
--   4. completeness: on every yes-instance some prover is accepted with probability at least $1-\epsilon_c$;
--   5. soundness: on every no-instance every prover is accepted with probability at most $\epsilon_s$.
--
--   $\mathsf{AM}(\cdots)$ adds the public-coin restriction: every verifier message is a fresh uniform random string and all coins are sent. For a language $L$, $\mathsf{coAM}(\cdots)$ is $\mathsf{AM}(\cdots)$ for its complement, i.e. for the promise problem $(\overline L, L)$.
--
--   **Formalization Note** The time bound is per verifier step, each step computed from the transcript; for the constant round counts of the mission ($k \le 2$) this agrees with the total running time up to a constant factor. Provers are deterministic strategies, which is no loss for either completeness or soundness. Bounds are functions of the input, so bounds in the statement length of a structured input are a special case.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §4.2.1, p.25, Definition 4.28

import Mathlib
import Definitions.Def_LaconicBarrier_IPVerifier
import Definitions.Def_LaconicBarrier_RunsWithin
import Definitions.Def_QAdvFew_PoQOracle_tup

namespace LaconicBarrier

/-- The verifier `V` is a `k`-round **interactive proof for the promise problem** `(yes, no)` with
the named parameters of the paper (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript sha256
1af78662…), §4.2.1, p.25, Definition 4.28 and the class `IP(rounds = k, verifier time = T, prover
comm = ℓ_P, verifier comm = ℓ_V, verifier randomness = r, completeness ≥ 1 − ϵ_c, soundness ≤ ϵ_s)`):

1. **verifier time `O(T)`**: one machine computes each verifier step (the next message, or after `k`
   prover messages the decision) from `(encoded input, coins, prover messages so far)` within
   `C · (T(i) + 1)` steps, for a constant `C`, for all coins and all prover messages;
2. **verifier randomness** at most `r(i)` coins;
3. **verifier communication** at most `ℓ_V(i)` bits in total, for all coins and all prover messages;
4. **prover communication** at most `ℓ_P(i)` bits in total (a transcript exceeding it is rejected,
   `IPVerifier.accProb`);
5. **completeness**: on every `i ∈ yes` some prover is accepted with probability `≥ 1 − ϵ_c(i)`;
6. **soundness**: on every `i ∈ no` every prover is accepted with probability `≤ ϵ_s(i)`.

**Formalization Note** "The bounds on verifier time, communication, and randomness hold for every
prover strategy and every choice of the verifier's coins" (p.25). The time bound is per verifier
step, each step computed from the transcript; for the constant round counts of the mission (`k ≤ 2`)
this is the total running time up to a constant factor. Provers are deterministic strategies (the
best coins of a randomized prover do at least as well). Bounds are functions of the input itself, so a
bound in the statement length `n` of a structured input is a special case. -/
def IPVerifier.Proves {I : Type} (V : IPVerifier I) (enc : I → List (List Bool))
    (yes no : Set I) (k : ℕ) (T ℓP ℓV r : I → ℕ) (εc εs : I → ℝ) : Prop :=
  (∃ (C : ℕ) (M : KarpLiptonOM.OracleTM), ∀ (i : I) (ρ : Fin (V.coins i) → Bool)
      (pms : List (List Bool)), pms.length ≤ k →
      RunsWithin M (enc i ++ [bits ρ, QAdvFew.PoQOracle.tup pms])
        (if pms.length < k then QAdvFew.PoQOracle.tup [[false], V.msg i ρ pms]
          else QAdvFew.PoQOracle.tup [[true], [V.dec i ρ pms]])
        (C * (T i + 1))) ∧
  (∀ i, V.coins i ≤ r i) ∧
  (∀ (i : I) (ρ : Fin (V.coins i) → Bool) (pms : List (List Bool)), pms.length = k →
    ((List.range k).map fun j => (V.msg i ρ (pms.take j)).length).sum ≤ ℓV i) ∧
  (∀ i ∈ yes, ∃ P : List (List Bool) → List Bool, 1 - εc i ≤ V.accProb i k (ℓP i) P) ∧
  (∀ i ∈ no, ∀ P : List (List Bool) → List Bool, V.accProb i k (ℓP i) P ≤ εs i)

/-- A verifier is **public-coin** (Arthur–Merlin) with `k` rounds (Jain, Mathialagan, Roy, STOC 2027
submission (manuscript sha256 1af78662…), §4.2.1, p.25: "restricts every verifier message to a
fresh, independent uniform random string, and the verifier's final decision is a deterministic
function of the common input and transcript"): its coins are split into `k` consecutive segments,
its `j`-th message is the `j`-th segment, and all its coins are sent. -/
def IPVerifier.IsPublicCoin {I : Type} (V : IPVerifier I) (k : ℕ) : Prop :=
  ∃ seg : I → ℕ → ℕ, ∀ i, (V.coins i = ∑ j ∈ Finset.range k, seg i j) ∧
    ∀ (ρ : Fin (V.coins i) → Bool) (pms : List (List Bool)), pms.length < k →
      V.msg i ρ pms =
        ((bits ρ).drop (∑ j ∈ Finset.range pms.length, seg i j)).take (seg i pms.length)

/-- `(yes, no) ∈ IP(rounds = k, verifier time = T, prover comm = ℓ_P, verifier comm = ℓ_V, verifier
randomness = r, completeness ≥ 1 − ϵ_c, soundness ≤ ϵ_s)` (Jain, Mathialagan, Roy, STOC 2027
submission (manuscript sha256 1af78662…), §4.2.1, p.25). -/
def InIP {I : Type} (enc : I → List (List Bool)) (yes no : Set I) (k : ℕ) (T ℓP ℓV r : I → ℕ)
    (εc εs : I → ℝ) : Prop :=
  ∃ V : IPVerifier I, V.Proves enc yes no k T ℓP ℓV r εc εs

/-- `(yes, no) ∈ AM(…)` with the same parameters: an interactive proof with a public-coin verifier
(Jain, Mathialagan, Roy, STOC 2027 submission (manuscript sha256 1af78662…), §4.2.1, p.25: "Replacing
IP by AM imposes the additional public-coin restriction"). The class `coAM(…)` of a language `L` is
`AM(…)` for its complement `(L̄, L)` ("coAM denotes the complements of languages in the AM class with
the same parameter values"). -/
def InAM {I : Type} (enc : I → List (List Bool)) (yes no : Set I) (k : ℕ) (T ℓP ℓV r : I → ℕ)
    (εc εs : I → ℝ) : Prop :=
  ∃ V : IPVerifier I, V.IsPublicCoin k ∧ V.Proves enc yes no k T ℓP ℓV r εc εs

end LaconicBarrier


