-- Prove2me | Definitions.Def_LaconicBarrier_Supplement_InMIP
-- name    : LaconicBarrier_Supplement_InMIP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:32:24.015755+00:00
-- url     : https://prove2.me/theorems/0a965440-26f6-441a-8409-5562c50cc05b
-- title:
--   Multiprover interactive proofs and the class $\mathsf{MIP}(\dots)$
-- statement:
--   Let $(L_{\mathrm{yes}}, L_{\mathrm{no}})$ be a promise problem and $\epsilon_c, \epsilon_s$ error bounds. A multiprover verifier $V$ is a **multiprover interactive proof** in
--   $$
--   \mathsf{MIP}\bigl(\text{provers} = k',\ \text{verifier time} = T,\ \text{ind prover comm} = \ell_P,\ \text{verifier comm} = \ell_V,\ \text{verifier randomness} = r,\ \text{completeness} \ge 1 - \epsilon_c,\ \text{soundness} \le \epsilon_s\bigr)
--   $$
--   if:
--
--   1. the verifier runs in time $O(T)$ (one machine for every input);
--   2. it uses at most $r$ random bits;
--   3. it questions only provers $j < k'$, each at most once;
--   4. its questions total at most $\ell_V$ bits, and each prover sends at most $\ell_P$ bits;
--   5. **completeness**: on every $i \in L_{\mathrm{yes}}$ some provers are accepted with probability at least $1 - \epsilon_c(i)$;
--   6. **soundness**: on every $i \in L_{\mathrm{no}}$ every tuple of unbounded provers is accepted with probability at most $\epsilon_s(i)$.
--
--   As stated on p.28, these resource bounds hold for every prover strategy and every choice of coins.
--
--   This is the class in the conclusion of Theorem 8.3.
--
--   **Formalization Note** The time bound is per verifier action, computed from the encoded input, the coins and the transcript; with polynomially many actions and polynomial time this is the total time up to a polynomial. Provers may share randomness and agree on joint non-uniform strategies in the paper; such strategies are mixtures of deterministic prover tuples, which are covered, so soundness is unchanged.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.32, p.27, and the class notation, p.28

import Mathlib
import Definitions.Def_LaconicBarrier_Supplement_MIPVerifier

namespace LaconicBarrier.Supplement

/-- The verifier `V` is a **multiprover interactive proof for the promise problem** `(yes, no)`
with the named parameters of the paper (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs:
Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…),
Definition 4.32, p.27, and the class `MIP(provers = k, verifier time = T, ind prover comm = ℓ_P,
verifier comm = ℓ_V, verifier randomness = r, completeness ≥ 1 − ϵ_c, soundness ≤ ϵ_s)`, p.28:
"at most `k(n)` provers, verifier time `O(T(n))`, at most `ℓ_P(n)` bits sent by each prover, total
verifier communication `ℓ_V(n)`, and at most `r(n)` verifier random bits. Resource bounds hold for
every prover strategy and every choice of coins"):
1. **verifier time `O(T)`**: one machine computes each verifier action from `(encoded input, coins,
   transcript so far)` within `C · (T(i) + 1)` steps, for a constant `C`, on every consistent
   transcript whose replies have at most `ℓ_P` bits;
2. **verifier randomness** at most `r(i)` coins;
3. **at most `k` provers, one round trip each**: every question goes to a prover `j < k(i)` that has
   not been asked before;
4. **verifier communication** at most `ℓ_V(i)` bits in total;
5. **individual prover communication** at most `ℓ_P(i)` bits per prover (a longer reply is rejected,
   `MIPVerifier.accProb`);
6. **completeness**: on every `i ∈ yes` some provers are accepted with probability `≥ 1 − ϵ_c(i)`;
7. **soundness**: on every `i ∈ no` all provers are accepted with probability `≤ ϵ_s(i)`.

**Formalization Note** Provers are given by their reply distributions to their single question, with
independent private coins. Shared randomness and joint non-uniform strategies (p.27) are mixtures of
deterministic prover tuples, which are covered, so soundness against these strategies is soundness
against the paper's provers. The time bound is per verifier action; the protocols of the mission have
polynomial time and at most polynomially many actions, so this is the total time up to a polynomial.
Bounds are functions of the input itself, so a bound in the statement length `n` of a structured input
is a special case. -/
def MIPVerifier.Proves {I : Type} (V : MIPVerifier I) (enc : I → List (List Bool))
    (yes no : Set I) (kP T ℓP ℓV r : I → ℕ) (εc εs : I → ℝ) : Prop :=
  (∃ (C : ℕ) (M : KarpLiptonOM.OracleTM), ∀ (i : I) (ρ : Fin (V.coins i) → Bool)
      (h : List (ℕ × List Bool × List Bool)), V.Consistent i ρ h →
      (∀ e ∈ h, e.2.2.length ≤ ℓP i) →
      RunsWithin M (enc i ++ [bits ρ, QAdvFew.PoQOracle.tup (h.map mipEntryCode)])
        (V.next i ρ h).code (C * (T i + 1))) ∧
  (∀ i, V.coins i ≤ r i) ∧
  (∀ (i : I) (ρ : Fin (V.coins i) → Bool) (h : List (ℕ × List Bool × List Bool)) (j : ℕ)
    (q : List Bool), V.Consistent i ρ h → V.next i ρ h = .ask j q →
      j < kP i ∧ j ∉ h.map Prod.fst) ∧
  (∀ (i : I) (ρ : Fin (V.coins i) → Bool) (h : List (ℕ × List Bool × List Bool)) (j : ℕ)
    (q : List Bool), V.Consistent i ρ h → V.next i ρ h = .ask j q →
      (h.map fun e => e.2.1.length).sum + q.length ≤ ℓV i) ∧
  (∀ i ∈ yes, ∃ P : ℕ → List Bool → PMF (List Bool), 1 - εc i ≤ V.accProb i (kP i) (ℓP i) P) ∧
  (∀ i ∈ no, ∀ P : ℕ → List Bool → PMF (List Bool), V.accProb i (kP i) (ℓP i) P ≤ εs i)

/-- `(yes, no) ∈ MIP(provers = k, verifier time = T, ind prover comm = ℓ_P, verifier comm = ℓ_V,
verifier randomness = r, completeness ≥ 1 − ϵ_c, soundness ≤ ϵ_s)` (Jain, Mathialagan, Roy, STOC
2027 submission (manuscript sha256 1af78662…), p.28). -/
def InMIP {I : Type} (enc : I → List (List Bool)) (yes no : Set I) (kP T ℓP ℓV r : I → ℕ)
    (εc εs : I → ℝ) : Prop :=
  ∃ V : MIPVerifier I, V.Proves enc yes no kP T ℓP ℓV r εc εs

end LaconicBarrier.Supplement


