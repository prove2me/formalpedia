-- Prove2me | Definitions.Def_LaconicBarrier_WEScheme
-- name    : LaconicBarrier_WEScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:37.801789+00:00
-- url     : https://prove2.me/theorems/13b8e641-051c-4ea4-adb8-07147fda19b5
-- title:
--   Witness encryption for one-bit messages
-- statement:
--   A **witness encryption scheme** for one-bit messages consists of probabilistic algorithms $\mathrm{Enc}(1^\lambda, x, \mu) \to ct$ for $\mu \in \{0,1\}$ and $\mathrm{Dec}(ct, w) \to \mu'$, where an output other than a single bit is the failure symbol $\bot$.
--
--   $(\mathrm{Enc}, \mathrm{Dec})$ is a witness encryption scheme for the relation $\mathcal R$, as far as the lower bound uses it, if
--
--   1. both algorithms are probabilistic polynomial-time;
--   2. **correctness**: there is a negligible $\kappa$ such that for all $\lambda$, all $(x, w) \in \mathcal R$ and all $\mu$,
--   $$
--   \Pr\bigl[\mathrm{Dec}(\mathrm{Enc}(1^\lambda, x, \mu), w) = \mu\bigr] \ge 1 - \kappa(\lambda).
--   $$
--
--   **Formalization Note** Negligible is written as: for every $e$, for all large $\lambda$ the error is at most $(\lambda+2)^{-e}$ uniformly in $x, w, \mu$. Security is not part of this definition: the lower bound never uses it, and the security game is the reduction's source family.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.4, p.18, Definition 4.8; §7.1, p.45

import Mathlib
import Definitions.Def_LaconicBarrier_PolyTimeOn
import Definitions.Def_LaconicBarrier_coinAvg

namespace LaconicBarrier

/-- A **witness encryption scheme for one-bit messages** (Jain, Mathialagan, Roy, *From Succinct
Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript
sha256 1af78662…), §4.1.4, p.18, "Syntax"; §7.1, p.45: "supporting one-bit messages"):

1. `Enc(1^λ, x, µ) → ct`, probabilistic with `ecoins λ x` coins, for `µ ∈ {0, 1}`;
2. `Dec(ct, w) → µ′`, probabilistic with `dcoins ct w` coins; the output `[µ′]` is the message, any
   other string is the failure symbol `⊥`. -/
structure WEScheme where
  /-- the number of coins of `Enc` -/
  ecoins : ℕ → List Bool → ℕ
  /-- encryption of a bit under a statement -/
  Enc : (lam : ℕ) → (x : List Bool) → Bool → (Fin (ecoins lam x) → Bool) → List Bool
  /-- the number of coins of `Dec` -/
  dcoins : List Bool → List Bool → ℕ
  /-- decryption with a witness -/
  Dec : (ct w : List Bool) → (Fin (dcoins ct w) → Bool) → List Bool

/-- `Pr[Dec(Enc(1^λ, x, µ), w) = µ]` over the coins of both algorithms. -/
noncomputable def WEScheme.decProb (E : WEScheme) (lam : ℕ) (x : List Bool) (mu : Bool)
    (w : List Bool) : ℝ :=
  coinAvg (E.ecoins lam x) fun ρ =>
    coinAvg (E.dcoins (E.Enc lam x mu ρ) w) fun ρ' =>
      if E.Dec (E.Enc lam x mu ρ) w ρ' = [mu] then 1 else 0

/-- `(Enc, Dec)` is a **witness encryption scheme** for the relation `R`, as far as the paper's
lower bound uses it (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript sha256 1af78662…),
Definition 4.8, p.18):

1. `Enc` and `Dec` are probabilistic polynomial-time: polynomially many coins and one machine each,
   on `(1^λ, x, µ, ρ)` and `(ct, w, ρ)`, within a polynomial of the input length;
2. **correctness**: there is a negligible `κ` with `Pr[Dec(Enc(1^λ, x, µ), w) = µ] ≥ 1 − κ(λ)` for all
   `λ`, all `(x, w) ∈ R` and all `µ`; written as: for every `e`, for all large `λ` the error is at
   most `(λ + 2)^{-e}`, uniformly in `x, w, µ`.

**Formalization Note** Security is not part of this definition: the lower bound never uses it (the
security game is the source family `WEScheme.source` of the reduction). -/
def WEScheme.IsWE (E : WEScheme) (Rel : List Bool → List Bool → Prop) : Prop :=
  (∃ c : ℕ, ∀ lam x, E.ecoins lam x ≤ (lam + x.length + 2) ^ c) ∧
  (∃ c : ℕ, ∀ ct w, E.dcoins ct w ≤ (ct.length + w.length + 2) ^ c) ∧
  PolyTimeOn (ι := (lam : ℕ) × (x : List Bool) × Bool × (Fin (E.ecoins lam x) → Bool))
    (fun i => [unary i.1, i.2.1, [i.2.2.1], bits i.2.2.2])
    (fun i => E.Enc i.1 i.2.1 i.2.2.1 i.2.2.2) ∧
  PolyTimeOn (ι := (ct : List Bool) × (w : List Bool) × (Fin (E.dcoins ct w) → Bool))
    (fun i => [i.1, i.2.1, bits i.2.2]) (fun i => E.Dec i.1 i.2.1 i.2.2) ∧
  ∀ e : ℕ, ∀ᶠ lam : ℕ in Filter.atTop, ∀ (x w : List Bool) (mu : Bool), Rel x w →
    1 - (((lam : ℝ) + 2) ^ e)⁻¹ ≤ E.decProb lam x mu w

end LaconicBarrier


