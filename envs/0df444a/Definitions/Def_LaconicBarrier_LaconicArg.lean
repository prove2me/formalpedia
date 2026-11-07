-- Prove2me | Definitions.Def_LaconicBarrier_LaconicArg
-- name    : LaconicBarrier_LaconicArg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:48.969202+00:00
-- url     : https://prove2.me/theorems/8d34be1b-9630-4c4a-af53-226443c5d434
-- title:
--   Two-message arguments
-- statement:
--   A **two-message argument** $\Pi = (\mathcal V = (\mathcal V_1, \mathcal V_2), \mathcal P)$ consists of
--
--   1. $\mathcal V_1(1^\lambda, x) \to (pk, vk)$, probabilistic: the first message $pk$ and a private verifier state $vk$;
--   2. $\mathcal P(pk, x, w) \to \pi$, probabilistic: the prover message;
--   3. $\mathcal V_2(vk, x, \pi) \to \{0,1\}$, deterministic.
--
--   It is **polynomial-time** if the three algorithms use polynomially many coins and run in time polynomial in their input length. The honest acceptance probability is $\Pr[\mathcal V_2(vk, x, \pi) = 1 : (pk, vk) \leftarrow \mathcal V_1(1^\lambda, x),\ \pi \leftarrow \mathcal P(pk, x, w)]$, and the distribution of $\mathcal P(pk, x, w)$ over its coins is also recorded.
--
--   **Formalization Note** Completeness, the message-length bounds $\ell_V, \ell_P$ and soundness are stated by the theorems that use the argument; succinctness enters only through the bound $\ell_P$ on prover messages (§6, p.37).
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.2, p.16 (Syntax); Definition 4.6 (Completeness)

import Mathlib
import Definitions.Def_LaconicBarrier_PolyTimeOn
import Definitions.Def_LaconicBarrier_coinAvg
import Definitions.Def_QAdvFew_PoQOracle_tup

namespace LaconicBarrier

/-- A **two-message argument** `Π = (V = (V₁, V₂), P)` (Jain, Mathialagan, Roy, *From Succinct
Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript
sha256 1af78662…), §4.1.2, p.16, "Syntax"):

1. `V₁(1^λ, x) → (pk, vk)`, probabilistic, with `vcoins λ x` coins: the first message `pk` and the
   private verifier state `vk`;
2. `P(pk, x, w) → π`, probabilistic, with `pcoins pk x w` coins: the prover message;
3. `V₂(vk, x, π) → {0, 1}`, deterministic.

**Formalization Note** Polynomial time is `LaconicArg.IsPPT`; completeness and the message-length
bounds are stated by the theorems that use the argument (succinctness enters only through an
explicit bound `ℓ_P` on prover messages, §6, p.37). -/
structure LaconicArg where
  /-- the number of coins of `V₁` -/
  vcoins : ℕ → List Bool → ℕ
  /-- the first verifier algorithm, `(pk, vk)` -/
  V1 : (lam : ℕ) → (x : List Bool) → (Fin (vcoins lam x) → Bool) → List Bool × List Bool
  /-- the number of coins of the prover -/
  pcoins : List Bool → List Bool → List Bool → ℕ
  /-- the prover -/
  P : (pk x w : List Bool) → (Fin (pcoins pk x w) → Bool) → List Bool
  /-- the decision `V₂(vk, x, π)` -/
  V2 : List Bool → List Bool → List Bool → Bool

/-- The three algorithms of the argument run in **polynomial time** (Jain, Mathialagan, Roy, STOC
2027 submission (manuscript sha256 1af78662…), §4.1.2, p.16: "specified by the following polynomial
time algorithms"): polynomially many coins, and one machine each for `V₁` (on `(1^λ, x, ρ)`), `P`
(on `(pk, x, w, ρ)`) and `V₂` (on `(vk, x, π)`), each within a polynomial of its input length. -/
def LaconicArg.IsPPT (A : LaconicArg) : Prop :=
  (∃ c : ℕ, ∀ lam x, A.vcoins lam x ≤ (lam + x.length + 2) ^ c) ∧
  (∃ c : ℕ, ∀ pk x w, A.pcoins pk x w ≤ (pk.length + x.length + w.length + 2) ^ c) ∧
  PolyTimeOn (ι := (lam : ℕ) × (x : List Bool) × (Fin (A.vcoins lam x) → Bool))
    (fun i => [unary i.1, i.2.1, bits i.2.2])
    (fun i => QAdvFew.PoQOracle.tup [(A.V1 i.1 i.2.1 i.2.2).1, (A.V1 i.1 i.2.1 i.2.2).2]) ∧
  PolyTimeOn (ι := (pk : List Bool) × (x : List Bool) × (w : List Bool) ×
      (Fin (A.pcoins pk x w) → Bool))
    (fun i => [i.1, i.2.1, i.2.2.1, bits i.2.2.2]) (fun i => A.P i.1 i.2.1 i.2.2.1 i.2.2.2) ∧
  PolyTimeOn (ι := List Bool × List Bool × List Bool) (fun i => [i.1, i.2.1, i.2.2])
    (fun i => [A.V2 i.1 i.2.1 i.2.2])

/-- The probability that the honest verifier accepts the honest prover on `x` with witness `w` at
`λ`: `Pr[V₂(vk, x, π) = 1 : (pk, vk) ← V₁(1^λ, x), π ← P(pk, x, w)]` (Jain, Mathialagan, Roy, STOC
2027 submission (manuscript sha256 1af78662…), Definition 4.6, p.16, Completeness). -/
noncomputable def LaconicArg.honestAcc (A : LaconicArg) (lam : ℕ) (x w : List Bool) : ℝ :=
  coinAvg (A.vcoins lam x) fun ρ =>
    coinAvg (A.pcoins (A.V1 lam x ρ).1 x w) fun ρ' =>
      if A.V2 (A.V1 lam x ρ).2 x (A.P (A.V1 lam x ρ).1 x w ρ') then 1 else 0

/-- The distribution of the honest prover's message `P(pk, x, w)` over its coins. -/
noncomputable def LaconicArg.proverPMF (A : LaconicArg) (pk x w : List Bool) : PMF (List Bool) :=
  (PMF.uniformOfFintype (Fin (A.pcoins pk x w) → Bool)).map (A.P pk x w)

end LaconicBarrier


