-- Prove2me | Definitions.Def_SeededShannon_Supplement_OAdv
-- name    : SeededShannon_Supplement_OAdv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:40:57.544205+00:00
-- url     : https://prove2.me/theorems/c70c562e-44d0-4f93-b1cf-423d74880aaf
-- title:
--   Nonuniform adaptive oracle adversaries
-- statement:
--   An **oracle adversary** $\mathcal A$ consists, for every security parameter $\lambda$, of a circuit $\mathcal A_\lambda$ and a number $q(\lambda)$ of oracle queries. On input $u$ with oracle access to $\mathcal O$, round $j<q(\lambda)$ evaluates $\mathcal A_\lambda$ on $(u,a_1,\dots,a_j)$, the answers received so far, to obtain the next query $Q_{j+1}$, and receives $a_{j+1}=\mathcal O(Q_{j+1})$; after $q(\lambda)$ answers the same circuit's output is the adversary's output. The adversary has polynomial size if its input length, circuit size and number of queries are at most $(\lambda+2)^c$.
--
--   This is the adversary model of the random-oracle results (Definition 7.16 and Theorem 7.18): adversaries make polynomially many adaptive queries.
--
--   **Formalization Note** Strings are fed and read with the published padding conventions of `LaconicBarrier`; a randomized adversary is matched by its best coins.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Definition 7.16, p.54 (PDF p.57)

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit
import Definitions.Def_QAdvFew_PoQOracle_tup

set_option autoImplicit false

namespace SeededShannon.Supplement

open LaconicBarrier

/-- A **nonuniform adaptive oracle adversary** (Dujmovic, Lu, Silbak, Wichs, STOC 2027 submission
(manuscript sha256 52f4b606…a769709), Definition 7.16, p.54: "In the random-oracle model, the
adversary has oracle access throughout the experiment. The adversary may make arbitrary
polynomially many oracle queries"): for every `λ` a multi-output circuit `A_λ` with `inLen λ` inputs
and a number `q(λ)` of oracle queries. Run on an input `u` with an oracle, round `j < q` evaluates
`A_λ` on `(u, a₁, …, a_j)` (the answers so far) to obtain the next query; after `q` answers the same
circuit's output is the adversary's output.

**Formalization Note** Strings are fed as `padIn` and outputs read with `unpadOut`, as for the
published `CircFamily`. Adversaries are deterministic: a randomized one is matched by its best
coins. -/
structure OAdv where
  /-- the number of inputs of `A_λ` -/
  inLen : ℕ → ℕ
  /-- the number of oracle queries `q(λ)` -/
  q : ℕ → ℕ
  /-- the circuit `A_λ` -/
  circ : (lam : ℕ) → MCircuit (inLen lam)

/-- The adversary has **polynomial size**: inputs, circuit size and number of queries at most
`(λ + 2)^c`. -/
def OAdv.IsPoly (A : OAdv) : Prop :=
  ∃ c : ℕ, ∀ lam, A.inLen lam ≤ (lam + 2) ^ c ∧ (A.circ lam).size ≤ (lam + 2) ^ c ∧
    A.q lam ≤ (lam + 2) ^ c

/-- The output of the adversary at `λ` on input `u` with oracle `O`, after `q(λ)` adaptive queries. -/
def OAdv.run (A : OAdv) (lam : ℕ) (O : List Bool → List Bool) (u : List Bool) : List Bool :=
  let step : List (List Bool) → List Bool := fun ans =>
    unpadOut ((A.circ lam).eval (padIn (A.inLen lam) (QAdvFew.PoQOracle.tup (u :: ans))))
  step ((List.range (A.q lam)).foldl (fun ans _ => ans ++ [O (step ans)]) [])

end SeededShannon.Supplement


