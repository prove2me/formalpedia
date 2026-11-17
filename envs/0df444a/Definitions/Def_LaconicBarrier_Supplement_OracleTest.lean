-- Prove2me | Definitions.Def_LaconicBarrier_Supplement_OracleTest
-- name    : LaconicBarrier_Supplement_OracleTest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:33:37.064245+00:00
-- url     : https://prove2.me/theorems/1fb69e07-69b5-4b9a-b482-bdaeb08b8358
-- title:
--   Oracle tests for a proof system at length $n$
-- statement:
--   Fix $\lambda$, $n$ and a proof system $\Pi = (G, P, V)$ for a relation $\mathcal R_L$. A **stateless oracle** $O$ answers each query $\mathsf{crs}$ with a pair $(x, \pi) \leftarrow O(\mathsf{crs})$, using fresh coins on each call. $O$ is a **false-statement oracle** if every pair it outputs has $|x| = n$ and $x \notin L$. For a distribution $D_Y$ on $L \cap \{0,1\}^n$ and witnesses $w(x)$ on its support, the **honest oracle** $H_{D_Y, w}$ samples $x \leftarrow D_Y$ and returns $(x, P(\mathsf{crs}, x, w(x)))$. Neither $D_Y$ nor $w$ needs to be efficiently computable.
--
--   An **oracle test** for $\Pi$ at length $n$ with completeness error $\epsilon_c$ and soundness error $\epsilon_s$ is an oracle algorithm $V'$ with
--   $$
--   \Pr\bigl[V'^{H_{D_Y, w}} \text{ accepts}\bigr] \ge 1 - \epsilon_c \quad\text{and}\quad \Pr\bigl[V'^{O} \text{ accepts}\bigr] \le \epsilon_s
--   $$
--   for every $D_Y$ and $w$ as above and every possibly unbounded false-statement oracle $O$.
--
--   Theorem A.5 turns such a test with short proofs into small circuits for $L$.
--
--   **Formalization Note** $V'$ is given by its number of coins and its next action (a query or a decision) as a function of its coins and the replies so far; it is run for a fixed number of actions, with $k + 1$ enough for at most $k$ queries. Proofs together with a failure symbol are encoded in $\ell_P + 1$ bits (p.73), so the replies of a false-statement oracle carry at most $\ell_P + 1$ bits of proof.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §A.3 and Definition A.3, p.73

import Mathlib
import Definitions.Def_LaconicBarrier_Supplement_SNARG

namespace LaconicBarrier.Supplement

/-- An action of an oracle test: query the oracle on `crs`, or stop with the decision `b`. -/
inductive OTAct where
  | query (crs : List Bool)
  | stop (b : Bool)

/-- The code of an oracle-test action (a tagged tuple). -/
def OTAct.code : OTAct → List Bool
  | .query crs => QAdvFew.PoQOracle.tup [[false], crs]
  | .stop b => QAdvFew.PoQOracle.tup [[true], [b]]

/-- The code of the replies `(x, π)` received so far by an oracle test. -/
def otViewCode (h : List (List Bool × List Bool)) : List Bool :=
  QAdvFew.PoQOracle.tup (h.map fun r => QAdvFew.PoQOracle.tup [r.1, r.2])

/-- An **oracle algorithm** for an oracle test (Jain, Mathialagan, Roy, *From Succinct Arguments to
Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256
1af78662…), §A.3, p.73, Definition A.3): with `coins` coins `ρ` and the oracle's replies `(x, π)` so
far, `next` gives its next query `crs` or its decision. Its input `(λ, n)` is fixed. -/
structure OracleTest where
  /-- the number of coins -/
  coins : ℕ
  /-- the next action from the coins and the replies so far -/
  next : (Fin coins → Bool) → List (List Bool × List Bool) → OTAct

/-- One execution against the stateless oracle `O` (`crs` ↦ distribution of the reply `(x, π)`,
fresh coins on each call), for at most `fuel` more actions; running out of actions rejects. -/
noncomputable def OracleTest.exec (V : OracleTest) (ρ : Fin V.coins → Bool)
    (O : List Bool → PMF (List Bool × List Bool)) :
    ℕ → List (List Bool × List Bool) → PMF Bool
  | 0, _ => PMF.pure false
  | f + 1, h =>
    match V.next ρ h with
    | .stop b => PMF.pure b
    | .query crs => (O crs).bind fun r => V.exec ρ O f (h ++ [r])

/-- `Pr[V′^O accepts]`, over the test's coins and the oracle's coins, running for `fuel` actions. -/
noncomputable def OracleTest.accProb (V : OracleTest) (O : List Bool → PMF (List Bool × List Bool))
    (fuel : ℕ) : ℝ :=
  (((PMF.uniformOfFintype (Fin V.coins → Bool)).bind fun ρ => V.exec ρ O fuel []) true).toReal

/-- The **honest oracle** `H_{D_Y, w}` (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript
sha256 1af78662…), Definition A.3, p.73: "samples `x ← D_Y` and returns `(x, P(crs, x, w(x)))`"). -/
noncomputable def honestOracleT (S : SNARG) (DY : PMF (List Bool)) (w : List Bool → List Bool) :
    List Bool → PMF (List Bool × List Bool) :=
  fun crs => DY.bind fun x => (S.proverPMF crs x (w x)).map fun π => (x, π)

/-- `V` is an **oracle test for `Π` at length `n`** with completeness error `ϵ_c` and soundness error
`ϵ_s` (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript sha256 1af78662…), Definition A.3,
p.73): `Pr[V′^{H_{D_Y,w}} accepts] ≥ 1 − ϵ_c` for every distribution `D_Y` on `L ∩ {0,1}ⁿ` and every
choice of witnesses `w(x)` on its support, and `Pr[V′^O accepts] ≤ ϵ_s` for every possibly unbounded
false-statement oracle `O` (every pair it outputs has `|x| = n` and `x ∉ L`). Neither `D_Y` nor `w`
need be efficiently computable.

**Formalization Note** "Proofs together with a failure symbol are encoded in `ℓ_P + 1` bits"
(p.73): the replies of a false-statement oracle carry a string `π` of at most `ℓ_P + 1` bits. The test
is run for `fuel` actions; with at most `k` queries, `fuel = k + 1` runs it to completion. -/
def OracleTest.IsTest (V : OracleTest) (S : SNARG) (Rel : List Bool → List Bool → Prop)
    (n ℓP fuel : ℕ) (εc εs : ℝ) : Prop :=
  (∀ (DY : PMF (List Bool)) (w : List Bool → List Bool),
    (∀ x ∈ DY.support, x.length = n ∧ Rel x (w x)) →
      1 - εc ≤ V.accProb (honestOracleT S DY w) fuel) ∧
  (∀ O : List Bool → PMF (List Bool × List Bool),
    (∀ crs, ∀ r ∈ (O crs).support, r.1.length = n ∧ r.1 ∉ Lang Rel ∧ r.2.length ≤ ℓP + 1) →
      V.accProb O fuel ≤ εs)

end LaconicBarrier.Supplement


