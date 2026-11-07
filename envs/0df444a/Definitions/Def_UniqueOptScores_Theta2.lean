-- Prove2me | Definitions.Def_UniqueOptScores_Theta2
-- name    : UniqueOptScores_Theta2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:28:14.020444+00:00
-- url     : https://prove2.me/theorems/bf476e2d-8646-4a8b-a8e7-bdb32c8247d3
-- title:
--   The class $\Theta^{\mathrm P,A}_2 = \mathrm P^{\mathrm{NP}^A}_{\parallel}$
-- statement:
--   A language $L$ belongs to $\Theta^{\mathrm P,A}_2$ if there are a fixed language $K \in \mathrm{NP}^A$ and two clocked deterministic oracle machines, a query generator $T$ and a decision machine $E$, both with access to $A$, such that
--   $$
--   x \in L \iff E^A\big(\langle x, ([y_1 \in K], \dots, [y_m \in K])\rangle\big) \text{ accepts},
--   $$
--   where $(y_1, \dots, y_m)$ is the list output by $T^A$ on $x$. All queries to the $\mathrm{NP}^A$ language are prepared before any answer is received, the final decision may depend on the whole answer vector, and queries to $A$ may be adaptive.
--
--   **Formalization Note** Truth-table form of polynomially many nonadaptive queries; $E$ sees $x$ and the answer vector and may recompute $T$. This is the paper's convention $\Theta^{\mathrm P,A}_2 := \mathrm P^{\mathrm{NP}^A}_\parallel$ with direct access to $A$.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 3.2, p.14 (Bounded access to NP); Definition 3.1, p.15

import Mathlib
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_UniqueOptScores_IsClocked
import Definitions.Def_UniqueOptScores_output
import Definitions.Def_UniqueOptScores_pair
import Definitions.Def_UniqueOptScores_decodeList
import Definitions.Def_UniqueOptScores_NP

namespace UniqueOptScores

/-- **The class Θ^{P,A}_2 = P^{NP^A}_∥ (parallel access).**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Definition 3.1, p.15: "Θ^{P,A}_2 := P^{NP^A}_∥ . Here the deterministic polynomial-time
computation has direct access to A and makes polynomially many nonadaptive queries to a fixed
language in NP^A. Queries to A may be adaptive; all queries to the NP^A language must be prepared
before any of their answers are received"; p.14: "the final decision may depend on the entire
answer vector".

`L ∈ Theta2 A` if there are `K ∈ NP A` and clocked machines `T` (query generator) and `E`
(decision), both with oracle `A`, such that `x ∈ L` exactly when `E` accepts `⟨x, a⟩`, where `a`
is the answer vector `([y₁ ∈ K], …, [y_m ∈ K])` for the list `(y₁, …, y_m)` output by `T` on `x`.

**Formalization Note.** Truth-table form of nonadaptive access: all NP^A queries are produced by
`T` before any answer is seen; `E` sees `x` and the whole answer vector and may recompute `T`. -/
def Theta2 (A : Set (List Bool)) : Set (Set (List Bool)) :=
  {L | ∃ K ∈ NP A, ∃ (T E : HMBinPacking.OracleMachine) (tT tE : Polynomial ℕ),
    IsClocked T tT ∧ IsClocked E tE ∧
    ∀ x : List Bool, x ∈ L ↔
      output E A (pair x ((decodeList (output T A x)).map
        (fun y => @decide (y ∈ K) (Classical.propDecidable _)))) = [true]}

end UniqueOptScores


