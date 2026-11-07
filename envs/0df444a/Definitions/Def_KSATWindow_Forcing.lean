-- Prove2me | Definitions.Def_KSATWindow_Forcing
-- name    : KSATWindow_Forcing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:10.141912+00:00
-- url     : https://prove2.me/theorems/dbf71f1b-26f8-4709-b062-9b31fc6411c9
-- title:
--   Solution sets $F_{n,m}$, $\Gamma_n$, forced-variable count $\ell$ and kill probability $\rho_j$
-- statement:
--   A formula enters every quantity of the paper only through its set $S\subseteq\{0,1\}^n$ of satisfying assignments. This module defines:
--
--   1. the solution set of $F_{n,m}=C_1\wedge\dots\wedge C_m$;
--   2. the solution set of the last satisfiable formula $\Gamma_n=F_{n,T_n-1}$;
--   3. $\ell(S)$, the number of variables that take the same value on all of $S$ (forced variables);
--   4. $\rho_j(S)$, the fraction of signed $j$-clauses on $[n]$ that are falsified by every point of $S$, i.e. the probability that one uniform signed $j$-clause makes the formula unsatisfiable.
--
--   These are the quantities through which the paper measures how close a formula is to unsatisfiability.
--
--   **Formalization Note** $\ell$ reuses the published `frozen`, which is all of $[n]$ at $S=\varnothing$, and $\rho_j(\varnothing)=1$; the paper defines both only for satisfiable formulas, and every statement of the mission guards them by $S\neq\varnothing$. $T_n$ is read through $\mathbb N_\infty\to\mathbb N$; $T_n=\infty$ is a null event for $n\ge k$.
-- source:
--   Carenini, A polynomial scaling window for random k-SAT and a proof of the satisfiability conjecture, STOC 2027 submission (manuscript sha256 1664cf10…), pp.3–5 (ℓ, ρ_j), p.2 (F_{n,m}), p.3 and p.8 (Γ_n)

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
open MeasureTheory ProbabilityTheory OAI.RandomKSAT
open scoped Classical

namespace KSATWindow

/-!
# Solution sets, forced variables and kill probabilities

G. Carenini, *A polynomial scaling window for random k-SAT and a proof of the satisfiability
conjecture*, STOC 2027 submission (manuscript sha256 1664cf10…), pp.3–5 and §2, p.5.

A formula `G` on `[n]` enters every quantity of the paper only through its set of satisfying
assignments ("The formula G need not be a k-CNF", p.5), so these objects take the solution set
`S : Finset (Assignment n)`; `G` is satisfiable iff `S` is nonempty.

**Formalization Note.**
* `forcedCount S` is the number of variables with the same value in every satisfying assignment,
  the paper's `ℓ(G)` (p.4). It reuses `OAI.RandomKSAT.frozen`, which is all of `[n]` at `S = ∅`;
  the paper defines `ℓ` only for satisfiable formulas, and every statement of the mission guards
  it by `S.Nonempty`.
* `rho n j S` is the fraction of signed `j`-clauses that falsify every point of `S`, the paper's
  `ρ_j(G)` (p.5). It is `1` at `S = ∅`; it is used only for nonempty `S`.
* A clause `c` is satisfied by `a` when `a` agrees with `c` at one of its variables
  (`OAI.RandomKSAT.Satisfies`), so a clause kills `S` when it disagrees with every point of `S`
  at each of its variables, the paper's "disagree with their values" (p.5).
-/

/-- The solution set of `F_{n,m} = C₁ ∧ ⋯ ∧ C_m` (p.2): the assignments satisfying the first `m`
clauses `ω 0, …, ω (m-1)` of the stream. -/
noncomputable def solutions {n k : ℕ} (ω : Stream n k) (m : ℕ) : Finset (Assignment n) :=
  Finset.univ.filter fun a => ∀ i < m, Satisfies (ω i) a

/-- The solution set of `Γₙ = F_{n,Tₙ−1}` (p.3, p.8), the last satisfiable formula of the
process. `Tₙ` is read as `(firstFailure ω).toNat`; `Tₙ ≥ 1` because the empty formula is
satisfiable, and `Tₙ = ∞` is a null event for `k ≤ n`. -/
noncomputable def lastSatisfiable {n k : ℕ} (ω : Stream n k) : Finset (Assignment n) :=
  solutions ω ((firstFailure ω).toNat - 1)

/-- `ℓ(G)` (p.4): the number of coordinates fixed throughout the solution set `S`. -/
noncomputable def forcedCount {n : ℕ} (S : Finset (Assignment n)) : ℕ :=
  (frozen S).card

/-- `ρ_j(G)` (p.5): the probability that one uniform signed `j`-clause makes the formula with
solution set `S` unsatisfiable. -/
noncomputable def rho (n j : ℕ) (S : Finset (Assignment n)) : ℝ :=
  ((Finset.univ.filter fun c : Clause n j => Kills S c).card : ℝ) /
    (Fintype.card (Clause n j) : ℝ)

end KSATWindow


