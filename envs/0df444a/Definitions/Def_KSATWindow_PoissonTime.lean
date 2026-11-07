-- Prove2me | Definitions.Def_KSATWindow_PoissonTime
-- name    : KSATWindow_PoissonTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:32:24.578292+00:00
-- url     : https://prove2.me/theorems/f24e065e-ed8b-4ac2-9438-2499829db249
-- title:
--   Poisson time: $\mathbb E f(F_n(t))$, $s_n(t)$, $\beta_n(t)$ and $q_G(z)$
-- statement:
--   The paper exposes the clauses at the arrival times of an independent rate-one Poisson process $(\Pi_t)_{t\ge0}$ and writes $F_n(t)=F_{n,\Pi_t}$. For a nonnegative function $f$ of the solution set,
--   $$\mathbb E f(F_n(t))=\sum_{m\ge0}e^{-t}\frac{t^m}{m!}\,\mathbb E f(F_{n,m}).$$
--   This module defines this mixture and, from it,
--
--   1. $s_n(t)=\mathbb P(F_n(t)\text{ is satisfiable})$;
--   2. $\beta_n(t)=\mathbb E\big[\mathbf 1\{F_n(t)\text{ is satisfiable}\}\,\ell(F_n(t))/n\big]$, the expected proportion of forced variables before unsatisfiability;
--   3. $q_G(z)$, the probability that adjoining an independent Poisson number of mean $z$ of uniform signed $s$-clauses (the paper uses $s=k-1$) makes the formula with solution set $S$ unsatisfiable.
--
--   **Formalization Note** No Poisson process is built: every statement looks at one time $t$, and the mixture is exactly what independence of $\Pi_t$ and the clauses gives. All expectations take values in $[0,\infty]$.
-- source:
--   Carenini, A polynomial scaling window for random k-SAT and a proof of the satisfiability conjecture, STOC 2027 submission (manuscript sha256 1664cf10…), §2, p.5 (F_n(t), s_n(t)), §3, p.7 (β_n(t)), Lemma 2.1, p.6 (q_G(z))

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_KSATWindow_Forcing
open MeasureTheory ProbabilityTheory OAI.RandomKSAT
open scoped Classical ENNReal

namespace KSATWindow

/-!
# Poisson time: `Fₙ(t)`, `sₙ(t)`, `βₙ(t)` and `q_G(z)`

G. Carenini, *A polynomial scaling window for random k-SAT and a proof of the satisfiability
conjecture*, STOC 2027 submission (manuscript sha256 1664cf10…), §2, p.5, §3, p.7, and Lemma 2.1,
p.6.

The paper exposes the clauses at the arrival times of an independent rate-one Poisson process
`(Π_t)` and writes `Fₙ(t) = F_{n,Π_t}` (p.5).

**Formalization Note.** Every statement of the mission looks at `Fₙ(t)` at a single time `t`, so a
functional of `Fₙ(t)` is encoded by its Poisson mixture: for `f ≥ 0` of the solution set,
`E f(Fₙ(t)) = Σ_{m ≥ 0} e^{-t} t^m / m! · E f(F_{n,m})`, which is what independence of `Π_t` and
the clauses gives. No process object is built. All these expectations take values in `ℝ≥0∞`, so
none of them is a junk value of a non-summable sum. Times are `t ≥ 0` in every statement.
-/

/-- The Poisson probability `P(Π_t = m) = e^{-t} t^m / m!`. -/
noncomputable def poissonWeight (t : ℝ) (m : ℕ) : ℝ :=
  Real.exp (-t) * t ^ m / (m.factorial : ℝ)

/-- `E[f(Fₙ(t))]` for a nonnegative function `f` of the solution set: the Poisson(`t`) mixture of
`E[f(F_{n,m})]` over `m`. -/
noncomputable def poissonMean (n k : ℕ) (t : ℝ) (f : Finset (Assignment n) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' m : ℕ, ENNReal.ofReal (poissonWeight t m) * ∫⁻ ω, f (solutions ω m) ∂(streamLaw n k)

/-- `sₙ(t) = P(τₙ > t) = P(Fₙ(t) is satisfiable)` (p.5). -/
noncomputable def survivalTime (n k : ℕ) (t : ℝ) : ℝ≥0∞ :=
  poissonMean n k t fun S => if S.Nonempty then 1 else 0

/-- `βₙ(t) = E[1{Fₙ(t) is satisfiable} ℓ(Fₙ(t))/n]` (p.7): the expected proportion of forced
variables, counted only before unsatisfiability. -/
noncomputable def beta (n k : ℕ) (t : ℝ) : ℝ≥0∞ :=
  poissonMean n k t fun S =>
    if S.Nonempty then ENNReal.ofReal ((forcedCount S : ℝ) / (n : ℝ)) else 0

/-- `q_G(z)` (Lemma 2.1, p.6), with clause length `s` (the paper uses `s = k − 1`): the probability
that adjoining an independent Poisson number of mean `z` of uniform signed `s`-clauses on `[u]`
makes the formula with solution set `S` unsatisfiable. `blockKill u s S d` is the probability
that `d` independent uniform `s`-clauses kill `S` (published `BlockKilling` vocabulary). -/
noncomputable def shortKill (u s : ℕ) (S : Finset (Assignment u)) (z : ℝ) : ℝ :=
  ∑' d : ℕ, poissonWeight z d * blockKill u s S d

end KSATWindow


