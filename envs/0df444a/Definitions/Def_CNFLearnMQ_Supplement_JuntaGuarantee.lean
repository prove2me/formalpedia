-- Prove2me | Definitions.Def_CNFLearnMQ_Supplement_JuntaGuarantee
-- name    : CNFLearnMQ_Supplement_JuntaGuarantee
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:03:40.636005+00:00
-- url     : https://prove2.me/theorems/c939389a-3bf6-4f6f-92c9-ccfd7c44b3e7
-- title:
--   Learning $r$-juntas from uniform examples, and Hypotheses 1.5 and 1.6
-- statement:
--   A **Boolean $r$-junta** is a function $f:\{0,1\}^N\to\{0,1\}$ that depends on at most $r$ input variables. A machine $M$ achieves the **junta-learning guarantee** for $r$ in time $T$ if for all integers $N\ge r$ and every $r$-junta $f$, given $N$ and only independent uniform labeled examples $(X,f(X))$, $X\sim\mathrm{Unif}(\{0,1\}^N)$, it runs within time $T(N)$ (evaluation included) and with probability at least $2/3$ outputs $h:\{0,1\}^N\to\{0,1\}$ with
--   $$\Pr_{X\sim\mathrm{Unif}(\{0,1\}^N)}[h(X)\neq f(X)]\le\frac13.$$
--
--   **Hypothesis 1.5** (weak hardness). For every constant $C>0$ there is an integer $r_0=r_0(C)$ such that for every fixed integer $r\ge r_0$ no randomized algorithm achieves this guarantee in time $O_r(N^C)$.
--
--   **Hypothesis 1.6** (strong hardness). There are constants $c>0$ and $r_0\ge1$ such that for every fixed integer $r\ge r_0$ no randomized algorithm achieves this guarantee in time $O_r(N^{cr})$.
--
--   These are assumptions, not results; Theorem 7.1 derives sample-only lower bounds for learning CNF formulas from them.
--
--   **Formalization Note** "Randomized algorithm" is a sample machine; "in time $O_r(N^C)$" is a constant $K$, chosen after $r$ and before $N$ and $f$, with time at most $K N^C$ for all $N\ge r$. The machine is given $N$ in binary; an example is the bit string $X_1\dots X_N f(X)$. Juntas and the prediction error are the published `OptQJunta.IsJunta` and `OptQJunta.hdist` on $\{0,1\}^N$.
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Hypotheses 1.5 and 1.6, p.5

import Mathlib
import Definitions.Def_CNFLearnMQ_Supplement_SampleMachine
import Definitions.Def_CNFLearnMQ_OProg
import Definitions.Def_OptQJunta_IsFar

set_option autoImplicit false

namespace CNFLearnMQ.Supplement

open CNFLearnMQ SampleMachine

/-- The law of one independent uniform labeled example `(X, f(X))`, `X ∼ Unif({0,1}^N)`, written as
the bit string `X_1 … X_N f(X)`. -/
noncomputable def exampleLaw (N : ℕ) (f : (Fin N → Bool) → Bool) : PMF (List Bool) :=
  (PMF.uniformOfFintype (Fin N → Bool)).map fun X => List.ofFn X ++ [f X]

/-- The guarantee of Hypothesis 1.5 (Feng, Yu, Zhang, STOC 2027 submission (manuscript sha256
519ee6d4…), p.5) for a machine `M`, a junta size `r` and a time bound `T`:
for all integers `N ≥ r` and every Boolean `r`-junta `f : {0,1}^N → {0,1}`, given `N` and only
independent uniform labeled examples of `f`, `M` runs within time `⌊T(N)⌋` including the evaluation
of its output on any input, and with probability at least `2/3` it outputs a hypothesis
`h : {0,1}^N → {0,1}` with `P_X[h(X) ≠ f(X)] ≤ 1/3`.

**Formalization Note** An `r`-junta (a function depending on at most `r` input variables, p.5) is
the published `OptQJunta.IsJunta`, and `P_{X∼Unif({0,1}^N)}[h(X) ≠ f(X)]` is the published uniform
Hamming distance `OptQJunta.hdist` (both on `{0,1}^N = Fin N → Bool`). -/
def JuntaGuarantee (M : SampleMachine) (r : ℕ) (T : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, r ≤ N → ∀ f : (Fin N → Bool) → Bool, OptQJunta.IsJunta f r →
    M.RunsWithin (exampleLaw N f) [N] N ⌊T N⌋₊ ∧
    (2 / 3 : ENNReal) ≤ prob (M.runFor (exampleLaw N f) ⌊T N⌋₊ (M.initCfg [N]))
      (fun o => ∃ c, o = some c ∧ OptQJunta.hdist (M.hypothesis ⌊T N⌋₊ c) f ≤ 1 / 3)

/-- **Hypothesis 1.5** (weak hardness of learning juntas under the uniform distribution, p.5): for
every constant `C > 0` there is an integer `r₀ = r₀(C)` such that for every fixed integer `r ≥ r₀`
no randomized algorithm achieves the guarantee of `JuntaGuarantee` for all `N ≥ r` in time
`O_r(N^C)`.

**Formalization Note** A hypothesis, never proved. "Randomized algorithm" is a `SampleMachine`
(finite control, finitely many stacks, unit cost per step, fair coins, a sample oracle); "in time
`O_r(N^C)`" is a constant `K` (chosen after `r`, before `N` and `f`) with time at most `K·N^C`,
evaluation of the output on any input included. -/
def Hypothesis_1_5 : Prop :=
  ∀ C : ℝ, 0 < C → ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
    ¬ ∃ (M : SampleMachine) (K : ℝ), JuntaGuarantee M r (fun N => K * (N : ℝ) ^ C)

/-- **Hypothesis 1.6** (strong hardness of learning juntas under the uniform distribution, p.5):
there are constants `c > 0` and `r₀ ≥ 1` such that for every fixed integer `r ≥ r₀` no randomized
algorithm achieves the guarantee of Hypothesis 1.5 for all `N ≥ r` in time `O_r(N^{cr})`.
A hypothesis, never proved; same cost model as `Hypothesis_1_5`. -/
def Hypothesis_1_6 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ r₀ : ℕ, 1 ≤ r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
    ¬ ∃ (M : SampleMachine) (K : ℝ), JuntaGuarantee M r (fun N => K * (N : ℝ) ^ (c * r))

end CNFLearnMQ.Supplement


