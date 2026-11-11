-- Prove2me | Definitions.Def_ForestRoundingNSW_Rounding_BalancedRounding
-- name    : ForestRoundingNSW_Rounding_BalancedRounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:50:22.940716+00:00
-- url     : https://prove2.me/theorems/2aeb21d2-b228-4151-a4a1-b86bb2f16d78
-- title:
--   Algorithm 1 (balanced individual rounding), its reweighted conditioned runs, and C = 2/(e ln 2) (§3.2–3.3)
-- statement:
--   Let $f:2^X\to\mathbb R$ with multilinear extension $F$, and let $x\in[0,1]^X$. A coordinate $j$ of $y$ is **fractional** if $0<y_j<1$. **Algorithm 1** starts at $y=x$:
--
--   * while at least two coordinates are fractional, choose two fractional coordinates $r\ne s$. If $\partial_rF(y)=\partial_sF(y)=0$, set $y_r$ to $1$ with probability $y_r$ and to $0$ otherwise. Otherwise let $d=\partial_sF(y)\,e_r-\partial_rF(y)\,e_s$, let $\lambda_+,\lambda_-$ be maximal with $y+\lambda_+d,\ y-\lambda_-d\in[0,1]^X$, and move to $y+\lambda_+d$ with probability $\lambda_-/(\lambda_++\lambda_-)$, to $y-\lambda_-d$ otherwise;
--   * if one fractional coordinate $j$ remains, set $y_j$ to $1$ with probability $y_j$ and to $0$ otherwise;
--   * return $S=\{j: y_j=1\}$.
--
--   Each executed loop iteration and the final single-coordinate choice is one **rounding step**. The pair $(r,s)$ is named by a **choice rule** $\rho$, a function of the current $y$ returning two distinct fractional coordinates whenever there are at least two (`IsChoiceRule`). `alg1Run f ρ x` is the run with a budget of $|X|$ rounding steps, returning the output and whether the run finished (no fractional coordinate left); `alg1Law f ρ x` is the law of $S$.
--
--   The **conditioned runs** of Algorithm 2 (line 7) replace the probability $q$ of every transition $z\to w$ by $q\,w_p/z_p$ (conditioning on $p\in S$) or by $q\,(1-w_p)/(1-z_p)$ (conditioning on $p\notin S$); `condLaw f ρ x p b` is the law of the output of that run. The constant is
--   $$C=\frac{2}{e\ln 2}.$$
--   `expect P g` $=\sum_a P(a)g(a)$ and `prob P E` are expectation and probability under a law on a finite type.
--
--   **Formalization Note.** Laws are `PMF`s built by recursion on the rounding steps; every step is a two-point move to `up` with probability $q$ (times the reweighting, clamped to $[0,1]$) and to `down` with the complementary probability. On every state the runs reach the clamp never acts and the reweighted probabilities of the two endpoints add up to $1$. $\lambda_\pm$ are `sSup`s of closed bounded sets in the branch where $d\ne0$. The single remaining fractional coordinate is taken by `Classical.choose`, which is unique there.
-- source:
--   Feng, Hu, Li, Zhang, Correlated Forest Rounding for Unweighted Nash Social Welfare, STOC 2027 submission (manuscript sha256 0c7af642…), p. 19, Lemma 3.2; p. 20, Algorithm 1; p. 23, Algorithm 2 line 7; p. 24, §3.3

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_ForestRoundingNSW_Rounding_SetFunctions

/-!
# Algorithm 1 (balanced individual rounding) and its conditioned variant

Feng, Hu, Li, Zhang, *Correlated Forest Rounding for Unweighted Nash Social Welfare*, STOC 2027
submission (manuscript sha256 0c7af642…): Lemma 3.2 (p. 19, `C := 2/(e ln 2)`), Algorithm 1
(p. 20), Algorithm 2 line 7 (p. 23, the reweighted transitions), §3.3 "Sampling conditional on
one item" (p. 24).

Algorithm 1, from the state `y ∈ [0, 1]^X` (a coordinate is fractional when `0 < y_j < 1`):
* while at least two coordinates are fractional, a choice rule `ρ` names two fractional
  coordinates `r ≠ s`. If `∂_r F(y) = ∂_s F(y) = 0`, `y_r` is set to `1` with probability `y_r`
  and to `0` otherwise. Otherwise `d := ∂_s F(y) e_r − ∂_r F(y) e_s`, `λ₊` and `λ₋` are the
  maximal `λ ≥ 0` with `y + λ d ∈ [0, 1]^X`, resp. `y − λ d ∈ [0, 1]^X`, and the next state is
  `y + λ₊ d` with probability `λ₋/(λ₊ + λ₋)` and `y − λ₋ d` otherwise;
* if exactly one coordinate `j` is fractional, `y_j` is set to `1` with probability `y_j` and to
  `0` otherwise;
* the output is `{j : y_j = 1}`.

Encoding.
* Each executed while-iteration and the final single-coordinate choice is one **rounding step**:
  a two-point move `(q, up, down)` to `up` with probability `q` and to `down` otherwise.
* `runAlg1 f ρ wt k y` runs at most `k` rounding steps from `y` and returns the output set and a
  flag `finished`, true iff no fractional coordinate is left. A step whose original probability
  of `up` is `q` instead goes to `up` with probability `q · wt y up` (clamped to `[0, 1]`) and to
  `down` with the complementary probability. `wt = 1` is Algorithm 1. `condWeight p true`
  (`w_p / z_p`) and `condWeight p false` (`(1 − w_p)/(1 − z_p)`) are the reweightings of
  Algorithm 2, line 7, for a run conditioned on `p ∈ S`, resp. `p ∉ S`; on every state these runs
  reach, the reweighted probabilities of the two endpoints add up to `1`.
* `alg1Run f ρ x` is the run with a budget of `|X|` rounding steps; `alg1Law f ρ x` is the law
  of its output set. "The algorithm uses at most `|X|` rounding steps" is "every outcome of
  `alg1Run` is finished". `condLaw f ρ x p b` is the law of the conditioned run, with the same
  budget.
* A choice rule is any function `ρ` of the current state naming two distinct fractional
  coordinates whenever there are at least two (`IsChoiceRule`); the paper leaves the choice open.
* `expect P g` is the expectation `∑_a P(a) g(a)` over a finite type, and `prob P E` the
  probability of the event `E`.
-/

namespace ForestRoundingNSW.Rounding

open NonmonotoneSubmod.Shared

/-- The constant `C = 2/(e ln 2)` of Lemma 3.2 and Proposition 3.4. -/
noncomputable def C : ℝ :=
  2 / (Real.exp 1 * Real.log 2)

variable {X : Type} [Fintype X] [DecidableEq X]

open Classical in
/-- The fractional coordinates of `y`: those with `0 < y_j < 1`. -/
noncomputable def fracSet (y : X → ℝ) : Finset X :=
  Finset.univ.filter fun j => 0 < y j ∧ y j < 1

open Classical in
/-- The output set `{j : y_j = 1}`. -/
noncomputable def roundedSet (y : X → ℝ) : Finset X :=
  Finset.univ.filter fun j => y j = 1

/-- A choice rule names two distinct fractional coordinates whenever there are at least two. -/
def IsChoiceRule (ρ : (X → ℝ) → X × X) : Prop :=
  ∀ y : X → ℝ, 2 ≤ (fracSet y).card →
    (ρ y).1 ≠ (ρ y).2 ∧ (ρ y).1 ∈ fracSet y ∧ (ρ y).2 ∈ fracSet y

/-- A coin that shows `true` with probability `p` (clamped to `[0, 1]`). -/
noncomputable def coin (p : ℝ) : PMF Bool :=
  PMF.ofFintype
    (fun b => if b then ((min (Real.toNNReal p) 1 : NNReal) : ENNReal)
      else 1 - ((min (Real.toNNReal p) 1 : NNReal) : ENNReal))
    (by
      rw [Fintype.sum_bool]
      simp only [if_true, Bool.false_eq_true, if_false]
      exact add_tsub_cancel_of_le (by exact_mod_cast min_le_right _ _))

/-- The maximal step length `sup {λ ≥ 0 : y + λ d ∈ [0, 1]^X}`. -/
noncomputable def maxStep (y d : X → ℝ) : ℝ :=
  sSup {t : ℝ | 0 ≤ t ∧ InUnitCube (y + t • d)}

/-- A two-point move: to `up` with probability `q`, to `down` otherwise. -/
structure Move (X : Type) where
  /-- The probability of `up`. -/
  q : ℝ
  /-- The first endpoint. -/
  up : X → ℝ
  /-- The second endpoint. -/
  down : X → ℝ

open Classical in
/-- The rounding step of Algorithm 1 from `y` (lines 3–9 when at least two coordinates are
fractional, line 11 when exactly one is), for the function `f` and the choice rule `ρ`. -/
noncomputable def move (f : Finset X → ℝ) (ρ : (X → ℝ) → X × X) (y : X → ℝ) : Move X :=
  if 2 ≤ (fracSet y).card then
    if partialDeriv (F f) (ρ y).1 y = 0 ∧ partialDeriv (F f) (ρ y).2 y = 0 then
      ⟨y (ρ y).1, Function.update y (ρ y).1 1, Function.update y (ρ y).1 0⟩
    else
      let d : X → ℝ := partialDeriv (F f) (ρ y).2 y • Pi.single (ρ y).1 (1 : ℝ) -
        partialDeriv (F f) (ρ y).1 y • Pi.single (ρ y).2 (1 : ℝ)
      let lp := maxStep y d
      let lm := maxStep y (-d)
      ⟨lm / (lp + lm), y + lp • d, y - lm • d⟩
  else if h : (fracSet y).Nonempty then
    ⟨y (Classical.choose h), Function.update y (Classical.choose h) 1,
      Function.update y (Classical.choose h) 0⟩
  else ⟨1, y, y⟩

/-- At most `k` rounding steps of Algorithm 1 from `y`, with transition reweighting `wt`
(`wt current next` multiplies the probability of moving to `next`). Returns the output set and
whether the run finished (no fractional coordinate left). -/
noncomputable def runAlg1 (f : Finset X → ℝ) (ρ : (X → ℝ) → X × X)
    (wt : (X → ℝ) → (X → ℝ) → ℝ) : ℕ → (X → ℝ) → PMF (Finset X × Bool)
  | 0, y => PMF.pure (roundedSet y, decide ((fracSet y).card = 0))
  | k + 1, y =>
    if (fracSet y).card = 0 then PMF.pure (roundedSet y, true)
    else
      (coin ((move f ρ y).q * wt y (move f ρ y).up)).bind fun b =>
        runAlg1 f ρ wt k (if b then (move f ρ y).up else (move f ρ y).down)

/-- Algorithm 1 on `x` with a budget of `|X|` rounding steps: output set and `finished` flag. -/
noncomputable def alg1Run (f : Finset X → ℝ) (ρ : (X → ℝ) → X × X) (x : X → ℝ) :
    PMF (Finset X × Bool) :=
  runAlg1 f ρ (fun _ _ => 1) (Fintype.card X) x

/-- The law of the output set `S` of Algorithm 1 on `x`. -/
noncomputable def alg1Law (f : Finset X → ℝ) (ρ : (X → ℝ) → X × X) (x : X → ℝ) :
    PMF (Finset X) :=
  (alg1Run f ρ x).map Prod.fst

/-- The reweighting of Algorithm 2, line 7: `w_p / z_p` when conditioning on `p ∈ S`
(`incl = true`), `(1 − w_p)/(1 − z_p)` when conditioning on `p ∉ S`. -/
noncomputable def condWeight (p : X) (incl : Bool) : (X → ℝ) → (X → ℝ) → ℝ :=
  fun z w => if incl then w p / z p else (1 - w p) / (1 - z p)

/-- The law of the output set of Algorithm 1 on `x` run with the transitions conditioned on
`p ∈ S` (`incl = true`) or `p ∉ S` (`incl = false`), budget `|X|` rounding steps. -/
noncomputable def condLaw (f : Finset X → ℝ) (ρ : (X → ℝ) → X × X) (x : X → ℝ) (p : X)
    (incl : Bool) : PMF (Finset X) :=
  (runAlg1 f ρ (condWeight p incl) (Fintype.card X) x).map Prod.fst

/-- The expectation `∑_a P(a) g(a)` of `g` under a law `P` on a finite type. -/
noncomputable def expect {α : Type} [Fintype α] (P : PMF α) (g : α → ℝ) : ℝ :=
  ∑ a, (P a).toReal * g a

open Classical in
/-- The probability of the event `E` under `P`. -/
noncomputable def prob {α : Type} [Fintype α] (P : PMF α) (E : α → Prop) : ℝ :=
  expect P fun a => if E a then 1 else 0

end ForestRoundingNSW.Rounding


