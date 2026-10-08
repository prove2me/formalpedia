-- Prove2me | Definitions.Def_McFadden1974_IIA_ChoiceModel
-- name    : McFadden1974_IIA_ChoiceModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:46:39.585395+00:00
-- url     : https://prove2.me/theorems/9552dab4-8bf8-483c-bd22-3dbd8dc95ab4
-- title:
--   §I, pp. 107–110 — selection probabilities, Axioms 1–2, binary probabilities $p_{xy}$, $V(s,x,z)$, universal benchmark
-- statement:
--   This definition bundle sets up the model of qualitative choice of McFadden (1974), §I.
--
--   Let $X$ be the universe of objects of choice and $S$ the universe of vectors of measured attributes of decision-makers. An **alternative set** is a finite set $B \subseteq X$, and a family $\mathcal B$ of finite sets is designated as the **possible alternative sets**. The **selection probability** $P(x \mid s, B)$ is the probability that an individual drawn at random from the population, with measured attributes $s \in S$ and facing the alternative set $B$, chooses $x \in B$. The bundle defines:
--
--   1. **Selection probabilities.** For every $s$ and every possible $B$, $x \mapsto P(x\mid s,B)$ is a probability vector on $B$: $P(x\mid s,B)\ge 0$ for $x\in B$ and $\sum_{x\in B}P(x\mid s,B)=1$ (the observed choice is a drawing from a multinomial distribution).
--   2. **Binary choices are possible.** Whenever $B$ is possible and $x \neq y$ are members of $B$, the pair $\{x,y\}$ is a possible alternative set.
--   3. **Axiom 1 (Independence of Irrelevant Alternatives).** For all possible $B$, all $s$, and all $x, y \in B$,
--   $$P(x\mid s,\{x,y\})\,P(y\mid s,B) = P(y\mid s,\{x,y\})\,P(x\mid s,B).$$
--   4. **Axiom 2 (Positivity).** $P(x\mid s,B) > 0$ for all possible $B$, all $s$, and all $x\in B$.
--   5. **Binary probabilities.** $p_{xy} = P(x\mid s,\{x,y\})$ for $x\neq y$, and $p_{xx} = \tfrac12$.
--   6. **The function $V$.** $V(s,x,z) = \log(p_{xz}/p_{zx})$.
--   7. **Universal benchmark.** An alternative $z$ such that $B\cup\{z\}$ is possible whenever $B$ is.
--
--   These objects carry the derivation of the conditional logit form of selection probabilities from Luce's choice axiom.
--
--   **Formalization Note** Selection probabilities are a function $P : S \to \mathrm{Finset}\,X \to X \to \mathbb R$; only values with $x\in B$ carry meaning. The pair condition (item 2) is an assumption the paper uses without stating it; it is not required for singletons. $p_{xx}=\tfrac12$ is the paper's definition, not $P(x\mid s,\{x\})$. $V$ uses `Real.log`, which is $0$ on non-positive arguments; under Axiom 2 its argument is positive wherever it is used.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 107 (model), p. 109 (Axioms 1–2, Equation (4), p_xy), p. 110 (Equation (10), footnote 3); PDF pp. 3, 5–6

import Mathlib

namespace McFadden1974.IIA

/-! # The selection-probability model of §I and Axioms 1–2 (definition bundle)

McFadden, *Conditional Logit Analysis of Qualitative Choice Behavior*, in P. Zarembka (ed.),
*Frontiers in Econometrics*, Academic Press (1974), §I, pp. 107, 109–110 (PDF pp. 3, 5–6).

Throughout, `X` is the universe of objects of choice, `S` the universe of vectors of measured
attributes, an alternative set is a `B : Finset X`, the family of possible alternative sets is
`poss : Set (Finset X)`, and the selection probabilities are `P : S → Finset X → X → ℝ`, with
`P s B x` standing for the paper's `P(x | s, B)`. Only the values `P s B x` with `x ∈ B` carry
meaning; no statement of this mission depends on the others. -/

variable {X S : Type*} [DecidableEq X]

/-- **Standing assumption of §I** (p. 107, PDF p. 3): "The observed choice in a trial with
attributes s and alternatives B can then be viewed as a drawing from a multinomial distribution
with selection probabilities P(x | s, B) for x ∈ B." For every attribute vector `s` and every
possible alternative set `B`, `x ↦ P(x | s, B)` is a probability vector on `B`.

Formalization Note: unnumbered in the paper (model description, p. 107). The sum is over `B`
only; values of `P s B x` for `x ∉ B` are unconstrained and irrelevant. Since the sum is `1`,
every possible set is nonempty. -/
def IsSelectionProb (P : S → Finset X → X → ℝ) (poss : Set (Finset X)) : Prop :=
  ∀ s : S, ∀ B ∈ poss, (∀ x ∈ B, 0 ≤ P s B x) ∧ ∑ x ∈ B, P s B x = 1

/-- **Binary choices are possible.** Axiom 1 (p. 109, PDF p. 5) and Equations (5)–(10) use the
binary selection probabilities `P(x | s, {x, y})` for every two members `x ≠ y` of a possible
set `B`, so the paper treats `{x, y}` as a possible alternative set without saying so. This
predicate makes that implicit assumption explicit: every two-element subset of a possible set is
possible.

Formalization Note: unnumbered; an implicit convention of §I (pp. 109–110). It is stated for
`x ≠ y` only, so singletons are not required to be possible. -/
def PairsPossible (poss : Set (Finset X)) : Prop :=
  ∀ B ∈ poss, ∀ x ∈ B, ∀ y ∈ B, x ≠ y → ({x, y} : Finset X) ∈ poss

/-- **Axiom 1 (Independence of Irrelevant Alternatives)** (p. 109, PDF p. 5): "For all possible
alternative sets B, measured attributes s, and members x and y of B,
(4) P(x | s, {x, y}) P(y | s, B) = P(y | s, {x, y}) P(x | s, B)." -/
def Axiom1 (P : S → Finset X → X → ℝ) (poss : Set (Finset X)) : Prop :=
  ∀ s : S, ∀ B ∈ poss, ∀ x ∈ B, ∀ y ∈ B,
    P s {x, y} x * P s B y = P s {x, y} y * P s B x

/-- **Axiom 2 (Positivity)** (p. 109, PDF p. 5): "P(x | s, B) > 0 for all possible alternative
sets B, vectors of measured attributes s, and x ∈ B." -/
def Axiom2 (P : S → Finset X → X → ℝ) (poss : Set (Finset X)) : Prop :=
  ∀ s : S, ∀ B ∈ poss, ∀ x ∈ B, 0 < P s B x

/-- **Binary selection probabilities** `p_xy` (p. 109, PDF p. 5): "let p_xy = P(x | s, {x, y}).
Define p_xx = ½."

Formalization Note: the attribute vector `s` is an explicit argument (`binProb P s x y` is the
paper's `p_xy` at `s`). The diagonal value `½` is the paper's definition, not `P(x | s, {x})`
(which is `1` for a probability vector, since `{x, x} = {x}`); with it `p_xx / p_xx = 1`. -/
noncomputable def binProb (P : S → Finset X → X → ℝ) (s : S) (x y : X) : ℝ :=
  if x = y then 1 / 2 else P s {x, y} x

/-- **The function `V(s, x, z)` of Equation (10)** (p. 110, PDF p. 6): "Taking z to be a
'benchmark' member of the alternative set B and defining V(s, x, z) = log(p_xz/p_zx)".

Formalization Note: `Real.log` is `0` on non-positive arguments; under Axiom 2 on the binary sets
both `p_xz` and `p_zx` are positive, so the argument is positive wherever the mission uses `V`.
`V s z z = log 1 = 0`. -/
noncomputable def altSetV (P : S → Finset X → X → ℝ) (s : S) (x z : X) : ℝ :=
  Real.log (binProb P s x z / binProb P s z x)

/-- **Universal benchmark** (footnote 3, p. 110, PDF p. 6): "some 'universal benchmark'
alternative z such that if B is a possible alternative set, then B ∪ {z} is also." -/
def IsUniversalBenchmark (poss : Set (Finset X)) (z : X) : Prop :=
  ∀ B ∈ poss, insert z B ∈ poss

end McFadden1974.IIA


