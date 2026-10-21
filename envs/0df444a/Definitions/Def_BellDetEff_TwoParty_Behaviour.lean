-- Prove2me | Definitions.Def_BellDetEff_TwoParty_Behaviour
-- name    : BellDetEff_TwoParty_Behaviour
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:19:17.669984+00:00
-- url     : https://prove2.me/theorems/e8c75f82-15e0-475f-be6f-68c2720945a9
-- title:
--   Two-party behaviours, the no-signaling condition (1), marginals, LHV models (3) and deterministic strategies (7) (pp. 1–2)
-- statement:
--   This file sets up the general objects of a two-party Bell test, following Section II of Cao and Peng.
--
--   Two separated parties A and B receive inputs $x\in\{1,\dots,M_A\}$ and $y\in\{1,\dots,M_B\}$ and produce outputs $a\in O_A$, $b\in O_B$ from finite alphabets.
--
--   1. **Behaviour.** A behaviour is a family $p(a,b\mid x,y)$ of real numbers that, for every pair of inputs $(x,y)$, is a probability distribution on $O_A\times O_B$: $p(a,b\mid x,y)\ge 0$ and $\sum_{a,b}p(a,b\mid x,y)=1$.
--   2. **No-signaling (eq. (1)).** A behaviour is no-signaling if A's marginal $p(a\mid x,y)=\sum_b p(a,b\mid x,y)$ does not depend on $y$ and B's marginal $p(b\mid x,y)=\sum_a p(a,b\mid x,y)$ does not depend on $x$.
--   3. **Marginals.** The one-party marginals used in Bell expressions are
--   $$p(a\mid x):=\frac1{M_B}\sum_{y}\sum_b p(a,b\mid x,y),\qquad p(b\mid y):=\frac1{M_A}\sum_{x}\sum_a p(a,b\mid x,y).$$
--   For a no-signaling behaviour these coincide with $\sum_b p(a,b\mid x,y)$ (resp. $\sum_a p(a,b\mid x,y)$) for every value of the other party's input.
--   4. **Local hidden variable model (eq. (3)).** An LHV model consists of a probability space $(\Lambda,\mu)$ of hidden variables and response probabilities $p_A(a\mid x,\lambda)$, $p_B(b\mid y,\lambda)$ that are nonnegative, sum to one over the outputs, and are measurable in $\lambda$. It produces the behaviour
--   $$p(a,b\mid x,y)=\int_\Lambda p_A(a\mid x,\lambda)\,p_B(b\mid y,\lambda)\,d\mu(\lambda).$$
--   A behaviour can be *simulated by an LHV model* if some LHV model produces exactly it.
--   5. **Deterministic strategies (eq. (7)).** For functions $F$ from A's inputs to A's outputs and $G$ from B's inputs to B's outputs, the deterministic behaviour is $p(a,b\mid x,y)=1$ if $F(x)=a$ and $G(y)=b$, and $0$ otherwise.
--
--   These are the objects in terms of which the detector-efficiency threshold and the Bell inequality of the paper are defined.
--
--   **Formalization Note** Inputs are `Fin MA`, `Fin MB`; the paper's input $x$ is `x.val + 1`. Output alphabets are arbitrary finite types. The hidden-variable space $\Lambda$ is an arbitrary `Type` with a measurable-space structure and a probability measure; it is not restricted to finite or deterministic models. Since the response probabilities are measurable and bounded by one, every integral in the LHV behaviour is of an integrable function. If $M_B=0$ (resp. $M_A=0$), the averaging factor $1/M_B$ is Lean's $1/0=0$, but then the sum is empty anyway.
-- source:
--   Cao & Peng, Tight detection efficiency bounds of Bell tests in no-signaling theories, arXiv:1607.04350v1, pp. 1–2, Section II, eqs. (1) and (3); p. 2, eq. (7)

import Mathlib

namespace BellDetEff.TwoParty

open MeasureTheory

/-- A two-party behaviour (Cao–Peng, Section II, p. 1): `p a b x y` is the probability that
A outputs `a` and B outputs `b` on inputs `x : Fin MA`, `y : Fin MB` (the paper's inputs
`x ∈ [1, MA]` are `x.val + 1`). It is a probability distribution over the outputs for every
pair of inputs. -/
def IsBehaviour {OA OB : Type} [Fintype OA] [Fintype OB] {MA MB : ℕ}
    (p : OA → OB → Fin MA → Fin MB → ℝ) : Prop :=
  (∀ a b x y, 0 ≤ p a b x y) ∧ ∀ x y, ∑ a, ∑ b, p a b x y = 1

/-- The no-signaling condition, eq. (1), p. 2: A's marginal `p(a|x, y) = ∑_b p(a, b|x, y)` does
not depend on `y`, and B's marginal `p(b|x, y) = ∑_a p(a, b|x, y)` does not depend on `x`. -/
def NoSignaling {OA OB : Type} [Fintype OA] [Fintype OB] {MA MB : ℕ}
    (p : OA → OB → Fin MA → Fin MB → ℝ) : Prop :=
  (∀ a x y y', ∑ b, p a b x y = ∑ b, p a b x y') ∧
    (∀ b x x' y, ∑ a, p a b x y = ∑ a, p a b x' y)

/-- A's marginal `p(a|x)`, taken as the average over B's inputs of `∑_b p(a, b|x, y)`. For a
no-signaling behaviour it equals `∑_b p(a, b|x, y)` for every `y`. -/
noncomputable def marginalA {OA OB : Type} [Fintype OA] [Fintype OB] {MA MB : ℕ}
    (p : OA → OB → Fin MA → Fin MB → ℝ) (a : OA) (x : Fin MA) : ℝ :=
  (1 / (MB : ℝ)) * ∑ y, ∑ b, p a b x y

/-- B's marginal `p(b|y)`, the average over A's inputs of `∑_a p(a, b|x, y)`. -/
noncomputable def marginalB {OA OB : Type} [Fintype OA] [Fintype OB] {MA MB : ℕ}
    (p : OA → OB → Fin MA → Fin MB → ℝ) (b : OB) (y : Fin MB) : ℝ :=
  (1 / (MA : ℝ)) * ∑ x, ∑ a, p a b x y

/-- A local hidden variable model, eq. (3), p. 2: a probability space `(Λ, μ)` of hidden
variables (an arbitrary measurable space) and local response probabilities
`pA x λ a = p_A(a|x, λ)`, `pB y λ b = p_B(b|y, λ)`, measurable in `λ`. -/
structure LHVModel (OA OB : Type) [Fintype OA] [Fintype OB] (MA MB : ℕ) where
  /-- The hidden-variable space. -/
  Λ : Type
  [mΛ : MeasurableSpace Λ]
  /-- The distribution of the hidden variable. -/
  μ : Measure Λ
  [isProb : IsProbabilityMeasure μ]
  /-- A's response probabilities `p_A(a|x, λ)`. -/
  pA : Fin MA → Λ → OA → ℝ
  /-- B's response probabilities `p_B(b|y, λ)`. -/
  pB : Fin MB → Λ → OB → ℝ
  measurable_pA : ∀ x a, Measurable fun l => pA x l a
  measurable_pB : ∀ y b, Measurable fun l => pB y l b
  pA_nonneg : ∀ x l a, 0 ≤ pA x l a
  pA_sum : ∀ x l, ∑ a, pA x l a = 1
  pB_nonneg : ∀ y l b, 0 ≤ pB y l b
  pB_sum : ∀ y l, ∑ b, pB y l b = 1

attribute [instance] LHVModel.mΛ LHVModel.isProb

/-- The behaviour produced by an LHV model: `∫ p_A(a|x, λ) p_B(b|y, λ) dμ(λ)` (eq. (3)). -/
noncomputable def LHVModel.behaviour {OA OB : Type} [Fintype OA] [Fintype OB] {MA MB : ℕ}
    (M : LHVModel OA OB MA MB) (a : OA) (b : OB) (x : Fin MA) (y : Fin MB) : ℝ :=
  ∫ l, M.pA x l a * M.pB y l b ∂M.μ

/-- A behaviour `p` can be simulated by an LHV model (eq. (3)) if some LHV model reproduces
every entry of `p`. -/
def LHVSimulable {OA OB : Type} [Fintype OA] [Fintype OB] {MA MB : ℕ}
    (p : OA → OB → Fin MA → Fin MB → ℝ) : Prop :=
  ∃ M : LHVModel OA OB MA MB, ∀ a b x y, p a b x y = M.behaviour a b x y

/-- The deterministic local behaviour of eq. (7), p. 2: A outputs `F x` and B outputs `G y`,
i.e. `p(a, b|x, y) = 1` if `F x = a` and `G y = b`, and `0` otherwise. -/
def deterministic {OA OB : Type} [DecidableEq OA] [DecidableEq OB] {MA MB : ℕ}
    (F : Fin MA → OA) (G : Fin MB → OB) (a : OA) (b : OB) (x : Fin MA) (y : Fin MB) : ℝ :=
  if F x = a ∧ G y = b then 1 else 0

end BellDetEff.TwoParty


