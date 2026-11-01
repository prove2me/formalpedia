-- Prove2me | Definitions.Def_HardyCausaloid_Model
-- name    : HardyCausaloid_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:16:59.690979+00:00
-- url     : https://prove2.me/theorems/bcdd67a7-912d-4daa-b310-199c5025f621
-- title:
--   Experiment model: labels $\alpha_x\Leftrightarrow(Y_x,F_x)$ and $\mathrm{Prob}(Y_R\mid F_R)$
-- statement:
--   Let $X$ be the set $O_R$ of locations $x$ in a large region $R$. At each location $x$ there is a set of **settings** $F_x$ and, for each setting $f$, a set of possible **outcomes** under $f$. A **label at $x$** is a pair $\alpha_x=(f,y)$ of a setting and an outcome possible under it, i.e. $\alpha_x\Leftrightarrow(Y_x,F_x)$.
--
--   An **experiment model** assigns to every procedure $F$ (a choice of setting $F(x)$ at every location) and every outcome family $Y$ under $F$ a number
--   $$\mathrm{Prob}(Y_R\mid F_R)\ \ge 0,\qquad \sum_{Y}\mathrm{Prob}(Y_R\mid F_R)=1\ \text{ for every }F,$$
--   the probability of seeing $Y$ given the procedure $F$, with the condition $C_{V-R}$ on what happens outside $R$ fixed true and dropped from the notation. For a **total label** $t$ (a label at every location) write $P(t)$ for the probability of its outcomes given its settings.
--
--   This is the data the causaloid framework analyses: every later notion (states, fiducial sets, the causaloid, conditional probabilities) is computed from this array.
--
--   **Formalization Note** Settings and outcomes are arbitrary types and the normalization is an unconditional sum (`HasSum`), so outcome sets may be infinite. Every combination of local settings is a procedure, since $F$ is an arbitrary function of $x$.
-- source:
--   Hardy, Towards Quantum Gravity: A Framework for Probabilistic Theories with Non-Fixed Causal Structure, arXiv:gr-qc/0608043v1, §3, eqs. (2)–(6), pp.8–9; §4.1, eqs. (8)–(9), p.10

import Mathlib

set_option autoImplicit false

namespace HardyCausaloid

universe u v w

/-- **Labels at a location.** Hardy, *Towards Quantum Gravity: A Framework for Probabilistic
Theories with Non-Fixed Causal Structure*, arXiv:gr-qc/0608043v1, §3, eqs. (2)–(6), pp.8–9
("We will label each possible (Y1, F1) in R1 with α1 = 1, 2, . . .").

A label at the location `x` is a pair `⟨f, y⟩` of a setting `f : Setting x` (the procedure
`F_x` at `x`) and an outcome `y : Outcome x f` possible under that setting (the outcome set
`Y_x`); this is `α_x ⇔ (Y_x, F_x)`.

**Formalization Note** Labels are dependent pairs (`Sigma`), because the possible outcomes depend
on the setting chosen. No finiteness is assumed of settings, outcomes or locations. -/
abbrev Label {X : Type u} (Setting : X → Type v) (Outcome : (x : X) → Setting x → Type w)
    (x : X) : Type (max v w) :=
  Σ f : Setting x, Outcome x f

/-- **An experiment model**, Hardy, arXiv:gr-qc/0608043v1, §3 (pp.6–9) and §4.1, eqs. (8)–(9),
p.10 ("We will assume that the probabilities Prob(YR|FR, CV −R) are well defined for all YR and
FR").

`X` is the set `O_R` of locations `x` in the large region `R`; `Setting x` is the set of
settings at `x` and `Outcome x f` the set of outcomes possible at `x` under the setting `f`. A
model gives, for every procedure `F` (a choice of setting `F x` at every location) and every
outcome family `Y` under `F` (an outcome `Y x : Outcome x (F x)` at every location), the
probability `prob F Y = Prob(Y_R | F_R)`, with the condition `C_{V−R}` fixed true and dropped
from the notation as on p.10. For every `F`, `prob F` is a probability distribution on outcome
families: nonnegative, with (unconditional) sum `1`.

**Formalization Note** The normalization is `HasSum (prob F) 1`, an unconditional sum, so that
outcome sets may be infinite (the paper labels them `α₁ = 1, 2, …` and does not say finite).
Every combination of local settings is a procedure, since `F` is an arbitrary function of `x`
(p.7). -/
structure Model {X : Type u} (Setting : X → Type v) (Outcome : (x : X) → Setting x → Type w) where
  /-- `prob F Y = Prob(Y_R | F_R)`. -/
  prob : (F : ∀ x, Setting x) → (∀ x, Outcome x (F x)) → ℝ
  /-- Probabilities are nonnegative. -/
  prob_nonneg : ∀ F Y, 0 ≤ prob F Y
  /-- For every procedure the probabilities of the outcome families sum to one. -/
  hasSum_prob : ∀ F, HasSum (prob F) 1

variable {X : Type u} {Setting : X → Type v} {Outcome : (x : X) → Setting x → Type w}

/-- **The probability of a total label**, Hardy, arXiv:gr-qc/0608043v1, §4.1, p.10: for a
total label `t` (a label `t x = ⟨F x, Y x⟩` at every location `x`), `M.P t = Prob(Y | F)` with
`F x = (t x).1` and `Y x = (t x).2`. -/
def Model.P (M : Model Setting Outcome) (t : ∀ x, Label Setting Outcome x) : ℝ :=
  M.prob (fun x => (t x).1) (fun x => (t x).2)

end HardyCausaloid


