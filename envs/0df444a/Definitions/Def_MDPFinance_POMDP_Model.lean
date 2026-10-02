-- Prove2me | Definitions.Def_MDPFinance_POMDP_Model
-- name    : MDPFinance_POMDP_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:12:28.0138+00:00
-- url     : https://prove2.me/theorems/4af59bdc-6c93-4bd1-a3f1-6ef6569a7c47
-- title:
--   Definition 5.1.1 — a Partially Observable Markov Decision Model
-- statement:
--   Data $(E_X\times E_Y, A, D, Q, Q_0, r, g, \beta)$: state $(x,y)\in E_X\times E_Y$
--   with $x$ observable, $y$ unobservable; action space $A$; feasible pairs $D\subset E_X\times A$
--   with $D(x)$ depending only on $x$; a stochastic kernel $Q$ from $D\times E_Y$ to $E_X\times
--   E_Y$; the initial law $Q_0$ of $Y_0$; one-stage and terminal rewards $r,g$; discount
--   $\beta\in(0,1]$. The marginal $Q^X(B|x,y,a) := Q(B\times E_Y|x,y,a)$ (Eq. (5.1)) is the law of
--   the next observable state alone.
--
--   This is the chapter's basic object: a Markov Decision Process in which the controller sees only
--   part of the state at every stage, and must choose actions using the observable part alone.
--
--   **Formalization Note.** `E_X`,`E_Y`,`A` are taken as abstract measurable spaces (the book's own
--   Borel-subset-of-Polish-space hypothesis is not separately encoded, matching the convention
--   throughout this book's missions of working with a bare `MeasurableSpace` instance).
--
--   **Moderation note.** The structure carries the book's requirements on the data (p. 148-149): $D$ measurable and containing the graph of a measurable $E_X\to A$ (so $D(x)\neq\emptyset$ and decision rules exist), $Q$ a stochastic (Markov) kernel, $r$ and $g$ measurable. Without the graph condition $\Pi_N$ can be empty and $J_N$ a default value; without measurability the expectations are default values.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 148-149, PDF 161-162, Definition 5.1.1 and Equation (5.1)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDP

/-- Definition 5.1.1. A Partially Observable Markov Decision Model consists of data
`(E_X × E_Y, A, D, Q, Q_0, r, g, β)` (Bäuerle–Rieder, p. 148, PDF 161-162): `E_X × E_Y` is the
state space, `x` the observable and `y` the unobservable component; `A` the action space;
`D ⊂ E_X × A` the feasible state-action pairs, `D(x)` depending only on `x`; `Q` a stochastic
kernel from `D × E_Y` to `E_X × E_Y`; `Q_0` the initial distribution of `Y_0`; `r`, `g` the
one-stage and terminal rewards; `β ∈ (0,1]` the discount factor. As in the book, `D` is
measurable and contains the graph of a measurable function `E_X → A`, `Q` is a stochastic
(Markov) kernel, and `r`, `g` are measurable (p. 148-149). -/
structure PartiallyObservableMDM (EX EY A : Type*) [MeasurableSpace EX] [MeasurableSpace EY]
    [MeasurableSpace A] where
  D : Set (EX × A)
  hD_meas : MeasurableSet D
  hD_graph : ∃ f : EX → A, Measurable f ∧ ∀ x, (x, f x) ∈ D
  Q : Kernel ((EX × EY) × A) (EX × EY)
  isMarkovQ : IsMarkovKernel Q
  Q0 : Measure EY
  isProbQ0 : IsProbabilityMeasure Q0
  r : EX × EY × A → ℝ
  hr_meas : Measurable r
  g : EX × EY → ℝ
  hg_meas : Measurable g
  β : ℝ
  hβ0 : 0 < β
  hβ1 : β ≤ 1

variable {EX EY A : Type*} [MeasurableSpace EX] [MeasurableSpace EY] [MeasurableSpace A]

/-- `D(x) := {a ∈ A | (x,a) ∈ D}`, the feasible actions depending only on the observable part
(Bäuerle–Rieder, p. 148, PDF 161). -/
def PartiallyObservableMDM.Dx (M : PartiallyObservableMDM EX EY A) (x : EX) : Set A :=
  {a | (x, a) ∈ M.D}

/-- `Q^X(B|x,y,a) := Q(B × E_Y|x,y,a)`, the marginal transition probability of the observable
part (Bäuerle–Rieder, Eq. (5.1), p. 149, PDF 162). -/
noncomputable def PartiallyObservableMDM.QX (M : PartiallyObservableMDM EX EY A) (x : EX) (y : EY)
    (a : A) (B : Set EX) : ENNReal :=
  M.Q ((x, y), a) (B ×ˢ Set.univ)

end MDPFinance.POMDP


