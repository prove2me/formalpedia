-- Prove2me | Definitions.Def_MDPFinance_POMDP_Objective
-- name    : MDPFinance_POMDP_Objective
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:13:55.139125+00:00
-- url     : https://prove2.me/theorems/0b3aa320-fa4e-41c8-bfb7-c9380e4782b1
-- title:
--   Definition 5.1.3 (Equation 5.2) — the POMDP objective $J_N$
-- statement:
--   $$J_N^\pi(x) := \int \mathbb{E}_{xy}^\pi\Big[\sum_{n=0}^{N-1}\beta^n
--   r(X_n,Y_n,A_n) + \beta^N g(X_N,Y_N)\Big]\,Q_0(dy), \qquad J_N(x) := \sup_{\pi\in\Pi_N}
--   J_N^\pi(x).$$
--   The expectation $\mathbb{E}_{xy}^\pi$ (`Ex`/`Vpi`) is realized as a recursive integral against
--   the kernel $Q$ — at each step, integrate the continuation value against $Q(\cdot\mid x_n,y_n,
--   a_n)$, where $a_n=\pi_n(x_0,\dots,x_n)$ — rather than via an explicit sample space, since $Q$
--   is an abstract stochastic kernel with no assumed generative (i.i.d.-noise) form, unlike the
--   concrete financial markets of chunks `04a`-`04d`.
--
--   Unlike Chapter 2's objective, this one carries an extra outer integral over $Q_0$ (the unknown
--   initial hidden state), and admissible $\pi$ must not depend on any $Y_n$ — exactly why Chapter
--   2's theory does not apply directly to $J_N$, and why the chapter goes on to build the filtered
--   reformulation.
--
--   **Formalization Note.** `Vpi`/`Ex`'s recursive-integral construction is mathematically an
--   iterated `Measure.bind`/kernel-composition, chosen over building an explicit measure on a
--   trajectory sample space because it states the value directly as a computable real-valued
--   recursion, exactly mirroring how `04a`-`04d`'s `Vpi`/`stateAcc` functions were built for
--   concrete (non-kernel) models.
--
--   **Moderation note.** The values $V^\pi$, $J_N^\pi$, $J_N$ are taken in $[-\infty,\infty]$ through `erealIntegral` (Lebesgue integrals of positive and negative parts), and the section's standing **Integrability Assumption** (p. 151), $\sup_\pi\int\mathbb{E}^\pi_{xy}[\sum_n\beta^n r^+(X_n,Y_n,A_n)+\beta^N g^+(X_N,Y_N)]\,Q_0(dy)<\infty$ for all $x$, is stated as `IntegrabilityAssumption` via the same recursion for the positive parts (`VposPi`). With real Bochner integrals a stage whose expectation is $-\infty$ would have been recorded as $0$, and the two sides of Theorem 5.3.2 could then differ.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 150, PDF 163, Definition 5.1.3, Equation (5.2)

import Mathlib
import Definitions.Def_MDPFinance_POMDP_Model
import Definitions.Def_MDPFinance_POMDP_Policy

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.POMDP

variable {EX EY A : Type*} [MeasurableSpace EX] [MeasurableSpace EY] [MeasurableSpace A]
  [Nonempty A]

/-- The expectation, under policy `π`, of a test function `F` of the whole (padded) observable
history and the current unobservable state, `k` steps after reaching `(xs,as,y)` at absolute
time `n`: `𝔼[F(X_0,A_0,…,X_{n+k},Y_{n+k})]` given `(X_0,A_0,…,X_n) = (xs,as)` restricted to their
first `n+1`/`n` coordinates and `Y_n = y` (Bäuerle–Rieder's `𝔼^π_{xy}`, restated as a recursive
integral against the kernel `Q` rather than via an explicit sample space, since `Q` is an
abstract stochastic kernel with no assumed generative/i.i.d.-noise form). -/
noncomputable def PartiallyObservableMDM.Ex (M : PartiallyObservableMDM EX EY A) (π : Policy EX A) :
    (k : ℕ) → (n : ℕ) → (xs : ℕ → EX) → (as : ℕ → A) → (y : EY) →
      ((ℕ → EX) → (ℕ → A) → EY → ℝ) → ℝ
  | 0, _n, xs, as, y, F => F xs as y
  | (k + 1), n, xs, as, y, F =>
      let a := π n xs as
      ∫ p : EX × EY, M.Ex π k (n + 1) (Function.update xs (n + 1) p.1) (Function.update as n a)
        p.2 F ∂(M.Q ((xs n, y), a))

/-- The integral `∫ v dμ` of an `EReal`-valued function, valued in `[-∞,∞]` (restated from
`MDPFinance.Bellman.erealIntegral`, chunk `02a`): the Lebesgue integrals of the positive and
negative parts are combined with `EReal`'s total addition (`⊤ + (-⊤) = ⊥`), so an expected
reward that is `-∞` is recorded as `-∞`, never as a default real value. -/
noncomputable def erealIntegral {E : Type*} [MeasurableSpace E] (μ : Measure E) (v : E → EReal) :
    EReal :=
  (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal) + (-(↑(∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ) : EReal))

/-- The value `V^π_{k,n}(xs,as,y) := 𝔼[Σ_{j=n}^{n+k-1} β^{j-n} r(X_j,Y_j,A_j) + β^k g(X_{n+k},
Y_{n+k})] ∈ [-∞,∞]` of policy `π` over the next `k` stages, from history `(xs,as)`, current
unobservable state `y`, at absolute time `n`; the stage expectations are `erealIntegral`s, so
that under the section's Integrability Assumption (finite expected positive parts) the value is
the book's expectation in `[-∞,∞)`. -/
noncomputable def PartiallyObservableMDM.Vpi (M : PartiallyObservableMDM EX EY A)
    (π : Policy EX A) : (k : ℕ) → (n : ℕ) → (xs : ℕ → EX) → (as : ℕ → A) → (y : EY) → EReal
  | 0, n, xs, _, y => (M.g (xs n, y) : EReal)
  | (k + 1), n, xs, as, y =>
      let a := π n xs as
      (M.r (xs n, y, a) : EReal) + (M.β : EReal) *
        erealIntegral (M.Q ((xs n, y), a)) (fun p : EX × EY =>
          M.Vpi π k (n + 1) (Function.update xs (n + 1) p.1) (Function.update as n a) p.2)

/-- `𝔼^π_{xy}[Σ_{j=n}^{n+k-1} β^{j-n} r⁺(X_j,Y_j,A_j) + β^k g⁺(X_{n+k},Y_{n+k})] ∈ [0,∞]`, the same
recursion for the positive parts `r⁺`, `g⁺` (Lebesgue integrals). -/
noncomputable def PartiallyObservableMDM.VposPi (M : PartiallyObservableMDM EX EY A)
    (π : Policy EX A) : (k : ℕ) → (n : ℕ) → (xs : ℕ → EX) → (as : ℕ → A) → (y : EY) → ℝ≥0∞
  | 0, n, xs, _, y => ENNReal.ofReal (M.g (xs n, y))
  | (k + 1), n, xs, as, y =>
      let a := π n xs as
      ENNReal.ofReal (M.r (xs n, y, a)) + ENNReal.ofReal M.β *
        ∫⁻ p : EX × EY, M.VposPi π k (n + 1) (Function.update xs (n + 1) p.1)
          (Function.update as n a) p.2 ∂(M.Q ((xs n, y), a))

/-- `J_N^π(x) := ∫ 𝔼^π_{xy}[Σ_{n=0}^{N-1} β^n r(X_n,Y_n,A_n) + β^N g(X_N,Y_N)] Q_0(dy) ∈ [-∞,∞]`
(Bäuerle–Rieder, Eq. (5.2), p. 150, PDF 163). -/
noncomputable def PartiallyObservableMDM.JNpi (M : PartiallyObservableMDM EX EY A)
    (π : Policy EX A) (N : ℕ) (x : EX) : EReal :=
  erealIntegral M.Q0 (fun y0 : EY => M.Vpi π N 0 (fun _ => x) (fun _ => Classical.arbitrary A) y0)

/-- `J_N(x) := sup_{π ∈ Π_N} J_N^π(x)` (Bäuerle–Rieder, Eq. (5.2), p. 150, PDF 163). -/
noncomputable def PartiallyObservableMDM.JN (M : PartiallyObservableMDM EX EY A) (N : ℕ) (x : EX) :
    EReal :=
  ⨆ π ∈ {π : Policy EX A | M.IsPolicy N π}, M.JNpi π N x

/-- The Integrability Assumption of Section 5.1 (Bäuerle–Rieder, p. 151, PDF 164), assumed
throughout the chapter: for all `x ∈ E_X`,
`sup_π ∫ 𝔼^π_{xy}[Σ_{n=0}^{N-1} β^n r⁺(X_n,Y_n,A_n) + β^N g⁺(X_N,Y_N)] Q_0(dy) < ∞`. -/
def PartiallyObservableMDM.IntegrabilityAssumption (M : PartiallyObservableMDM EX EY A)
    (N : ℕ) : Prop :=
  ∀ x : EX, (⨆ π ∈ {π : Policy EX A | M.IsPolicy N π},
    ∫⁻ y0 : EY, M.VposPi π N 0 (fun _ => x) (fun _ => Classical.arbitrary A) y0 ∂M.Q0) < ⊤

end MDPFinance.POMDP


