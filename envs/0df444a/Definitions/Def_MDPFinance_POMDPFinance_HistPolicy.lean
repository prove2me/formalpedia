-- Prove2me | Definitions.Def_MDPFinance_POMDPFinance_HistPolicy
-- name    : MDPFinance_POMDPFinance_HistPolicy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:33:14.023996+00:00
-- url     : https://prove2.me/theorems/0b4e126f-9056-491e-a561-d5d92b72478c
-- title:
--   History-dependent portfolio strategies and their value function under partial observation
-- statement:
--   A **history-dependent portfolio strategy** on the observable filtration $\mathcal F_n =
--   \sigma(R_1,\dots,R_n)$ is, formally, a sequence $\pi = (f_0,\dots,f_{N-1})$ of maps from the
--   history of observed returns to an action in $\mathbb R^d$. Because the filtration is generated
--   by the returns alone (Bäuerle and Rieder, p. 177/184), a strategy can be represented directly as
--   a function of the stage $n$ and the return path $z_1,\dots,z_n$, without separately tracking
--   wealth or past actions, both of which are themselves deterministic functions of the return path
--   once the strategy is fixed.
--
--   Given a strategy $\pi$, an initial wealth $x_0$ and a sequence of one-period rates $(i_n)$, the
--   **wealth process** it generates obeys the usual recursion $x_{n+1} = (1+i_{n+1})(x_n + f_n\cdot
--   z_{n+1})$, and $\pi$ is **feasible** on $[0,N)$ for a feasible-action correspondence $D$ if every
--   $f_n$ is a measurable function of the return history and is feasible at the wealth it is
--   actually used at.
--
--   The **value-to-go** of a strategy $\pi$ over $k$ further stages, from absolute time $n$,
--   observable wealth $x$ and belief $\rho$, with terminal payoff function $\mathrm{term}$ (the
--   utility $U$ for the terminal-wealth problem, a quadratic loss $(x-b)^2$ for the auxiliary
--   mean-variance problem, or the raw moments $x,x^2$), is defined by the backward recursion
--   $$
--   V_0 = \mathrm{term}(x), \qquad
--   V_{k+1}(n,z_{[1,n]},x,\rho) = \int V_k\big(n+1,z_{[1,n+1]},(1+i_{n+1})(x+f_n\cdot z),\Phi(\rho,z)
--   \big)\,d(\text{predictive}(\rho))(z),
--   $$
--   using the extended-real integral throughout so that the supremum/infimum value functions below
--   are always well-defined (possibly $\pm\infty$). The **value function** of a maximization problem
--   (the terminal-wealth problem, Theorem 6.1.1) is the supremum of the value-to-go over feasible
--   strategies; the value function of a minimization problem ($QP(b)$, Theorem 6.2.2) is the
--   corresponding infimum. Finally, a **Markov strategy** built from a sequence of decision rules
--   $f_n : \mathbb R \times \mathbb P(E_Y) \to \mathbb R^d$ is the history-dependent strategy that
--   reads off the current wealth and current filter belief from the return history and applies
--   $f_n$, exactly the shape of every optimal strategy this chapter exhibits.
--
--   **Formalization Note.** This one scaffold, parametrized by the terminal payoff, the rate
--   sequence and the feasible-action correspondence, serves every value function of this chapter
--   (Theorem 6.1.1's utility-maximization value, Theorem 6.1.2/6.1.7's power/log specializations,
--   Theorem 6.2.2's $QP(b)$, and Theorem 6.2.3's mean-variance moments), rather than one bespoke
--   construction per section.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 177-178/184, Def. 5.1.3 specialized + Eq. (5.2)/(6.2)/model data preceding Theorem 6.2.2

import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDPFinance

variable {EY : Type*} [MeasurableSpace EY] {d : ℕ}

/-- A **history-dependent portfolio strategy** (Bäuerle–Rieder, `Π_N`, p. 184: `π = (f_0,\dots,
f_{N-1})` with `f_n : H_n → A` depending on the observable history until time `n`), represented
here directly as a function of the stage `n` and the *return* history `zs` alone, since `F_n =
σ(R_1,\dots,R_n)` (p. 177/184): wealth and past actions carry no information beyond what the
returns already determine (`FilterOp.mu`'s own restriction to `zs`, above). `zs 0` and `zs k` for
`k > n` are unused junk, as elsewhere in this series. -/
def HistPolicy (d : ℕ) := ℕ → (ℕ → (Fin d → ℝ)) → (Fin d → ℝ)

/-- The wealth process `x_n` reached from `x_0` under portfolio strategy `π` and observed return
path `zs`, via the transition `T_{n,X}(x,a,z) := (1+i_{n+1})(x+a\cdot z)` (Bäuerle–Rieder, p. 177
(stationary `i`) / p. 184 (`i_n`, non-stationary); both instances of this one recursion). -/
def xOf (i : ℕ → ℝ) (x0 : ℝ) (π : HistPolicy d) : (n : ℕ) → (ℕ → (Fin d → ℝ)) → ℝ
  | 0, _ => x0
  | (n + 1), zs => (1 + i (n + 1)) * (xOf i x0 π n zs + ∑ j, π n zs j * zs (n + 1) j)

/-- `π` is feasible over `[0,N)` for the (possibly `x`-dependent) feasible set `D`: every decision
rule is measurable (in the return history) and feasible at the wealth it is actually used at
(Bäuerle–Rieder, Definition 5.1.3 specialized; `D ≡ fun _ => Set.univ` for §6.2's unconstrained
`D_n(x) := A`, p. 184). -/
def IsFeasiblePolicy (D : ℝ → Set (Fin d → ℝ)) (i : ℕ → ℝ) (x0 : ℝ) (N : ℕ) (π : HistPolicy d) :
    Prop :=
  ∀ n < N, Measurable (π n) ∧ ∀ zs, π n zs ∈ D (xOf i x0 π n zs)

/-- The integral `∫ v \, dμ ∈ [-∞,∞)` of an extended-real-valued function, restated from
`MDPFinance.Bellman.erealIntegral` (chunk `02a`) for this chunk's own return space `Fin d → ℝ`. -/
noncomputable def erealIntegral (μ : Measure (Fin d → ℝ)) (v : (Fin d → ℝ) → EReal) : EReal :=
  (↑(∫⁻ z, (v z ⊔ 0).toENNReal ∂μ) : EReal) + (-(↑(∫⁻ z, ((-v z) ⊔ 0).toENNReal ∂μ) : EReal))

/-- The value-to-go `V_{k,n}^π(zs,x,ρ)` of strategy `π` over the next `k` stages from absolute
time `n`, observable wealth `x`, belief `ρ`, and return history `zs` so far, with terminal payoff
`term` (`term := U` for §6.1's terminal-wealth problem, `term := fun x => (x-b)^2` for §6.2's
`QP(b)`, `term := id`/`fun x => x^2` for the raw moments of `X_N`); every stage reward is `0` and
`β = 1` throughout this chapter (Bäuerle–Rieder, p. 178/184 model data `r ≡ 0`, `β = 1`). -/
noncomputable def Vpi (M : FilterMarket EY d) (Fd : FilterOp M) (i : ℕ → ℝ) (term : ℝ → ℝ)
    (π : HistPolicy d) : (k : ℕ) → (n : ℕ) → (ℕ → (Fin d → ℝ)) → ℝ → Measure EY → EReal
  | 0, _, _, x, _ => (term x : EReal)
  | (k + 1), n, zs, x, ρ =>
      let a := π n zs
      erealIntegral (M.predictive ρ) fun z =>
        Vpi M Fd i term π k (n + 1) (Function.update zs (n + 1) z)
          ((1 + i (n + 1)) * (x + ∑ j, a j * z j)) (Fd.Phi ρ z)

/-- `J_N(x,ρ) := \sup_{π \text{ feasible}} V_{N,0}^π(x,ρ)`, the value function (general belief `ρ`,
not only the prior `Q_0`) of the maximization problem (e.g. (6.2), Theorem 6.1.1) over
history-dependent strategies; `Jsup ... N x0 M.Q0` recovers the value of the original problem
(Theorem 6.1.1's part c), folded into this one scaffold — see `theorem_6_1_1`'s docstring). -/
noncomputable def Jsup (M : FilterMarket EY d) (Fd : FilterOp M) (i : ℕ → ℝ) (term : ℝ → ℝ)
    (D : ℝ → Set (Fin d → ℝ)) (N : ℕ) (x0 : ℝ) (ρ0 : Measure EY) : EReal :=
  ⨆ π ∈ {π : HistPolicy d | IsFeasiblePolicy D i x0 N π}, Vpi M Fd i term π N 0 (fun _ => 0) x0 ρ0

/-- `J_N(x,ρ) := \inf_{π \text{ feasible}} V_{N,0}^π(x,ρ)`, the value function (general belief
`ρ`) of a minimization problem (`QP(b)`, Theorem 6.2.2) over history-dependent strategies. -/
noncomputable def Jinf (M : FilterMarket EY d) (Fd : FilterOp M) (i : ℕ → ℝ) (term : ℝ → ℝ)
    (D : ℝ → Set (Fin d → ℝ)) (N : ℕ) (x0 : ℝ) (ρ0 : Measure EY) : EReal :=
  ⨅ π ∈ {π : HistPolicy d | IsFeasiblePolicy D i x0 N π}, Vpi M Fd i term π N 0 (fun _ => 0) x0 ρ0

/-- The wealth process reached under the *Markov* strategy built from a sequence `fs : ℕ → ℝ ×
\text{Measure } EY → A` of stage-`n` decision rules (each depending on the current wealth and the
current filter belief only), folding `fs`'s own dependence on the wealth-so-far directly into the
recursion rather than going through the generic `xOf`/`HistPolicy` detour (which would otherwise
be mutually, not structurally, recursive with the policy it builds). -/
noncomputable def xOfMarkov (M : FilterMarket EY d) (Fd : FilterOp M) (i : ℕ → ℝ) (x0 : ℝ)
    (fs : ℕ → ℝ × Measure EY → Fin d → ℝ) : (n : ℕ) → (ℕ → (Fin d → ℝ)) → ℝ
  | 0, _ => x0
  | (n + 1), zs =>
      let xn := xOfMarkov M Fd i x0 fs n zs
      let an := fs n (xn, FilterOp.mu M Fd n zs)
      (1 + i (n + 1)) * (xn + ∑ j, an j * zs (n + 1) j)

/-- A **Markov decision rule** `f : ℝ × \text{Measure } EY → A` at stage `n`, packaged into the
strategy that reads off the current wealth and current filter belief from the return history so
far via `xOfMarkov`/`FilterOp.mu`, exactly `f_n(h_n) := f_n^*(x_n,μ_n(\cdot|h_n))` (Bäuerle–Rieder,
Theorem 6.1.1d, Theorem 6.1.2b, etc.): the strategy built from a *sequence* `fs : ℕ → ℝ ×
\text{Measure } EY → A` of stage-`n` Markov decision rules. -/
noncomputable def ofMarkov (M : FilterMarket EY d) (Fd : FilterOp M) (i : ℕ → ℝ) (x0 : ℝ)
    (fs : ℕ → ℝ × Measure EY → Fin d → ℝ) : HistPolicy d :=
  fun n zs => fs n (xOfMarkov M Fd i x0 fs n zs, FilterOp.mu M Fd n zs)

end MDPFinance.POMDPFinance


