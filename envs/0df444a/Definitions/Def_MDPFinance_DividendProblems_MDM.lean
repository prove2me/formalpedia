-- Prove2me | Definitions.Def_MDPFinance_DividendProblems_MDM
-- name    : MDPFinance_DividendProblems_MDM
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:11:52.327454+00:00
-- url     : https://prove2.me/theorems/a5817ef7-b0cb-44b3-b03b-92abf5eb531f
-- title:
--   A generic stationary Markov Decision Model (restated, real-valued contracting theory)
-- statement:
--   Both numbered models of this chunk — the random-horizon consumption-investment model of §9.1 and the discrete dividend model of §9.2 — are instances of the same stationary, infinite-horizon, real-valued Markov Decision Model `(E,A,D,\mathrm{step},r,\beta)` Chapter 7 builds its contracting theory around. This item restates (own namespace copy) exactly the pieces of that theory this chunk's two subsections need: the one-stage operators `T'`/`T_\circ`, the reward-to-go `J_n^\pi`/`J_n`/`J_\infty` via this series' `limsup`-of-truncations convention, the regularity class $IB_b$ and its weighted norm, bounding functions (Definition 7.3.1), and the policy-iteration vocabulary (`\mathrm{Ls}`, `D^*`) needed to state Theorem 9.1.1's own "policy iteration holds" clause faithfully.
--
--   **Formalization Note.** `step` gives the one-step transition measure directly as a plain function to `Measure E` (not a bundled `Kernel`), avoiding a measurability-proof obligation neither of this chunk's two models' own theorems needs discharged.
--
--   **Moderation note.** The draft's restated apparatus took real-valued (Bochner) integrals and real suprema over *all* maps `ℕ → E → A` as the value functions: with an inadmissible action the reward `a` is unbounded, so the real supremum is `0` and `J_∞ ≡ 0` — every bound of §9.2 was then refutable. Both models of this chunk are positive (`r ≥ 0`), so rewards and values are now in `[0,∞]` with Lebesgue integrals, `Q` is a Markov kernel, `D(x)` is nonempty, policies range over measurable decision rules with `f(x) ∈ D(x)` (`F^∞`), `J_{∞π} = lim_n J_{nπ}` is the supremum of the increasing sequence, and maximizers are defined against the `[0,∞]`-valued operator `T`; the real operator `T'` remains only for the fixed-point statements in `IB_b`, where it is genuine.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 194-208, PDF 205-219, Chapter 7's contracting theory (restated from chunk `07a`'s identical apparatus, per this series' file-ownership boundary)

import Mathlib

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Topology

namespace MDPFinance.DividendProblems

/-- A stationary, infinite-horizon **positive** Markov Decision Model `(E,A,D,Q,r,\beta)`
(Bäuerle–Rieder, Ch. 7, restated — own namespace copy per this series' file-ownership boundary):
both the random-horizon consumption-investment model (§9.1, utilities `\ge 0`) and the discrete
dividend model (§9.2, `r(x,a) = a \ge 0`) are positive models, so rewards are recorded in
`[0,\infty]` and every value below is a Lebesgue integral — no real-valued integral or supremum
that silently returns `0`. `step` is a Markov kernel (`Q`), and every `D(x)` is nonempty. -/
structure StationaryMDM (E A : Type*) [MeasurableSpace E] [MeasurableSpace A] where
  D : Set (E × A)
  hD_nonempty : ∀ x, {a | (x, a) ∈ D}.Nonempty
  step : Kernel (E × A) E
  isMarkov : IsMarkovKernel step
  r : E × A → ℝ≥0∞
  β : ℝ
  hβ : 0 < β

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

def StationaryMDM.Dx (M : StationaryMDM E A) (x : E) : Set A :=
  {a | (x, a) ∈ M.D}

/-- A decision rule `f \in F`: measurable with `f(x) \in D(x)` (Bäuerle–Rieder, Definition
2.1.5 / p. 194). -/
def StationaryMDM.IsDecisionRuleOf (M : StationaryMDM E A) (f : E → A) : Prop :=
  Measurable f ∧ ∀ x, (x, f x) ∈ M.D

/-- A Markov policy `\pi = (f_0,f_1,\dots) \in F^\infty`. -/
def StationaryMDM.IsPolicyOf (M : StationaryMDM E A) (π : ℕ → E → A) : Prop :=
  ∀ n, M.IsDecisionRuleOf (π n)

/-- `IB_b := \{v : E \to \mathbb R \mid v \text{ measurable}, \exists c \ge 0, |v(x)| \le
c\,b(x)\}` (Bäuerle–Rieder, p. 29/205). -/
def IBb (b : E → ℝ) : Set (E → ℝ) :=
  {v | Measurable v ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ x, |v x| ≤ c * b x}

/-- `Tv(x) := \sup_{a \in D(x)} [r(x,a) + \beta \int v\,dQ(\cdot|x,a)]` on `[0,\infty]`-valued
`v` (the positive model's operator, Bäuerle–Rieder, p. 195/213). -/
noncomputable def TL (M : StationaryMDM E A) (v : E → ℝ≥0∞) (x : E) : ℝ≥0∞ :=
  ⨆ a ∈ M.Dx x, M.r (x, a) + ENNReal.ofReal M.β * ∫⁻ y, v y ∂(M.step (x, a))

/-- The same operator on real-valued `v \in IB_b` (used for the fixed-point statements in
`IB_b`; genuine there because `D(x) \ne \emptyset` and `v` is `b`-bounded). -/
noncomputable def T' (M : StationaryMDM E A) (v : E → ℝ) (x : E) : ℝ :=
  ⨆ a ∈ M.Dx x, (M.r (x, a)).toReal + M.β * ∫ y, v y ∂(M.step (x, a))

/-- `T_\circ v(x) := \sup_{a \in D(x)} \beta \int v\,dQ(\cdot|x,a)` (Bäuerle–Rieder, Definition
7.1.2), on `[0,\infty]`-valued `v`. -/
noncomputable def TcircL (M : StationaryMDM E A) (v : E → ℝ≥0∞) (x : E) : ℝ≥0∞ :=
  ⨆ a ∈ M.Dx x, ENNReal.ofReal M.β * ∫⁻ y, v y ∂(M.step (x, a))

/-- `f` is a maximizer of `v` (Bäuerle–Rieder, Definition 7.1.3): a decision rule attaining
`Tv(x)` at every `x`. -/
def StationaryMDM.IsMaximizerOf (M : StationaryMDM E A) (v : E → ℝ≥0∞) (f : E → A) : Prop :=
  M.IsDecisionRuleOf f ∧
    ∀ x, M.r (x, f x) + ENNReal.ofReal M.β * ∫⁻ y, v y ∂(M.step (x, f x)) = TL M v x

/-- `J_{n\pi}(x)`, the `n`-stage reward under `\pi = (f_0,f_1,\dots)` (Bäuerle–Rieder, p. 194),
in `[0,\infty]`. -/
noncomputable def Jnpi (M : StationaryMDM E A) (π : ℕ → E → A) : (n : ℕ) → E → ℝ≥0∞
  | 0, _ => 0
  | (n + 1), x =>
      M.r (x, π 0 x) +
        ENNReal.ofReal M.β * ∫⁻ y, Jnpi M (fun k => π (k + 1)) n y ∂(M.step (x, π 0 x))

/-- `J_n(x) := \sup_{\pi \in F^\infty} J_{n\pi}(x)`. -/
noncomputable def Jn (M : StationaryMDM E A) (n : ℕ) (x : E) : ℝ≥0∞ :=
  ⨆ π : ℕ → E → A, ⨆ (_ : M.IsPolicyOf π), Jnpi M π n x

/-- `J_{\infty\pi}(x) := \lim_n J_{n\pi}(x)` — for a positive model the limit of the increasing
sequence `(J_{n\pi}(x))`, i.e. its supremum. -/
noncomputable def Jinfpi (M : StationaryMDM E A) (π : ℕ → E → A) (x : E) : ℝ≥0∞ :=
  ⨆ n, Jnpi M π n x

/-- `J_\infty(x) := \sup_{\pi \in F^\infty} J_{\infty\pi}(x)`. -/
noncomputable def Jinf (M : StationaryMDM E A) (x : E) : ℝ≥0∞ :=
  ⨆ π : ℕ → E → A, ⨆ (_ : M.IsPolicyOf π), Jinfpi M π x

/-- A bounding function (Bäuerle–Rieder, Definition 7.1.1 / 7.3.1): `r(x,a) \le c_r b(x)` and
`\int b\,dQ(\cdot|x,a) \le \alpha_b b(x)` on `D` (Lebesgue integrals of `b \ge 0`). -/
structure IsBoundingFunction (M : StationaryMDM E A) (b : E → ℝ) (cr αb : ℝ) : Prop where
  hb_meas : Measurable b
  hb_nonneg : ∀ x, 0 ≤ b x
  hcr : 0 ≤ cr
  hαb : 0 ≤ αb
  hr : ∀ xa ∈ M.D, M.r xa ≤ ENNReal.ofReal (cr * b xa.1)
  hstep : ∀ xa ∈ M.D, ∫⁻ y, ENNReal.ofReal (b y) ∂(M.step xa) ≤ ENNReal.ofReal (αb * b xa.1)

variable [TopologicalSpace A]

/-- `\mathrm{Ls}\,D_n(x)`, the upper limit of a sequence of sets (Bäuerle–Rieder, p. 201): the
accumulation points of sequences `(a_n)` with `a_n \in D_n`. -/
def LsSeq (Dn : ℕ → Set A) : Set A :=
  {a | ∃ an : ℕ → A, (∀ n, an n ∈ Dn n) ∧ MapClusterPt a atTop an}

/-- `D^*_J(x) := \{a \in D(x) \mid a \text{ is a maximum point of } a \mapsto r(x,a) + \beta
\int J\,dQ(\cdot|x,a)\}` (Bäuerle–Rieder, p. 201). -/
def Dstar (M : StationaryMDM E A) (Jval : E → ℝ≥0∞) (x : E) : Set A :=
  {a | a ∈ M.Dx x ∧ ∀ a' ∈ M.Dx x,
    M.r (x, a') + ENNReal.ofReal M.β * ∫⁻ y, Jval y ∂(M.step (x, a')) ≤
      M.r (x, a) + ENNReal.ofReal M.β * ∫⁻ y, Jval y ∂(M.step (x, a))}

end MDPFinance.DividendProblems


