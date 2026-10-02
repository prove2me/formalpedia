-- Prove2me | Definitions.Def_MDPFinance_IndifferencePricing_IndexTrackingMarket
-- name    : MDPFinance_IndifferencePricing_IndexTrackingMarket
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:09:43.473777+00:00
-- url     : https://prove2.me/theorems/c02e7997-dd4f-4399-afad-4d877e2b525e
-- title:
--   The index-tracking Markov Decision Model and its cost-to-go value function
-- statement:
--   State $(x,\hat s)\in E:=\mathbb{R}\times\mathbb{R}$ (wealth, non-traded index value),
--   action $a\in A:=\mathbb{R}^d$ (amounts invested in $d$ traded assets), transition
--   $T_n((x,\hat s),a,(z_1,z_2)) := ((1+i_{n+1})(x+a\cdot z_1),\ \hat s\,z_2)$. The investor
--   minimizes the quadratic tracking error
--   $$V_n(x,\hat s) := \inf_\pi \mathbb{E}\Big[\sum_{k=n}^N (X_k-\hat S_k)^2\Big]$$
--   over admissible Markov strategies (Bäuerle–Rieder, Eq. (4.36)), i.e. the investor tries to
--   replicate the value of an index $\hat S$ that cannot itself be traded, using only the $d$
--   traded assets.
--
--   **Formalization Note.** `stateAcc` accumulates the running cost $(X_k-\hat S_k)^2$ at every
--   intermediate time $k=n,\dots,N$ alongside the evolving state, mirroring the accumulator pattern
--   used for running-reward models elsewhere in this book's missions (e.g. chunk `04b`'s
--   `ConsumptionInvestmentMarket.stateAcc`).
--
--   **Moderation note.** The market carries the section's standing assumptions as fields: the Section 3.1 financial market ($1+i_n>0$, relative risks $R_n>-1$), the positive non-traded return $\hat R_n>0$, independence of the vectors $(R_1,\hat R_1),(R_2,\hat R_2),\dots$, finite second moments (p. 51: "we assume that all expectations exist"), and $\mathbb{E}[R_{n+1}R_{n+1}^\top]$ regular, which Theorem 4.8.1(b)'s inverse presupposes. The tracking cost is a Lebesgue integral in $[0,\infty]$ (the integrand is nonnegative), so a strategy without a finite expected cost has cost $\infty$ rather than a spurious value; $V_n$ and $V^\pi$ take values in $[0,\infty]$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 133, PDF 147, Equation (4.36) and unnumbered model summary

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.IndifferencePricing

/-- The index-tracking Markov Decision Model (Bäuerle–Rieder, p. 133, PDF 147): state
`(x,ŝ) ∈ E := ℝ × ℝ` (wealth, value of the non-traded index), action `a ∈ A := ℝ^d` (amounts
invested in the `d` traded assets), transition `T_n((x,ŝ),a,(z1,z2)) := ((1+i_{n+1})(x+a·z1),
ŝz2)` where `z1` is the traded assets' relative risk and `z2` the non-traded asset's relative
price change; running and terminal cost `(x-ŝ)^2` (a cost-minimization problem, Eq. (4.36)).
Standing assumptions carried as fields: the financial market of Section 3.1 (`1+i_n > 0`,
relative risks `R_n > -1`), the positive non-traded return `R̂_n > 0`, independence of the
vectors `(R_1,R̂_1), (R_2,R̂_2), …` (p. 132), finite second moments so that every expectation
in Theorem 2.6.3 / 4.8.1 exists (p. 51: "we assume that all expectations exist"), and
`𝔼[R_{n+1}R_{n+1}ᵀ]` regular, which is what Theorem 4.8.1(b)'s inverse `(𝔼[R_{n+1}R_{n+1}ᵀ])⁻¹`
and Theorem 2.6.3's "𝔼[Bᵀ Q B] positive definite" presuppose. -/
structure IndexTrackingMarket (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) where
  measIP : Measure Ω
  isProb : IsProbabilityMeasure measIP
  N : ℕ
  i : ℕ → ℝ
  hi_pos : ∀ n, 1 ≤ n → n ≤ N → 0 < 1 + i n
  R : ℕ → Ω → (Fin d → ℝ)
  hR_meas : ∀ n, Measurable (R n)
  hR_gt : ∀ n, 1 ≤ n → n ≤ N → ∀ j, ∀ᵐ ω ∂measIP, -1 < R n ω j
  Rhat : ℕ → Ω → ℝ
  hRhat_meas : ∀ n, Measurable (Rhat n)
  hRhat_pos : ∀ n, 1 ≤ n → n ≤ N → ∀ᵐ ω ∂measIP, 0 < Rhat n ω
  hR_indep : iIndepFun (fun n : Fin N => fun ω => (R (n.val + 1) ω, Rhat (n.val + 1) ω)) measIP
  hR_L2 : ∀ n, 1 ≤ n → n ≤ N → ∀ j, MemLp (fun ω => R n ω j) 2 measIP
  hRhat_L2 : ∀ n, 1 ≤ n → n ≤ N → MemLp (Rhat n) 2 measIP
  hRR_posdef : ∀ n, 1 ≤ n → n ≤ N →
    (Matrix.of fun j k : Fin d => ∫ ω, R n ω j * R n ω k ∂measIP).PosDef

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- A Markov strategy `φ : ℕ → ℝ×ℝ → ℝ^d` is admissible over `[n,N)` if `φ k` is measurable for
every `n ≤ k < N` (`D(x,ŝ) := A`, no further restriction, Bäuerle–Rieder p. 133). -/
def IndexTrackingMarket.IsAdmissible (M : IndexTrackingMarket Ω d) (n : ℕ)
    (φ : ℕ → ℝ × ℝ → (Fin d → ℝ)) : Prop :=
  ∀ k, n ≤ k → k < M.N → Measurable (φ k)

/-- The state `(X_k,Ŝ_k)` reached after `k` steps from time `n`, state `(x,ŝ)`, under `φ`, on
path `ω`, paired with the accumulated tracking cost `Σ_{j=n}^{n+k} (X_j-Ŝ_j)^2`. -/
noncomputable def IndexTrackingMarket.stateAcc (M : IndexTrackingMarket Ω d)
    (φ : ℕ → ℝ × ℝ → (Fin d → ℝ)) : (k : ℕ) → (n : ℕ) → (x ŝ : ℝ) → (ω : Ω) → ℝ × ℝ × ℝ
  | 0, _, x, ŝ, _ => (x, ŝ, (x - ŝ) ^ 2)
  | (k + 1), n, x, ŝ, ω =>
      let a := φ n (x, ŝ)
      let x' := (1 + M.i (n + 1)) * (x + ∑ j, a j * M.R (n + 1) ω j)
      let ŝ' := ŝ * M.Rhat (n + 1) ω
      let rest := M.stateAcc φ k (n + 1) x' ŝ' ω
      (rest.1, rest.2.1, (x - ŝ) ^ 2 + rest.2.2)

/-- The tracking cost `𝔼[Σ_{k=n}^N (X_k-Ŝ_k)^2] ∈ [0,∞]` of a fixed strategy `φ` from time `n`,
state `(x,ŝ)` (Bäuerle–Rieder, p. 133, PDF 147). The integrand is nonnegative, so the
expectation is a Lebesgue integral in `ℝ≥0∞`: a strategy whose cost has no finite expectation
has cost `∞`, as in the book's cost-minimization framework (`r ≤ 0`, `b ≡ 1`, p. 51). -/
noncomputable def IndexTrackingMarket.trackingCostPi (M : IndexTrackingMarket Ω d)
    (φ : ℕ → ℝ × ℝ → (Fin d → ℝ)) (n : ℕ) (x ŝ : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (M.stateAcc φ (M.N - n) n x ŝ ω).2.2 ∂M.measIP

/-- The value function `V_n(x,ŝ) := inf_φ 𝔼[Σ_{k=n}^N (X_k-Ŝ_k)^2]` over admissible Markov
strategies (Bäuerle–Rieder, p. 133, PDF 147). -/
noncomputable def IndexTrackingMarket.V (M : IndexTrackingMarket Ω d) (n : ℕ) (x ŝ : ℝ) :
    ℝ≥0∞ :=
  ⨅ φ ∈ {φ : ℕ → ℝ × ℝ → (Fin d → ℝ) | M.IsAdmissible n φ}, M.trackingCostPi φ n x ŝ

/-- The value of a fixed admissible strategy `φ` from time `0`. -/
noncomputable def IndexTrackingMarket.Vpi (M : IndexTrackingMarket Ω d)
    (φ : ℕ → ℝ × ℝ → (Fin d → ℝ)) (x ŝ : ℝ) : ℝ≥0∞ :=
  M.trackingCostPi φ 0 x ŝ

end MDPFinance.IndifferencePricing


