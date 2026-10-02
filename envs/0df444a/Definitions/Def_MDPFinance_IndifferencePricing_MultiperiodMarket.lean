-- Prove2me | Definitions.Def_MDPFinance_IndifferencePricing_MultiperiodMarket
-- name    : MDPFinance_IndifferencePricing_MultiperiodMarket
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:09:43.571055+00:00
-- url     : https://prove2.me/theorems/d7cbca1f-afd6-427b-be5f-ab71bbb054f8
-- title:
--   The multiperiod indifference-pricing market, its value function, and the indifference price at time n
-- statement:
--   The $N$-period extension of the one-period market: state $(x,s,\hat s)\in E:=
--   \mathbb{R}\times\mathbb{R}_{>0}\times\mathbb{R}_{>0}$, action $a\in\mathbb{R}$, i.i.d.
--   relative returns $(\tilde R_n,\hat R_n)$, transition $(x,s,\hat s)\mapsto(x+a(z_1-1),
--   sz_1,\hat sz_2)$. For a claim $H=h(S_m,\hat S_m)$ maturing at time $m$,
--   $$V_n^H(x,s,\hat s;m) := \sup_\pi \mathbb{E}\big[-e^{-\gamma(X_m-h(S_m,\hat S_m))}\big]$$
--   (`VHAt`, generalized from the book's own fixed maturity $N$ to a general $m\ge n$ in order to
--   state Theorem 4.9.4(c)'s consistency condition, which prices a claim maturing at $n+1$); the
--   indifference price $v_n(H,s,\hat s)$ at time $n$ solves $V_n^0(x,\cdot)=V_n^H(x+v_n,\cdot)$ for
--   all $x$ (`IsIndifferencePriceAt`, the multiperiod analogue of Definition 4.9.1). Also
--   $v:=\inf_a\mathbb{E}[e^{-\gamma a(\tilde R_1-1)}]$ (Eq. (4.39)).
--
--   **Formalization Note.** `VHAt`'s explicit maturity parameter `m` (rather than always `M.N`) is
--   this file's one deviation from the book's own notation, needed solely to state part c)'s
--   consistency condition (pricing, at time $n$, a claim maturing at $n+1$ whose payoff is itself an
--   indifference price) inside the same value-function machinery as parts a)-b).
--
--   **Moderation note.** The book's multiperiod market has i.i.d. return vectors "with the same distribution as in the last section"; the structure now carries that four-atom law ($u,d,\hat u,\hat d$, $p_1,\dots,p_4>0$ under (FM)) for $n=1,\dots,N$ and independence of $(\tilde R_1,\hat R_1),\dots,(\tilde R_N,\hat R_N)$. Without (FM) the constant $v$ of (4.39) can be $0$ (e.g. $\tilde R>1$ a.s.), which makes $v^{N-n}$ and $\log(d_n/v^{N-n})$ meaningless, and without independence the dynamic-programming solution of Theorem 4.9.4 fails.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 137-138, PDF 151-152, Equations (4.38)-(4.39) and unnumbered model summary

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.IndifferencePricing

/-- The multiperiod financial market underlying indifference pricing (Bäuerle–Rieder, p. 137,
PDF 151-152): a bond with zero interest, a traded asset `S` and a non-traded asset `Ŝ` with i.i.d.
relative returns `(R̃_n,R̂_n)`, state `(x,s,ŝ) ∈ E := ℝ × ℝ_{>0} × ℝ_{>0}`, action `a ∈ A := ℝ`,
transition `(x,s,ŝ) ↦ (x+a(z1-1), sz1, ŝz2)`, exponential utility `U(x) = -e^{-γx}`. The
return vectors `(R̃_1,R̂_1), (R̃_2,R̂_2), …` are independent with the four-atom law of the
one-period market of p. 135 ("the same distribution as in the last section"): values
`(u,û),(u,d̂),(d,û),(d,d̂)` with probabilities `p1,…,p4 > 0`, under Assumption (FM)
`0 < d < 1 < u`, `d̂ < û`. -/
structure MultiperiodIndifferenceMarket (Ω : Type*) [MeasurableSpace Ω] where
  measIP : Measure Ω
  isProb : IsProbabilityMeasure measIP
  N : ℕ
  u : ℝ
  d : ℝ
  uhat : ℝ
  dhat : ℝ
  h0d : 0 < d
  hd1 : d < 1
  h1u : 1 < u
  hdhat_uhat : dhat < uhat
  γ : ℝ
  hγ : 0 < γ
  Rtilde : ℕ → Ω → ℝ
  Rhat : ℕ → Ω → ℝ
  hRtilde_meas : ∀ n, Measurable (Rtilde n)
  hRhat_meas : ∀ n, Measurable (Rhat n)
  p1 : ℝ
  p2 : ℝ
  p3 : ℝ
  p4 : ℝ
  hp_pos : 0 < p1 ∧ 0 < p2 ∧ 0 < p3 ∧ 0 < p4
  hp_sum : p1 + p2 + p3 + p4 = 1
  hlaw1 : ∀ n, 1 ≤ n → n ≤ N →
    measIP {ω | Rtilde n ω = u ∧ Rhat n ω = uhat} = ENNReal.ofReal p1
  hlaw2 : ∀ n, 1 ≤ n → n ≤ N →
    measIP {ω | Rtilde n ω = u ∧ Rhat n ω = dhat} = ENNReal.ofReal p2
  hlaw3 : ∀ n, 1 ≤ n → n ≤ N →
    measIP {ω | Rtilde n ω = d ∧ Rhat n ω = uhat} = ENNReal.ofReal p3
  hlaw4 : ∀ n, 1 ≤ n → n ≤ N →
    measIP {ω | Rtilde n ω = d ∧ Rhat n ω = dhat} = ENNReal.ofReal p4
  hR_indep : iIndepFun (fun n : Fin N => fun ω => (Rtilde (n.val + 1) ω, Rhat (n.val + 1) ω))
    measIP

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A Markov strategy `φ : ℕ → ℝ×ℝ×ℝ → ℝ` is admissible over `[n,N)` if `φ k` is measurable for
every `n ≤ k < N` (`D(x,s,ŝ) := A`, Bäuerle–Rieder p. 138, PDF 152). -/
def MultiperiodIndifferenceMarket.IsAdmissible (M : MultiperiodIndifferenceMarket Ω) (n : ℕ)
    (φ : ℕ → ℝ × ℝ × ℝ → ℝ) : Prop :=
  ∀ k, n ≤ k → k < M.N → Measurable (φ k)

/-- The state `(X_k,S_k,Ŝ_k)` reached after `k` steps from time `n`, state `(x,s,ŝ)`, under `φ`,
on path `ω`. -/
noncomputable def MultiperiodIndifferenceMarket.terminalState (M : MultiperiodIndifferenceMarket Ω)
    (φ : ℕ → ℝ × ℝ × ℝ → ℝ) : (k : ℕ) → (n : ℕ) → (x s ŝ : ℝ) → (ω : Ω) → ℝ × ℝ × ℝ
  | 0, _, x, s, ŝ, _ => (x, s, ŝ)
  | (k + 1), n, x, s, ŝ, ω =>
      let a := φ n (x, s, ŝ)
      M.terminalState φ k (n + 1) (x + a * (M.Rtilde (n + 1) ω - 1)) (s * M.Rtilde (n + 1) ω)
        (ŝ * M.Rhat (n + 1) ω) ω

/-- The value function `V_n^H(x,s,ŝ) := sup_φ 𝔼[-e^{-γ(X_m - h(S_m,Ŝ_m))}]` for a claim `H =
h(S_m,Ŝ_m)` maturing at time `m ≥ n` (Bäuerle–Rieder, Eq. (4.38), p. 138, PDF 152, generalized
from maturity `N` to a general maturity `m` in order to state Theorem 4.9.4(c)'s consistency
condition, which prices a claim maturing at `n+1`). -/
noncomputable def MultiperiodIndifferenceMarket.VHAt (M : MultiperiodIndifferenceMarket Ω)
    (h : ℝ → ℝ → ℝ) (m n : ℕ) (x s ŝ : ℝ) : ℝ :=
  ⨆ φ ∈ {φ : ℕ → ℝ × ℝ × ℝ → ℝ | M.IsAdmissible n φ},
    ∫ ω, (fun p => -Real.exp (-M.γ * (p.1 - h p.2.1 p.2.2)))
      (M.terminalState φ (m - n) n x s ŝ ω) ∂M.measIP

/-- `V_n^H` at the model's own final horizon `N` (Bäuerle–Rieder, Eq. (4.38)). -/
noncomputable def MultiperiodIndifferenceMarket.VH (M : MultiperiodIndifferenceMarket Ω)
    (h : ℝ → ℝ → ℝ) (n : ℕ) (x s ŝ : ℝ) : ℝ :=
  M.VHAt h M.N n x s ŝ

/-- The indifference price of a claim `H = h(S_m,Ŝ_m)` at time `n ≤ m`, `v_n = v_n(H,s,ŝ)`, is
the amount such that `V_n^0(x,s,ŝ) = V_n^H(x+v_n,s,ŝ)` for all `x` (Bäuerle–Rieder, unnumbered
display, p. 138, PDF 152, the multiperiod extension of Definition 4.9.1). -/
def MultiperiodIndifferenceMarket.IsIndifferencePriceAt (M : MultiperiodIndifferenceMarket Ω)
    (h : ℝ → ℝ → ℝ) (m n : ℕ) (s ŝ vn : ℝ) : Prop :=
  ∀ x : ℝ, M.VHAt (fun _ _ => 0) m n x s ŝ = M.VHAt h m n (x + vn) s ŝ

/-- `v := inf_a 𝔼[e^{-γa(R̃_1-1)}]` (Bäuerle–Rieder, Eq. (4.39), p. 138, PDF 152). -/
noncomputable def MultiperiodIndifferenceMarket.vGeneric (M : MultiperiodIndifferenceMarket Ω) :
    ℝ :=
  ⨅ a : ℝ, ∫ ω, Real.exp (-M.γ * a * (M.Rtilde 1 ω - 1)) ∂M.measIP

end MDPFinance.IndifferencePricing


