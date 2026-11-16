-- Prove2me | Definitions.Def_HSOSetCover_FullCover_Supplement_OneTurn
-- name    : HSOSetCover_FullCover_Supplement_OneTurn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:11:30.182748+00:00
-- url     : https://prove2.me/theorems/4636216a-1e8f-4379-9fcf-210a7dd91984
-- title:
--   One-turn partial-cover batches, the history-conditional guarantee, $\mathrm{OPT}^{\mathrm{risk}}_\eta$, $r_0$, $r_1$ and the greedy multicover step
-- statement:
--   In the one-turn model of §5, the oracles are indexed by $[k]$, and each oracle $i$ has a known set $V_i\subseteq U$. A call-count vector $\zeta\in\mathbb Z^k_{\ge0}$ issues $\zeta_i$ concurrent calls to oracle $i$. On a probability space, each call $(i,a)$ returns a random partial cover and has a realized token cost $\mathrm{TOK}_{i,a}$ and a latency. The responses are processed in a fixed order, and no independence among calls is assumed.
--
--   The **history-conditional guarantee** with parameter $p$ holds if the following is true for every processed position whose call is to oracle $i$, every $e\in V_i$, and every positive-probability history of earlier processed responses whose residual (after the retention rule) contains $e$: conditionally on that history, the call's partial cover satisfies the local dual-certification condition for that residual and covers $e$ with probability at least $p$.
--
--   The batch succeeds if the retained partial covers form a certified $\rho$-cover and every call finishes by $D$.
--
--   With $q=1-p$, the quantities of the analysis are:
--   1. $d_e(\zeta)=\sum_{i:e\in V_i}\zeta_i$;
--   2. $c(\zeta)=\sum_ic_i\zeta_i$;
--   3. the risk sum $\sum_{e}q^{d_e(\zeta)}$;
--   4. $\mathrm{OPT}^{\mathrm{risk}}_\eta=\min\{c(\zeta):\sum_eq^{d_e(\zeta)}\le1-\eta\}$;
--   5. $r_0=\lceil\ln(1/(1-\eta))/\ln(1/q)\rceil$ and $r_1=\lceil\ln(n/(1-\eta))/\ln(1/q)\rceil$;
--   6. the potential $\Phi(\zeta)=\sum_e\min\{r_1,d_e(\zeta)\}$ and the marginals $\Delta_i(\zeta)=|\{e\in V_i:d_e(\zeta)<r_1\}|$.
--
--   One **greedy step**, taken while $\Phi(\zeta)<nr_1$, picks any $i$ with $\Delta_i(\zeta)>0$ minimizing $c_i/\Delta_i(\zeta)$ and increments $\zeta_i$.
--
--   These objects state Theorem 4.
--
--   **Formalization Note** A history is the exact list of earlier processed responses; the conditional bound is written in the multiplicative form $\mathbb P(E\cap H)\ge p\,\mathbb P(H)$. $\mathrm{OPT}^{\mathrm{risk}}_\eta$ is a real infimum.
-- source:
--   Jie Wang, Computing Weighted Set Covers with Heterogeneous Stochastic Oracles: Deadline-Constrained Token Complexity, STOC 2027 submission #191 (October 2026), SHA-256 d7c07e91dc65c2dd29234b0edf05fe6bcfcbee569eb1a14c07b3e0f337ca7a48, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/191.pdf, §5, PDF pp. 9–10 / printed pp. 8–9 (model, history-conditional guarantee, d_e, c(ζ), OPT^risk_η, r_0, r_1, Φ, Δ_i, greedy)

import Mathlib
import Definitions.Def_HSOSetCover_FullCover_Supplement_WSC

open MeasureTheory

namespace HSOSetCover.FullCover.Supplement

variable {U ι : Type*} [Fintype U] [DecidableEq U] [Fintype ι] [DecidableEq ι]
variable {k : ℕ}

/-! ### §5: one-turn selection with partial-cover responses (PDF pp. 9–10) -/

/-- `d_e(ζ) = ∑_{i : e ∈ V_i} ζ_i`, the number of calls in the batch `ζ` whose oracle's guarantee
set `V_i` contains `e`. -/
def callDegree (V : Fin k → Finset U) (ζ : Fin k → ℕ) (e : U) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i => e ∈ V i), ζ i

/-- `c(ζ) = ∑_i c_i ζ_i`, the almost-sure bound on the batch's token cost. -/
noncomputable def batchBound (c : Fin k → ℝ) (ζ : Fin k → ℕ) : ℝ := ∑ i, c i * ζ i

/-- The failure-risk bound `∑_{e ∈ U} q^{d_e(ζ)}`, `q = 1 - p`. -/
noncomputable def riskSum (V : Fin k → Finset U) (p : ℝ) (ζ : Fin k → ℕ) : ℝ :=
  ∑ e, (1 - p) ^ callDegree V ζ e

/-- `OPT^risk_η`, the minimum of `c(ζ)` over `ζ ∈ ℤ^k_{≥0}` with `∑_e q^{d_e(ζ)} ≤ 1 - η`
(PDF p. 9). Under the standing assumptions (`⋃_i V_i = U`, `p ∈ (0,1)`) the set is nonempty, and
it is bounded below by `0` when the `c_i` are nonnegative. -/
noncomputable def optRisk (V : Fin k → Finset U) (c : Fin k → ℝ) (p η : ℝ) : ℝ :=
  sInf {v | ∃ ζ : Fin k → ℕ, riskSum V p ζ ≤ 1 - η ∧ v = batchBound c ζ}

/-- `r₀ = ⌈ln(1/(1-η)) / ln(1/q)⌉` (PDF p. 10). -/
noncomputable def r0 (p η : ℝ) : ℕ := ⌈Real.log (1 / (1 - η)) / Real.log (1 / (1 - p))⌉₊

/-- `r₁ = ⌈ln(n/(1-η)) / ln(1/q)⌉` with `n = |U|` (PDF p. 10). -/
noncomputable def r1 (U : Type*) [Fintype U] (p η : ℝ) : ℕ :=
  ⌈Real.log (Fintype.card U / (1 - η)) / Real.log (1 / (1 - p))⌉₊

/-- `Φ(ζ) = ∑_{e ∈ U} min{r, d_e(ζ)}` (PDF p. 10, with `r = r₁`). -/
def coverPotential (V : Fin k → Finset U) (r : ℕ) (ζ : Fin k → ℕ) : ℕ :=
  ∑ e, min r (callDegree V ζ e)

/-- `Δ_i(ζ) = |{e ∈ V_i : d_e(ζ) < r}|`, computed by scanning `V_i` (PDF p. 10). -/
def marginal (V : Fin k → Finset U) (r : ℕ) (ζ : Fin k → ℕ) (i : Fin k) : ℕ :=
  ((V i).filter (fun e => callDegree V ζ e < r)).card

/-- One iteration of the greedy multicover algorithm (PDF p. 10), with any tie-break: while
`Φ(ζ) < n r`, choose an oracle `i` with `Δ_i(ζ) > 0` minimizing `c_i / Δ_i(ζ)` and increase `ζ_i`
by `1`. -/
def GreedyStep (V : Fin k → Finset U) (c : Fin k → ℝ) (r : ℕ) (ζ ζ' : Fin k → ℕ) : Prop :=
  coverPotential V r ζ < Fintype.card U * r ∧
    ∃ i, 0 < marginal V r ζ i ∧
      (∀ i', 0 < marginal V r ζ i' → c i / marginal V r ζ i ≤ c i' / marginal V r ζ i') ∧
      ζ' = Function.update ζ i (ζ i + 1)

/-- The calls of the one-turn batch `ζ`: the pairs `(i, a)` with `a < ζ_i` (the `a`-th call to
oracle `i`). -/
abbrev Call (ζ : Fin k → ℕ) : Type := Σ i : Fin k, Fin (ζ i)

/-- The one-turn batch `ζ` of §5 (PDF p. 9) on a measurable space `Ω` of outcomes: a fixed order in
which the PTM processes the responses after all calls finish, and for each call `(i, a)` its random
partial cover (a subfamily of the candidate indices), its realized token cost `TOK_{i,a}` and its
latency. No independence among calls is assumed. -/
structure OneTurnBatch (ι : Type*) (ζ : Fin k → ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  /-- The processing order: `order j` is the `j`-th processed call. -/
  order : Fin (∑ i, ζ i) ≃ Call ζ
  /-- The partial cover returned by a call. -/
  resp : Call ζ → Ω → Finset ι
  /-- The realized token cost `TOK_{i,a}` of a call. -/
  tok : Call ζ → Ω → ℝ
  /-- The latency of a call. -/
  lat : Call ζ → Ω → ℝ
  measurableSet_resp : ∀ a P, MeasurableSet {ω | resp a ω = P}
  measurable_tok : ∀ a, Measurable (tok a)
  measurable_lat : ∀ a, Measurable (lat a)

namespace OneTurnBatch

variable {ζ : Fin k → ℕ} {Ω : Type*} [MeasurableSpace Ω] (B : OneTurnBatch ι ζ Ω)

/-- The responses in processing order. -/
def respList (ω : Ω) : List (Finset ι) := List.ofFn fun j => B.resp (B.order j) ω

/-- The **history-conditional guarantee** of §5 (PDF p. 9) with parameter `p`: for every position
`j` of the processing order, whose call is to oracle `i`, every `e ∈ V_i`, and every history `h`
of earlier processed responses of positive probability whose residual (after the PTM's retention
rule) contains `e`, the call's partial cover satisfies the local dual-certification condition for
that residual and covers `e` with conditional probability at least `p` (multiplicative form
`ℙ(E ∩ H) ≥ p ℙ(H)`). -/
def HistoryGuarantee (W : WSCInstance U ι) (ρ : ℝ) (y : U → ℝ) (V : Fin k → Finset U)
    (p : ℝ) (μ : Measure Ω) : Prop :=
  ∀ (j : Fin (∑ i, ζ i)) (e : U), e ∈ V (B.order j).1 →
    ∀ h : List (Finset ι),
      0 < μ {ω | (B.respList ω).take j = h} →
      e ∈ W.residual (W.retained ρ y h) →
      ENNReal.ofReal p * μ {ω | (B.respList ω).take j = h} ≤
        μ ({ω | (B.respList ω).take j = h} ∩
          {ω | W.LocalDualCert ρ y (B.resp (B.order j) ω) (W.residual (W.retained ρ y h)) ∧
            e ∈ W.covered (B.resp (B.order j) ω)})

/-- The event that the one-turn batch returns a certified `ρ`-cover by `D` (PDF p. 10): the
partial covers retained by processing the responses in order (retaining each one exactly when it
satisfies the local dual-certification condition for the current residual) form a certified
`ρ`-cover, and every call has finished by `D`. -/
def successEvent (W : WSCInstance U ι) (ρ : ℝ) (y : U → ℝ) (D : ℝ) : Set Ω :=
  {ω | W.CertifiedCover ρ (W.retained ρ y (B.respList ω)) ∧ ∀ a, B.lat a ω ≤ D}

/-- The batch's total token cost `∑_{(i,a)} TOK_{i,a}`. -/
noncomputable def totalTok (ω : Ω) : ℝ := ∑ a, B.tok a ω

end OneTurnBatch

end HSOSetCover.FullCover.Supplement


