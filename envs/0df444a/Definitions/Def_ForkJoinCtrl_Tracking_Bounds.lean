-- Prove2me | Definitions.Def_ForkJoinCtrl_Tracking_Bounds
-- name    : ForkJoinCtrl_Tracking_Bounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:34.362227+00:00
-- url     : https://prove2.me/theorems/fed881ce-af78-4adc-a20b-f6554c3c2ac8
-- title:
--   Appendix C–D, pp. 20–22 — λ̄, µ̄, λ_, µ_, M^r, C8, the event B^r (42) and the events 𝒜^{(l),r}_in(ε₂) (36)
-- statement:
--   For a horizon $T>0$ (Appendix C):
--
--   1. $\bar\lambda=\max_j\lambda_j$, $\bar\mu=\max_{j, i\in\mathcal I_j}\mu_{ij}$, $\underline\lambda=\min_j\lambda_j$, $\underline\mu=\min_{j,i\in\mathcal I_j}\mu_{ij}$, and $M^r=1+\lceil(1+\bar\mu)Jr^2T\rceil$;
--   2. $C_8=1+\bar\lambda\vee\bar\mu\vee\max_{k}\mu_k$ and the event (42)
--   $$B^r=\Big\{\max_j A^r_j(r^2T)\vee\max_{i,j\in\mathcal J_i}S_{ij}(r^2T)\vee\max_{k}S_k(r^2T)\le\lfloor C_8r^2T\rfloor-1\Big\};$$
--   3. for a run of the proposed policy, $\epsilon_2>0$ and constants $C_5,C_6,C_7$, the events (36a)–(36e): $\mathcal A^{(1),r}_{in}=\{\tau^r_{in}>r^2T\}\cup\{\tau^r_{i(n+1)}-\tau^r_{in}\le\epsilon_2r\}$; $\mathcal A^{(2),r}_{in}$ and $\mathcal A^{(3),r}_{in}$ bound the oscillation of $Q^r_{ij}$ and of $q^{*,r}_{ij}$ over $[\tau^r_{in},\tau^r_{i(n+1)}]$ by $C_5\epsilon_2r$ and $C_6\epsilon_2r$ for all $j\in\mathcal J_i$; $\mathcal A^{(4),r}_{in}$ bounds $|Q^r_{ij}-q^{*,r}_{ij}|$ at $\tau^r_{i(n+1)}$ by $C_7\epsilon_2r$; and $\mathcal A^r_{in}$ is their intersection.
--
--   These quantify that every review period in $[0,r^2T]$ is short, stable and ends near the QP-selected LP solution.
--
--   **Formalization Note** The review epochs live in $[0,\infty]$; the differences in (36a) are taken there and only matter when $\tau^r_{in}$ is finite, where they are exact. The suprema in (36b)–(36c) are written as bounds for every real time in $[\tau^r_{in},\tau^r_{i(n+1)}]$ (all $t\ge\tau^r_{in}$ when $\tau^r_{i(n+1)}=\infty$). The bound in (36d) is imposed when $\tau^r_{i(n+1)}<\infty$; when $\tau^r_{in}\le r^2T$ and $\tau^r_{i(n+1)}=\infty$ the event (36a) fails, so (36e) is unchanged. When there is no dedicated server the maximum in $C_8$ runs over $\bar\lambda,\bar\mu$ only.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, pp. 20–21, Appendix C, (36), (37), M^r; p. 22, Appendix D, (42)

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_Policy

namespace ForkJoinCtrl.Tracking

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Filter Topology

/-!
Özkan, arXiv:2002.01496v1, Appendix C (pp. 20–21) and Appendix D (p. 22): the constants
`λ̄, µ̄, λ_, µ_`, the number `M^r` of review periods, the event `B^r` (42) with `C₈`, and the events
`𝒜^{(l),r}_in(ε₂)` of (36). All of them are for a fixed horizon `T > 0`, and they live on the
unscaled time scale (`r² T`, sizes `ε r`).
-/

variable (N : Network)

theorem Network.univ_nonempty_J : (Finset.univ : Finset (Fin N.J)).Nonempty :=
  ⟨⟨0, N.J_pos⟩, Finset.mem_univ _⟩

/-- The incident pairs `{(i, j) : j ∈ 𝒥, i ∈ ℐ_j}`. -/
def Network.pairs : Finset (Fin N.I × Fin N.J) :=
  Finset.univ.filter (fun p => N.P p.1 p.2 = true)

theorem Network.pairs_nonempty : N.pairs.Nonempty := by
  obtain ⟨i, hi⟩ := N.exists_server ⟨0, N.J_pos⟩
  exact ⟨(i, ⟨0, N.J_pos⟩), by simp [Network.pairs, hi]⟩

/-- `λ̄ := max_{j ∈ 𝒥} λ_j` (p. 20). -/
noncomputable def Network.lamBar : ℝ := Finset.univ.sup' N.univ_nonempty_J N.lam

/-- `µ̄ := max_{j ∈ 𝒥, i ∈ ℐ_j} µ_ij` (p. 20). -/
noncomputable def Network.muBar : ℝ := N.pairs.sup' N.pairs_nonempty (fun p => N.mu p.1 p.2)

/-- `λ_ := min_{j ∈ 𝒥} λ_j` (p. 20). -/
noncomputable def Network.lamMin : ℝ := Finset.univ.inf' N.univ_nonempty_J N.lam

/-- `µ_ := min_{j ∈ 𝒥, i ∈ ℐ_j} µ_ij` (p. 20). -/
noncomputable def Network.muMin : ℝ := N.pairs.inf' N.pairs_nonempty (fun p => N.mu p.1 p.2)

/-- `M^r := 1 + ⌈(1 + µ̄) J r² T⌉` (p. 20). -/
noncomputable def Network.Mr (T : ℝ) (r : ℕ) : ℕ :=
  1 + ⌈(1 + N.muBar) * N.J * (r : ℝ) ^ 2 * T⌉₊

/-- `C₈ := 1 + λ̄ ∨ µ̄ ∨ max_{j ∈ 𝒥, k ∈ 𝒦_j} µ_k` (p. 22), i.e. one plus the largest of `λ̄`, `µ̄` and
the dedicated service rates (only `λ̄, µ̄` enter when there is no dedicated server). -/
noncomputable def Network.C8 : ℝ :=
  1 + (insert N.lamBar (insert N.muBar (Finset.univ.image N.muK))).max' (Finset.insert_nonempty _ _)

variable {N} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The event `B^r` of (42) for the horizon `T`:
`max_j A^r_j(r²T) ∨ max_{i ∈ ℐ, j ∈ 𝒥_i} S_ij(r²T) ∨ max_{j, k ∈ 𝒦_j} S_k(r²T) ≤ ⌊C₈ r² T⌋ − 1`,
written as: each of these counts is at most `⌊C₈ r² T⌋ − 1`. -/
def Model.Bevent (M : Model N Ω P) (T : ℝ) (r : ℕ) : Set Ω :=
  {ω | (∀ j, (M.A r j ω ((r : ℝ) ^ 2 * T) : ℝ) ≤ (⌊N.C8 * (r : ℝ) ^ 2 * T⌋ : ℝ) - 1) ∧
    (∀ i j, N.P i j = true →
      (M.Ss i j ω ((r : ℝ) ^ 2 * T) : ℝ) ≤ (⌊N.C8 * (r : ℝ) ^ 2 * T⌋ : ℝ) - 1) ∧
    (∀ k, (M.S k ω ((r : ℝ) ^ 2 * T) : ℝ) ≤ (⌊N.C8 * (r : ℝ) ^ 2 * T⌋ : ℝ) - 1)}

variable {M : Model N Ω P} {r : ℕ}

/-- `𝒜^{(1),r}_in(ε₂) := {τ^r_in > r²T} ∪ {τ^r_{i(n+1)} − τ^r_in ≤ ε₂ r}` (36a). The difference is
taken in `ℝ₊ ∪ {∞}`; it is only used where `τ^r_in` is finite, where it is the exact difference
(`∞` if `τ^r_{i(n+1)} = ∞`). -/
def PolicyRun.A1 (X : PolicyRun M r) (T ε₂ : ℝ) (i : Fin N.I) (n : ℕ) : Set Ω :=
  {ω | ENNReal.ofReal ((r : ℝ) ^ 2 * T) < X.tau i n ω ∨
    X.tau i (n + 1) ω - X.tau i n ω ≤ ENNReal.ofReal (ε₂ * r)}

/-- `𝒜^{(2),r}_in(ε₂) := {τ^r_in > r²T} ∪ ⋂_{j ∈ 𝒥_i} {sup_{τ^r_in ≤ t ≤ τ^r_{i(n+1)}} |Q^r_ij(t) − Q^r_ij(τ^r_in)| ≤ C₅ ε₂ r}`
(36b); the supremum is over all real `t ≥ 0` in `[τ^r_in, τ^r_{i(n+1)}]` (`[τ^r_in, ∞)` if
`τ^r_{i(n+1)} = ∞`), written as a bound for every such `t`. -/
def PolicyRun.A2 (X : PolicyRun M r) (T C5 ε₂ : ℝ) (i : Fin N.I) (n : ℕ) : Set Ω :=
  {ω | ENNReal.ofReal ((r : ℝ) ^ 2 * T) < X.tau i n ω ∨
    ∀ j ∈ N.Ji i, ∀ t : ℝ, 0 ≤ t → X.tau i n ω ≤ ENNReal.ofReal t →
      ENNReal.ofReal t ≤ X.tau i (n + 1) ω →
      |X.Qij i j ω t - X.Qij i j ω (X.tau i n ω).toReal| ≤ C5 * ε₂ * r}

/-- `𝒜^{(3),r}_in(ε₂) := {τ^r_in > r²T} ∪ ⋂_{j ∈ 𝒥_i} {sup_{τ^r_in ≤ t ≤ τ^r_{i(n+1)}} |q^{*,r}_ij(t) − q^{*,r}_ij(τ^r_in)| ≤ C₆ ε₂ r}`
(36c), with the supremum read as in `A2`. -/
def PolicyRun.A3 (X : PolicyRun M r) (T C6 ε₂ : ℝ) (i : Fin N.I) (n : ℕ) : Set Ω :=
  {ω | ENNReal.ofReal ((r : ℝ) ^ 2 * T) < X.tau i n ω ∨
    ∀ j ∈ N.Ji i, ∀ t : ℝ, 0 ≤ t → X.tau i n ω ≤ ENNReal.ofReal t →
      ENNReal.ofReal t ≤ X.tau i (n + 1) ω →
      |X.qstar i j ω t - X.qstar i j ω (X.tau i n ω).toReal| ≤ C6 * ε₂ * r}

/-- `𝒜^{(4),r}_in(ε₂) := {τ^r_in > r²T} ∪ ⋂_{j ∈ 𝒥_i} {|Q^r_ij(τ^r_{i(n+1)}) − q^{*,r}_ij(τ^r_{i(n+1)})| ≤ C₇ ε₂ r}`
(36d). The bound is imposed when `τ^r_{i(n+1)}` is finite; when `τ^r_{i(n+1)} = ∞` and
`τ^r_in ≤ r²T` the event `𝒜^{(1),r}_in(ε₂)` fails, so the intersection (36e) is unaffected. -/
def PolicyRun.A4 (X : PolicyRun M r) (T C7 ε₂ : ℝ) (i : Fin N.I) (n : ℕ) : Set Ω :=
  {ω | ENNReal.ofReal ((r : ℝ) ^ 2 * T) < X.tau i n ω ∨
    ∀ j ∈ N.Ji i, ∀ e : ℝ, 0 ≤ e → X.tau i (n + 1) ω = ENNReal.ofReal e →
      |X.Qij i j ω e - X.qstar i j ω e| ≤ C7 * ε₂ * r}

/-- `𝒜^r_in(ε₂) := ⋂_{l=1}^4 𝒜^{(l),r}_in(ε₂)` (36e). -/
def PolicyRun.Aev (X : PolicyRun M r) (T C5 C6 C7 ε₂ : ℝ) (i : Fin N.I) (n : ℕ) : Set Ω :=
  X.A1 T ε₂ i n ∩ X.A2 T C5 ε₂ i n ∩ X.A3 T C6 ε₂ i n ∩ X.A4 T C7 ε₂ i n

end ForkJoinCtrl.Tracking


