-- Prove2me | Definitions.Def_RedundancyStab_IID_Model
-- name    : RedundancyStab_IID_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:13:34.434303+00:00
-- url     : https://prove2.me/theorems/08ee536b-e4ef-4abb-8c54-f83b0de0b1e6
-- title:
--   §3, pp. 4–6 — the redundancy-d model: types C and C(s), copies M_s, and the PS chain with i.i.d. copies, rates (1)
-- statement:
--   The **redundancy-$d$ model** has $K$ homogeneous servers $S=\{1,\dots,K\}$, each of capacity $1$. Jobs arrive according to a Poisson process of rate $\lambda$; an arriving job chooses $d$ of the $K$ servers uniformly at random and sends one copy to each. The $d$ copies of a job have i.i.d. exponential service requirements with mean $1/\mu$, and when one copy completes, the other copies of that job are removed at once (cancel-on-complete).
--
--   1. **Types.** A job's type is the set $c\subseteq S$ of its $d$ servers. The set of all types is $C=\{c\subseteq S : |c|=d\}$, so $|C|=\binom{K}{d}$, and $C(s)=\{c\in C : s\in c\}$ is the set of types with a copy at server $s$.
--   2. **State and copies.** $N_c$ is the number of type-$c$ jobs, $\vec N=(N_c)_{c\in C}\in\mathbb N^{C}$, and
--   $$M_s=\sum_{c\in C(s)} N_c$$
--   is the number of copies at server $s$. The same sum $m_s=\sum_{c\in C(s)} n_c$ is defined for a real vector $\vec n\in\mathbb R^{C}$ (the fluid analogue).
--   3. **The Processor Sharing (PS) chain.** Under PS each copy at server $s$ receives capacity $1/M_s$. Since copies are i.i.d. exponential, a type-$c$ job leaves at the first completion of one of its $d$ copies, so $\vec N$ is a continuous-time Markov chain on $\mathbb N^{C}$ with transitions
--   $$\vec N\to\vec N+e_c\ \text{ at rate }\ \frac{\lambda}{\binom{K}{d}},\qquad \vec N\to\vec N-e_c\ \text{ at rate }\ \mu\sum_{\tilde s\in c}\frac{N_c}{M_{\tilde s}},$$
--   the second being display (1) of the paper. Its exit rate is $q(\vec N)=\lambda+\mu\sum_{c\in C}\sum_{\tilde s\in c} N_c/M_{\tilde s}$ and its jump matrix sends $\vec N$ to each neighbour with probability (rate)/$q(\vec N)$.
--
--   These objects are the state space and dynamics that Proposition 3 (stability of PS for $\rho<1$) and the drift identity (14) are about.
--
--   **Formalization Note** Server $s$ is the index $s-1$ in `Fin K`; types are the subtype `{c : Finset (Fin K) // c.card = d}`; $\lambda$ is written `lam` (a Lean keyword). Rates are real numbers; `psEventRate` lists the rate of each arrival/departure event, `psRate` is their sum and `psJump` (via the generic `clockStep`) picks event $e$ with probability $r_e/\sum r$ and applies it. A departure with $N_c=0$ has rate $0$ (the quotient $N_c/M_s$ uses Lean's $x/0=0$, which agrees with the paper because $M_s\ge N_c$ for $s\in c$). If some rate were negative or the total rate were $0$ (impossible under $\lambda>0,\ \mu>0,\ 1\le d\le K$), `clockStep` returns the junk self-loop `PMF.pure`. The chain is consumed by the published `ProcessingNetworks.Stability.PositiveRecurrent`.
-- source:
--   Anton, Ayesta, Jonckheere & Verloop, On the stability of redundancy models, arXiv:1903.04414v2, pp. 4–6, §3 (model, types C and C(s), M_s, PS discipline) and display (1)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions

namespace RedundancyStab.IID

open Finset
open scoped ENNReal

/-- The type set `C = {c ⊆ S : |c| = d}` of the redundancy-`d` model with `K` servers
(§3, p. 5). Servers are `Fin K`; the paper's server `s` is the index `s - 1`. -/
abbrev JobType (K d : ℕ) := {c : Finset (Fin K) // c.card = d}

/-- `C(s) = {c ∈ C : s ∈ c}`, the types that have a copy at server `s` (§3, p. 5). -/
def typesAt (K d : ℕ) (s : Fin K) : Finset (JobType K d) :=
  univ.filter (fun c => s ∈ c.1)

/-- `M_s = Σ_{c ∈ C(s)} N_c`, the number of copies at server `s` in the job-count state
`N ∈ ℕ^C` (§3, p. 5). -/
def copies (K d : ℕ) (n : JobType K d → ℕ) (s : Fin K) : ℕ :=
  ∑ c ∈ typesAt K d s, n c

/-- The fluid analogue `m_s = Σ_{c ∈ C(s)} n_c` for a real vector `n ∈ ℝ^C`
(proofs of Lemma 2 and Proposition 3, pp. 26–27). -/
def fluidCopies (K d : ℕ) (n : JobType K d → ℝ) (s : Fin K) : ℝ :=
  ∑ c ∈ typesAt K d s, n c

/-- The state space `ℕ^C` of the job-count process `N = (N_c)_{c ∈ C}` (§3, p. 5). -/
abbrev PSState (K d : ℕ) := JobType K d → ℕ

/-- Events of the PS chain: `Sum.inl c` = arrival of a type-`c` job, `Sum.inr c` = departure of
a type-`c` job. -/
abbrev PSEvent (K d : ℕ) := JobType K d ⊕ JobType K d

/-- Rate of each event of the PS chain with i.i.d. `Exp(μ)` copies in state `n`:
a type-`c` arrival at rate `λ / C(K,d)` (§3, p. 5), a type-`c` departure at rate
`μ Σ_{s ∈ c} N_c / M_s` (display (1), p. 6: each of the `N_c` copies at server `s` receives
capacity `1 / M_s`, and a job leaves when its first copy completes). The convention
`N_c / 0 = 0` agrees with the paper since `M_s ≥ N_c` for `s ∈ c`. -/
noncomputable def psEventRate (K d : ℕ) (lam μ : ℝ) (n : PSState K d) : PSEvent K d → ℝ
  | Sum.inl _ => lam / (K.choose d : ℝ)
  | Sum.inr c => μ * ∑ s ∈ c.1, (n c : ℝ) / (copies K d n s : ℝ)

/-- The exit rate of state `n` of the PS chain: the sum of all event rates,
`λ + μ Σ_c Σ_{s ∈ c} N_c / M_s` when `d ≤ K`. -/
noncomputable def psRate (K d : ℕ) (lam μ : ℝ) (n : PSState K d) : ℝ :=
  ∑ e, psEventRate K d lam μ n e

/-- The state reached from `n` by an event: `n + e_c` for an arrival, `n - e_c` for a
departure (a departure of type `c` has rate `0` when `N_c = 0`). -/
def psApply (K d : ℕ) (n : PSState K d) : PSEvent K d → PSState K d
  | Sum.inl c => Function.update n c (n c + 1)
  | Sum.inr c => Function.update n c (n c - 1)

/-- The weights `rate / total` of a finite family of nonnegative rates with positive total sum
to one. -/
theorem sum_ofReal_div_total {ι : Type*} [Fintype ι] (r : ι → ℝ) (h0 : ∀ i, 0 ≤ r i)
    (hpos : 0 < ∑ i, r i) : ∑ i, ENNReal.ofReal (r i / ∑ j, r j) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (h0 i) hpos.le), ← Finset.sum_div,
    div_self hpos.ne', ENNReal.ofReal_one]

open Classical in
/-- One step of a jump chain driven by a finite family of competing exponential clocks: event
`i` (rate `r i`) fires first with probability `r i / Σ_j r j`, and the chain then moves
according to `next i`. Junk value `PMF.pure x` (a self-loop) when some rate is negative or the
total rate is not positive; under the paper's hypotheses `λ > 0`, `μ > 0`, `1 ≤ d ≤ K` this
branch is never taken. -/
noncomputable def clockStep {ι X : Type*} [Fintype ι] (r : ι → ℝ) (next : ι → PMF X) (x : X) :
    PMF X :=
  if h : (∀ i, 0 ≤ r i) ∧ 0 < ∑ i, r i then
    (PMF.ofFintype (fun i => ENNReal.ofReal (r i / ∑ j, r j))
      (sum_ofReal_div_total r h.1 h.2)).bind next
  else PMF.pure x

/-- The jump matrix of the PS chain with i.i.d. copies: from `n`, the next event is `e` with
probability `psEventRate e / psRate n`, and the chain moves to `psApply n e`. -/
noncomputable def psJump (K d : ℕ) (lam μ : ℝ) (n : PSState K d) : PMF (PSState K d) :=
  clockStep (psEventRate K d lam μ n) (fun e => PMF.pure (psApply K d n e)) n

end RedundancyStab.IID


