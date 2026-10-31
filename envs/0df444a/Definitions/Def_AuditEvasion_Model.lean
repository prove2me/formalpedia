-- Prove2me | Definitions.Def_AuditEvasion_Model
-- name    : AuditEvasion_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:27:12.587928+00:00
-- url     : https://prove2.me/theorems/726b8143-df8c-4388-a9b8-ed4e72ae9f24
-- title:
--   §3, pp.1846–1849 — parameters, public histories, history-adapted audit and payment policies
-- statement:
--   The model of Wang, de Véricourt and Sun is a principal–agent relationship in continuous time. An adverse issue occurs at a random time $T$, exponentially distributed with rate $\lambda>0$, and is privately known to the agent. Future costs are discounted at rate $\theta>0$. The principal can audit at cost $k$; the agent can evade audits at cost $h>0$, after which an audit detects the issue with probability $\beta\in[0,1)$; remediation costs $r$; the maximal fine is $F$. The paper assumes $h\le r$ (1) and $h\le F$ (p.1847).
--
--   The module records:
--
--   1. the parameters $(\lambda,\theta,k,h,F,r,\beta)$ as one record;
--   2. **public histories**: once time reaches $t$ with no disclosure, the public history is the list of past audit epochs $0<\tau_1<\dots<\tau_n$ (§3.3); its last epoch is $\tau_n$, with $\tau_0=0$ for the empty history;
--   3. **policies** $(P,Q)$ of problem (11): for every history $H=(\tau_1,\dots,\tau_n)$, a disclosure payment $P_t$, an impulsive-audit probability $q^m_t$ and an intensive-audit rate $q^n_t$, used on the phase $(\tau_n,\tau_{n+1}]$ until the next audit;
--   4. **well-formed** policies (§3.1): $q^m_t\in[0,1]$ with finitely many epochs $q^m_t>0$ in every bounded interval after the last audit, $q^n_t\ge0$ integrable on some interval just after the last audit (its cumulative intensity may diverge later, and then an audit has happened by that time), and all three functions jointly Borel measurable in the history and the time.
--
--   **Formalization Note** The paper's rigorous policy class is in its Online Appendix A, which is not used. Integrability and measurability are the added technical conditions. The damage rate $c$ and $r<c/\theta$ do not enter problem (11) and are omitted. The standing assumptions are stated as hypotheses of each theorem.
-- source:
--   Wang, de Véricourt, Sun, Audit and Remediation Strategies in the Presence of Evasion Capabilities, Oper. Res. 72(5) (2024), doi:10.1287/opre.2022.0289, §3.1–§3.3 pp.1847–1848, (1)–(2) p.1847, §4 p.1849

import Mathlib

open MeasureTheory Set

namespace AuditEvasion

/-- The primitive data of the audit–evasion model of Wang, de Véricourt and Sun, *Audit and
Remediation Strategies in the Presence of Evasion Capabilities*, Oper. Res. 72(5) (2024), §3,
pp.1846–1848: the rate `lam` (λ) of the exponential issue time `T`, the discount rate `theta`
(θ), the audit cost `k`, the evasion cost `h`, the maximal penalty `F`, the remedial cost `r`,
and the post-evasion detection probability `beta` (β).

**Formalization Note** The standing assumptions (λ > 0, θ > 0, h > 0, β ∈ [0,1), h ≤ r (1),
h ≤ F, p.1847) are not bundled here; every theorem states the ones it uses as hypotheses. The
damage rate `c` and the assumption `r < c/θ` (p.1847) do not enter problem (11) and are omitted. -/
structure Params where
  /-- Rate λ of the exponential issue time `T` (p.1846). -/
  lam : ℝ
  /-- Discount rate θ (p.1847). -/
  theta : ℝ
  /-- Cost `k` of one audit (§3.1, p.1847). -/
  k : ℝ
  /-- Cost `h` of the evasive effort (§3.1, p.1847). -/
  h : ℝ
  /-- Maximal penalty `F` (§3.2, p.1847). -/
  F : ℝ
  /-- Remedial cost `r` (p.1847). -/
  r : ℝ
  /-- Probability β that an audit reveals the issue after an evasive effort (§3.1, p.1847). -/
  beta : ℝ

/-- The last audit epoch of a public history `H = (τ₁, …, τₙ)` (§3.3, p.1848), with `τ₀ = 0`
for the empty history (Theorem 2, p.1850: "with τ0 = 0"). -/
def lastEpoch : (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, H => H (Fin.last n)

/-- A public history (§3.3, p.1848: "the public history I_t simply corresponds to all the audits'
time epochs that have been run thus far") is a finite list of audit epochs
`0 < τ₁ < τ₂ < … < τₙ`, encoded as a strictly increasing `H : Fin n → ℝ` with positive values. -/
def ValidHist (n : ℕ) (H : Fin n → ℝ) : Prop :=
  StrictMono H ∧ ∀ i, 0 < H i

/-- A (prompt-disclosure) policy `(P, Q) = (P_t, Q_t)` of problem (11) (p.1849: "We thus refer to
a policy P in the following as a pair (P,Q) = (P_t,Q_t)… and take F_t = F for all t"), adapted
to the public history (§3.3, p.1848). For every history `H = (τ₁,…,τₙ)` it specifies, on the
phase `(τₙ, τₙ₊₁]` that lasts until the next audit:
* `pay n H t`, the disclosure payment `P_t` (§3.2, p.1847);
* `qm n H t`, the probability `q^m_t` of an impulsive audit at the epoch `t` (§3.1, p.1847);
* `qn n H t`, the rate `q^n_t` of intensive audits at time `t` (§3.1, p.1847).

**Formalization Note** The payment at time `t` is the one of the history of audits strictly
before `t` (Figure 1, p.1848: the agent acts, then the audit takes place). Only the values for
`t > τₙ` are ever used; the regularity conditions of §3.1 are in `WellFormed`. -/
structure Policy where
  /-- Disclosure payment `P_t` on the phase after the history `H`. -/
  pay : (n : ℕ) → (Fin n → ℝ) → ℝ → ℝ
  /-- Impulsive audit probability `q^m_t` on the phase after the history `H`. -/
  qm : (n : ℕ) → (Fin n → ℝ) → ℝ → ℝ
  /-- Intensive audit rate `q^n_t` on the phase after the history `H`. -/
  qn : (n : ℕ) → (Fin n → ℝ) → ℝ → ℝ

/-- The conditions §3.1 (p.1847) puts on an audit schedule: "An impulsive audit takes place at
time epoch t with probability q^m_t ∈ [0,1], where we require only finitely many impulsive audit
time epochs with q^m_t > 0 within any finite time interval. By contrast, an intensive audit occurs
in time interval [t,t+∆t) with probability q^n_t ∆t + o(∆t), where the audit rate q^n_t ≥ 0."

**Formalization Note** The paper's rigorous policy class is in its Online Appendix A, which is
not used here. Added as encodings: the rate is integrable on some `(τₙ, τₙ + ε]` (so the next
audit comes strictly after the last one; the cumulative intensity may diverge later, at a time
by which an audit has then happened almost surely), and the three functions are jointly Borel
measurable in `(H, t)` (so the expectations of the costs are taken of measurable functions). The
conditions are imposed on every `H`, including lists that are not histories; values there never
enter a cost. -/
structure WellFormed (π : Policy) : Prop where
  qm_mem : ∀ n (H : Fin n → ℝ) t, π.qm n H t ∈ Icc (0 : ℝ) 1
  qm_finite : ∀ n (H : Fin n → ℝ) (b : ℝ),
    {t | t ∈ Ioc (lastEpoch n H) b ∧ 0 < π.qm n H t}.Finite
  qn_nonneg : ∀ n (H : Fin n → ℝ) t, 0 ≤ π.qn n H t
  qn_integrableOn_start : ∀ n (H : Fin n → ℝ), ∃ ε > 0,
    IntegrableOn (π.qn n H) (Ioc (lastEpoch n H) (lastEpoch n H + ε))
  measurable_pay : ∀ n, Measurable fun x : (Fin n → ℝ) × ℝ => π.pay n x.1 x.2
  measurable_qm : ∀ n, Measurable fun x : (Fin n → ℝ) × ℝ => π.qm n x.1 x.2
  measurable_qn : ∀ n, Measurable fun x : (Fin n → ℝ) × ℝ => π.qn n x.1 x.2

end AuditEvasion


