-- Prove2me | Definitions.Def_AuditEvasion_AuditProcess
-- name    : AuditEvasion_AuditProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:27:48.715983+00:00
-- url     : https://prove2.me/theorems/6aface33-0f7b-40fd-b011-1c5213dbeac9
-- title:
--   §3.1, p.1847 — the law of the audit epochs built from a policy; issue time $T\sim\mathrm{Exp}(\lambda)$
-- statement:
--   Given a policy and a history $H$ with last audit $s$, the probability that no audit occurs in $(s,u]$ is
--
--   $$S_H(u)=\exp\Big(-\int_{(s,u]} q^n_x\,dx\Big)\prod_{x\in(s,u],\ q^m_x>0}(1-q^m_x),$$
--
--   with $S_H(u)=0$ when the cumulative intensity diverges, which is what §3.1's description of impulsive audits (probability $q^m_t$ at the epoch $t$) and intensive audits (probability $q^n_t\Delta t+o(\Delta t)$ in $[t,t+\Delta t)$) gives.
--
--   The audit epochs are built from an i.i.d. sequence $v_0,v_1,\dots$ of uniform variables on $[0,1]$: given the history so far and that no audit has happened in $(s,t)$, the next audit is
--
--   $$\inf\{u\ge t:\ S_H(u)\le v\,S_H(t^-)\}\in[0,\infty],$$
--
--   with $\infty$ ("no further audit") when the set is empty; it has $P(\text{next}>u)=S_H(u)/S_H(t^-)$. Each audit extends the history, and the next one follows the policy at the new history. This yields the audit sequence $\tau_1,\tau_2,\dots$ (with $\tau_0=0$), the same construction started from a state $(H,t)$ (used for the threat utility), and, for an issue time $T$, the number of audits before $T$, the history $H_T$ of these audits, and the first audit $\tau(T)$ at or after $T$.
--
--   The issue time $T$ has the exponential law with rate $\lambda$ and is independent of the audit noise (the policy does not see $T$).
--
--   **Formalization Note** The construction realizes the conditional next-audit laws (an Ionescu–Tulcea construction) pathwise from uniform noise, so the law is computed from the policy rather than assumed. Times are in $[0,\infty]$.
-- source:
--   Wang, de Véricourt, Sun, Audit and Remediation Strategies in the Presence of Evasion Capabilities, Oper. Res. 72(5) (2024), doi:10.1287/opre.2022.0289, §3.1 p.1847, §3.3 p.1848, §3.5 p.1848

import Mathlib
import Definitions.Def_AuditEvasion_Model

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section
open Classical

namespace AuditEvasion

/-- The probability `exp(-∫_A q^n)` that no intensive audit happens in `A` on the phase after
the history `H` (§3.1, p.1847), `0` when the cumulative intensity `∫_A q^n` diverges. -/
def noIntensive (π : Policy) (n : ℕ) (H : Fin n → ℝ) (A : Set ℝ) : ℝ :=
  let I : ℝ≥0∞ := ∫⁻ x in A, ENNReal.ofReal (π.qn n H x)
  if I = ⊤ then 0 else Real.exp (-I.toReal)

/-- Survival function of the next audit on the phase after the history `H` (last epoch
`s = lastEpoch n H`): the probability that no audit happens in `(s, u]`,
`S_H(u) = exp(-∫_{(s,u]} q^n) · ∏_{x ∈ (s,u], q^m_x > 0} (1 - q^m_x)` (§3.1, p.1847). -/
def survClosed (π : Policy) (n : ℕ) (H : Fin n → ℝ) (u : ℝ) : ℝ :=
  noIntensive π n H (Ioc (lastEpoch n H) u) *
    ∏ᶠ x ∈ {x | x ∈ Ioc (lastEpoch n H) u ∧ 0 < π.qm n H x}, (1 - π.qm n H x)

/-- The probability that no audit happens in `(s, u)` on the phase after the history `H`
(the left limit `S_H(u-)` of `survClosed`). -/
def survOpen (π : Policy) (n : ℕ) (H : Fin n → ℝ) (u : ℝ) : ℝ :=
  noIntensive π n H (Ioo (lastEpoch n H) u) *
    ∏ᶠ x ∈ {x | x ∈ Ioo (lastEpoch n H) u ∧ 0 < π.qm n H x}, (1 - π.qm n H x)

/-- The next audit time on the phase after the history `H`, given that no audit happened in
`(lastEpoch n H, t)`, sampled from a uniform variable `v ∈ [0,1]` by inversion:
`inf {u ≥ t | S_H(u) ≤ v · S_H(t-)}`, with `⊤` ("no further audit") when the set is empty.
For `v` uniform on `[0,1]` it has `P(next > u) = S_H(u) / S_H(t-)` for `u ≥ t`. -/
def nextAudit (π : Policy) (n : ℕ) (H : Fin n → ℝ) (t v : ℝ) : ℝ≥0∞ :=
  sInf (ENNReal.ofReal '' {u : ℝ | t ≤ u ∧ survClosed π n H u ≤ v * survOpen π n H t})

/-- The audits that follow a history `H` when time has reached `t` with no audit in
`(lastEpoch n H, t)`: `futureEpochs π n H t v m` is the vector of the next `m` audit epochs
(`⊤` = no further audit, absorbing). Audit `m` is sampled by `nextAudit` from the uniform
`v m`, on the phase of the history `H` extended by the audits already drawn. -/
def futureEpochs (π : Policy) (n : ℕ) (H : Fin n → ℝ) (t : ℝ) (v : ℕ → unitInterval) :
    (m : ℕ) → Fin m → ℝ≥0∞
  | 0 => Fin.elim0
  | m + 1 =>
    let A := futureEpochs π n H t v m
    let H' : Fin (n + m) → ℝ := Fin.append H fun i => (A i).toReal
    Fin.snoc (α := fun _ => ℝ≥0∞) A
      (if ∃ i, A i = ⊤ then ⊤
       else nextAudit π (n + m) H' (if m = 0 then t else lastEpoch (n + m) H') (v m))

/-- The `i`-th audit (`i = 0, 1, …`) after the state `(H, t)`; see `futureEpochs`. -/
def auditFrom (π : Policy) (n : ℕ) (H : Fin n → ℝ) (t : ℝ) (v : ℕ → unitInterval) (i : ℕ) :
    ℝ≥0∞ :=
  futureEpochs π n H t v (i + 1) (Fin.last i)

/-- The audit epochs of the policy `π` from time `0`, as a function of the audit noise `v`:
`audits π v i = τ_{i+1}` (`⊤` = no further audit). -/
def audits (π : Policy) (v : ℕ → unitInterval) (i : ℕ) : ℝ≥0∞ :=
  auditFrom π 0 ![] 0 v i

/-- The audit epochs indexed as in the paper: `epoch π v 0 = τ₀ = 0` and
`epoch π v (i + 1) = τ_{i+1}` (Theorem 2, p.1850). -/
def epoch (π : Policy) (v : ℕ → unitInterval) : ℕ → ℝ≥0∞
  | 0 => 0
  | i + 1 => audits π v i

/-- The audit noise: an i.i.d. sequence of uniform variables on `[0,1]`. -/
def auditNoise : Measure (ℕ → unitInterval) :=
  Measure.infinitePi fun _ => volume

/-- The joint law of the issue time `T ~ Exp(λ)` (p.1846) and of the audit noise, independent
of each other (the policy cannot see `T`). -/
def issueAuditLaw (p : Params) : Measure (ℝ × (ℕ → unitInterval)) :=
  (expMeasure p.lam).prod auditNoise

/-- The number `n` of audits strictly before the issue time `T`. -/
def stageAt (π : Policy) (v : ℕ → unitInterval) (T : ℝ) : ℕ :=
  sInf {i | ENNReal.ofReal T ≤ audits π v i}

/-- The public history `H_T = (τ₁, …, τₙ)` of the audits strictly before `T`. -/
def histAt (π : Policy) (v : ℕ → unitInterval) (T : ℝ) : Fin (stageAt π v T) → ℝ :=
  fun i => (audits π v i).toReal

/-- `τ(T)`, the first audit at or after the issue time `T` (§3.5, p.1848). -/
def firstAuditAfter (π : Policy) (v : ℕ → unitInterval) (T : ℝ) : ℝ≥0∞ :=
  audits π v (stageAt π v T)

end AuditEvasion


