-- Prove2me | Definitions.Def_NegNetQueue_Meets_Supplement_Exposure
-- name    : NegNetQueue_Meets_Supplement_Exposure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:06:57.155861+00:00
-- url     : https://prove2.me/theorems/48fa4144-4f67-461b-ae53-319a0984eda4
-- title:
--   §5 — independent exponential clocks, person-hour exposure, and the matrices Q, N, D_G
-- statement:
--   Let $\lambda,\mu>0$, let $c\ge1$ be the number of servers and let $n\ge1$ be the waiting-room capacity. The event sequence is the published sequence $\varepsilon$, with true meaning completion. An independent exponential clock family consists of measurable i.i.d. real variables $\tau_t\sim\operatorname{Exp}(\lambda+c\mu)$, independent of the entire event sequence. This uses Mathlib's exponential distribution directly; it does not introduce another exponential law.
--
--   Starting the published tagged-customer dynamics at $(j,k)$, let $J_t,K_t$ denote position and waiting queue length just before event $t$. The total person-hour exposure is
--   $$T_{j,k}=\sum_{t\ge0}\mathbf1_{\{J_t>0\}}(K_t-1)\tau_t.$$
--   Lost arrivals at capacity are included in this sum. Position zero is absorbing and contributes no further exposure. The sum takes values in $[0,\infty]$, without assigning a divergent sum the value zero.
--
--   The transient state space is $S_n=\{(j,k):1\le j\le k\le n\}$. For $k<n$, $Q$ sends $(j,k)$ to $(j,k+1)$ with probability $\lambda/(\lambda+c\mu)$ and, if $j>1$, to $(j-1,k-1)$ with probability $c\mu/(\lambda+c\mu)$. At $k=n$, it sends $(j,n)$ to $(j-1,n-1)$ with probability one for $j>1$, while row $(1,n)$ is zero. Absorption is omitted from $Q$.
--
--   Write $N_{j,k}=(k-1)/(\lambda+c\mu)$ for $k<n$ and $N_{j,n}=(n-1)/(c\mu)$. Set $g_k(\eta)=1/(1+N_{j,k}\log(1/\eta))$ and $D_G(\eta)=\operatorname{diag}(g_k(\eta))$. The actual transform $G_{j,k}(\eta)=E[\eta^{T_{j,k}}]$ is defined by integration of the pathwise exposure, independently of these matrices. These definitions supply the objects of Theorem 4.
--
--   **Formalization Note** Uniformization includes lost arrivals as self-loops with holding time; the independence of the exponential clocks from the event marks implements the competing exponential clocks. Clock nonnegativity holds almost surely from its exponential law; `ofReal` only clips exceptional negative values. At $T=\infty$, $\eta^T=0$ for $\eta<1$ and $1^T=1$. The theorem concludes transform integrability. The p. 11 completion target $(j-1,k)$ is corrected to $(j-1,k-1)$, as in (9), (11), (13) and the published dynamics. No assertion of invertibility, integrability, absorption or any desired identity is part of these definitions.
-- source:
--   Hassin, Meilijson & Perlman, Queueing with Negative Network Effects, SSRN 4097977 (version of July 2, 2022), pp. 11–13, §5, tagged-customer chain and person-hour exposure, (8), (10), (12)

import Mathlib
import Definitions.Def_NegNetQueue_Meets_Model
import Definitions.Def_NegNetQueue_Meets_EventSeq

set_option autoImplicit false
open scoped ENNReal Matrix

namespace NegNetQueue.Meets.Supplement

open MeasureTheory ProbabilityTheory

/-- An independent exponential clock sequence, independent of the entire mark sequence.
The exponential law is Mathlib's `expMeasure`; no moments are assumed. -/
structure IndependentExpClocks {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (rate : ℝ) (ε : ℕ → Ω → Bool) (τ : ℕ → Ω → ℝ) : Prop where
  meas : ∀ t, Measurable (τ t)
  law : ∀ t, Measure.map (τ t) P = expMeasure rate
  indep : iIndepFun τ P
  independent_marks : IndepFun (fun ω t => ε t ω) (fun ω t => τ t ω) P

/-- Uniformized M/M/c/n clocks: lost arrivals are events too. -/
structure IsHoldingSeq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (lam mu : ℝ) (c : ℕ)
    (ε : ℕ → Ω → Bool) (τ : ℕ → Ω → ℝ) : Prop where
  events : IsEventSeq P lam mu c ε
  clocks : IndependentExpClocks P (lam + c * mu) ε τ

/-- The transient states, including n = 1. Absorption is pos = 0 in `run`. -/
abbrev State (n : ℕ) := {p : Fin (n + 1) × Fin (n + 1) //
  1 ≤ p.1.val ∧ p.1.val ≤ p.2.val}

/-- The paper's Q, omitting the absorbing state and skipping lost arrivals.
The completion target is (j-1,k-1), correcting the prose typo on p. 11. -/
noncomputable def Q (n : ℕ) (lam mu : ℝ) (c : ℕ) : Matrix (State n) (State n) ℝ :=
  fun s u =>
    if s.1.2.val = n then
      if 2 ≤ s.1.1.val ∧ u.1.1.val = s.1.1.val - 1 ∧ u.1.2.val = n - 1 then 1 else 0
    else
      (if u.1.1.val = s.1.1.val ∧ u.1.2.val = s.1.2.val + 1 then
        lam / (lam + c * mu) else 0) +
      (if 2 ≤ s.1.1.val ∧ u.1.1.val = s.1.1.val - 1 ∧
          u.1.2.val = s.1.2.val - 1 then qComp lam mu c else 0)

/-- Mean person-hour contribution in one sojourn of the embedded chain. -/
noncomputable def localMean (n : ℕ) (lam mu : ℝ) (c k : ℕ) : ℝ :=
  if k = n then ((n : ℝ) - 1) / (c * mu)
  else ((k : ℝ) - 1) / (lam + c * mu)

/-- The vector N in (8). -/
noncomputable def N (n : ℕ) (lam mu : ℝ) (c : ℕ) : State n → ℝ :=
  fun s => localMean n lam mu c s.1.2.val

/-- The local transform in (10), including its zero-exposure value 1 at k = 1. -/
noncomputable def localGF (n : ℕ) (lam mu : ℝ) (c : ℕ) (η : ℝ) (k : ℕ) : ℝ :=
  1 / (1 + localMean n lam mu c k * Real.log (1 / η))

/-- D_G in (12). -/
noncomputable def DG (n : ℕ) (lam mu : ℝ) (c : ℕ) (η : ℝ) :
    Matrix (State n) (State n) ℝ :=
  Matrix.diagonal (fun s => localGF n lam mu c η s.1.2.val)

/-- Pathwise person-hours. Every pre-absorption event interval counts, including lost arrivals.
The extended nonnegative sum retains divergent trajectories as infinity. -/
noncomputable def exposure {Ω : Type*} (n j k : ℕ)
    (ε : ℕ → Ω → Bool) (τ : ℕ → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∑' t : ℕ,
    let s := run n ⟨j, k, 0, 0⟩ (fun t => ε t ω) t
    if s.pos = 0 then 0 else (s.len - 1 : ℕ) * ENNReal.ofReal (τ t ω)

/-- η^T; the value at infinity is 0 for η < 1 and 1 for η = 1.
Only 0 < η ≤ 1 is asserted in the theorem. -/
noncomputable def survivalPower (η : ℝ) (T : ℝ≥0∞) : ℝ :=
  if T = ⊤ then (if η = 1 then 1 else 0) else η ^ T.toReal

/-- The actual expectation, not the matrix expression. Integrability is a conclusion. -/
noncomputable def totalGF {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n j k : ℕ) (ε : ℕ → Ω → Bool) (τ : ℕ → Ω → ℝ) (η : ℝ) : ℝ :=
  ∫ ω, survivalPower η (exposure n j k ε τ ω) ∂P

/-- The vector of actual transforms. -/
noncomputable def GFvec {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n : ℕ) (ε : ℕ → Ω → Bool) (τ : ℕ → Ω → ℝ) (η : ℝ) : State n → ℝ :=
  fun s => totalGF P n s.1.1.val s.1.2.val ε τ η

end NegNetQueue.Meets.Supplement


