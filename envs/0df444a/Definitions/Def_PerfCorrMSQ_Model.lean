-- Prove2me | Definitions.Def_PerfCorrMSQ_Model
-- name    : PerfCorrMSQ_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:02.563276+00:00
-- url     : https://prove2.me/theorems/4a1d60aa-dc58-4b85-8021-520715474cfa
-- title:
--   The model $M/M_{pc}/n+M_{pc}$, $n\ge1$, on one probability space, and the staffing rule (1.1)
-- statement:
--   The sequence of systems on one probability space $(\Omega,\mathcal F,P)$. For each $n$, the primitives of system $n$ (see `PerfCorrMSQ.System`) are random. The model with patience rate $\theta$ and arrival rates $(\lambda_n)$ requires that $P$ is a probability measure and, for every $n\ge1$:
--
--   1. $\lambda_n>0$;
--   2. the initial state is non-idling, $Z^n(0)\le n$ and $Q^n(0)>0\Rightarrow Z^n(0)=n$ (4.2); elapsed waits and remaining phase-1 times are nonnegative, and the elapsed waits are nonincreasing along the queue (FIFO order);
--   3. the initial state is a random variable, with an otherwise arbitrary joint law;
--   4. the fresh draws are independent exponential random variables: interarrival times with rate $\lambda_n$ (Poisson arrivals), the arrivals' service requirements with rate $1$ (patience $T=S/\theta$), the remaining patience of each initial waiting customer with rate $\theta$, the phase-2 time of each initial customer in service with rate $1$;
--   5. the fresh draws are jointly independent of the initial state.
--
--   Nothing is assumed about the dependence between different systems. Further,
--
--   $$
--   \beta_n=\frac{n-\lambda_n}{\sqrt n}\quad(5.1),\qquad\text{and the square-root staffing rule (1.1) is}\quad \beta_n\to\beta .
--   $$
--
--   **Formalization Note** Items 4 (for initial waiting customers) and 5 are readings: the paper states neither but its proofs use both (the time-0 σ-algebra $\mathcal F^n_0$ of §4.1; memorylessness of $T$, (2.1)). (1.1) reads $\sqrt n(1-\rho_n)\to\beta$ with $\rho_n=\lambda_n/n$, which is $\beta_n\to\beta$.
-- source:
--   Yu and Perry, Many-Server Heavy-Traffic Limits for Queueing Systems with Perfectly Correlated Service and Patience Times, arXiv:2008.12890v1, §1 p.3 ((1.1)), §2 pp.4–5, §3.3 p.9, §4.1 p.11, (5.1) p.12

import Mathlib
import Definitions.Def_PerfCorrMSQ_System

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace PerfCorrMSQ

/-!
The sequence of systems `M/M_pc/n + M_pc`, `n ≥ 1`, on one probability space (Yu–Perry,
arXiv:2008.12890v1, §2 pp.4–5, §3.3 p.9), and the square-root staffing rule (1.1).
-/

/-- The **random primitives of every system `n`** on a common sample space `Ω`: for system `n`,
the initial state (`q0 n`, `z0 n`, `ell n`, `r n`) and the fresh draws (`tau n`, `S n`, `Tq n`,
`Sb n`); see `PerfCorrMSQ.Prim`. -/
structure SystemData (Ω : Type*) where
  q0 : ℕ → Ω → ℕ
  z0 : ℕ → Ω → ℕ
  ell : ℕ → Ω → ℕ → ℝ
  r : ℕ → Ω → ℕ → ℝ
  tau : ℕ → Ω → ℕ → ℝ
  S : ℕ → Ω → ℕ → ℝ
  Tq : ℕ → Ω → ℕ → ℝ
  Sb : ℕ → Ω → ℕ → ℝ

namespace SystemData

variable {Ω : Type*} (sys : SystemData Ω)

/-- The primitives of system `n` on the sample path `ω`. -/
def prim (n : ℕ) (ω : Ω) : Prim :=
  ⟨sys.q0 n ω, sys.z0 n ω, sys.ell n ω, sys.r n ω, sys.tau n ω, sys.S n ω, sys.Tq n ω,
    sys.Sb n ω⟩

/-- The initial state of system `n`: `(Qⁿ(0), Zⁿ(0), (ℓⁿᵢ(0))ᵢ, (rⁿⱼ(0))ⱼ)`. -/
def initData (n : ℕ) (ω : Ω) : ℕ × ℕ × (ℕ → ℝ) × (ℕ → ℝ) :=
  (sys.q0 n ω, sys.z0 n ω, sys.ell n ω, sys.r n ω)

/-- The fresh draws of system `n`, as one family indexed by `Fin 4 × ℕ`: `(0, k)` the
interarrival times `τₖ`, `(1, k)` the arrivals' service requirements `Sₖ`, `(2, i)` the remaining
patience times `Tqᵢ` of the initial waiting customers, `(3, j)` the phase-2 times `Sbⱼ` of the
initial customers in service. -/
def fresh (n : ℕ) (ω : Ω) (i : Fin 4 × ℕ) : ℝ :=
  match i.1 with
  | 0 => sys.tau n ω i.2
  | 1 => sys.S n ω i.2
  | 2 => sys.Tq n ω i.2
  | 3 => sys.Sb n ω i.2

/-- The **rate of the exponential law** of each fresh draw: `λₙ` for interarrival times, `1` for
service requirements and phase-2 times (`µ = 1`), `θ` for the remaining patience of an initial
waiting customer. -/
def freshRate (θ lamn : ℝ) (i : Fin 4 × ℕ) : ℝ :=
  match i.1 with
  | 0 => lamn
  | 1 => 1
  | 2 => θ
  | 3 => 1

end SystemData

/-- **The model** (§2 pp.4–5, §3.3 p.9), for patience rate `θ` and arrival rates `λ`:
`P` is a probability measure, and for every system `n ≥ 1`:
1. `λₙ > 0`;
2. the initial state is non-idling: `Zⁿ(0) ≤ n`, and `Qⁿ(0) > 0` forces `Zⁿ(0) = n` ((4.2));
   elapsed waits `ℓⁿᵢ(0)` and remaining phase-1 times `rⁿⱼ(0)` are nonnegative, and the
   waiting customers are in FIFO order, so the elapsed waits are nonincreasing along the queue
   (`ℓⁿ₁(0) ≥ ℓⁿ₂(0) ≥ ⋯`, the head of the line having waited longest);
3. the initial state is a random variable, with an otherwise arbitrary joint law;
4. the fresh draws are independent exponential random variables: interarrival times with rate
   `λₙ` (Poisson arrivals), arrivals' service requirements `S` with rate `1` (patience
   `T = S/θ`), remaining patience of initial waiting customers with rate `θ`, phase-2 times of
   initial customers in service with rate `1`;
5. the fresh draws are jointly independent of the initial state.

Nothing is assumed about the dependence between different systems `n`.

**Formalization Note.** Item 5 and the law of the remaining patience in item 4 are readings R1
and R2 of the mission: the paper states neither, and its proofs use both (the time-`0`
σ-algebra `Fⁿ₀` of §4.1, p.11; memorylessness of `T` for a customer who has waited `ℓ`, (2.1)). -/
def IsModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : ℝ) (lam : ℕ → ℝ)
    (sys : SystemData Ω) : Prop :=
  IsProbabilityMeasure P ∧
  ∀ n : ℕ, 1 ≤ n →
    0 < lam n ∧
    (∀ ω, sys.z0 n ω ≤ n ∧ (0 < sys.q0 n ω → sys.z0 n ω = n) ∧
      (∀ i < sys.q0 n ω, 0 ≤ sys.ell n ω i) ∧
      (∀ i j, i ≤ j → j < sys.q0 n ω → sys.ell n ω j ≤ sys.ell n ω i) ∧
      (∀ j < sys.z0 n ω, 0 ≤ sys.r n ω j)) ∧
    Measurable (sys.initData n) ∧
    (∀ i, Measurable (fun ω => sys.fresh n ω i)) ∧
    (∀ i, P.map (fun ω => sys.fresh n ω i) = expMeasure (SystemData.freshRate θ (lam n) i)) ∧
    iIndepFun (fun i ω => sys.fresh n ω i) P ∧
    IndepFun (sys.initData n) (sys.fresh n) P

/-- `βₙ = n^{−1/2}(n − λₙ)` (5.1). -/
noncomputable def betaN (lam : ℕ → ℝ) (n : ℕ) : ℝ := ((n : ℝ) - lam n) / Real.sqrt n

/-- The **square-root staffing rule** (1.1) with `µ = 1`: `√n (1 − λₙ/n) = βₙ → β`. -/
def StaffingRule (lam : ℕ → ℝ) (β : ℝ) : Prop := Tendsto (betaN lam) atTop (𝓝 β)

end PerfCorrMSQ


