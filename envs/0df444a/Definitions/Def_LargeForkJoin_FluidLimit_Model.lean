-- Prove2me | Definitions.Def_LargeForkJoin_FluidLimit_Model
-- name    : LargeForkJoin_FluidLimit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:27.552984+00:00
-- url     : https://prove2.me/theorems/81965b4c-3a0f-4854-98ac-f54b5ef93913
-- title:
--   Definitions 2.1–2.3, 4.1, (2.1), (2.3), (2.5)–(2.7), Assumptions 2.1–2.5 — N-server fork-join queue with Bernoulli arrivals/services, maximum queue length, fluid limit q(t)
-- statement:
--   This file sets up the nearly deterministic fork-join queue of Schol, Vlasiou and Zwart and every quantity its fluid limit refers to.
--
--   **Primitives.** For each number of servers $N$ there are arrival indicators $X^{(N)}(j)\in\{0,1\}$ and service indicators $Y_i^{(N)}(j)\in\{0,1\}$ for slots $j\ge1$ and servers $i$, with
--   $$
--   \mathbb P(X^{(N)}(j)=1)=p^{(N)}=1-\frac{\alpha}{N}-\frac{\beta}{N^2},\qquad \mathbb P(Y_i^{(N)}(j)=1)=q^{(N)}=1-\frac{\alpha}{N},\qquad \alpha,\beta>0 .
--   $$
--   Every server receives the same arrivals. The counting processes are $A^{(N)}(n)=\sum_{j=1}^{n}X^{(N)}(j)$ (Definition 2.1) and $S_i^{(N)}(n)=\sum_{j=1}^{n}Y_i^{(N)}(j)$ (Definition 2.2). The initial queue length of server $i$ is $Q_i^{(N)}(0)=\lfloor r_N U_i\rfloor$, where $U_1,U_2,\dots$ are i.i.d. random variables, the initial queue lengths are non-negative, and $r_N\ge0$ is a scaling sequence (Assumptions 2.2–2.3).
--
--   **Maximum queue length.** By Lindley's recursion the queue of server $i$ at time $n$ is
--   $$
--   Q_i^{(N)}(n)=\max\Big(\sup_{0\le k\le n}\big[(A^{(N)}(n)-A^{(N)}(k))-(S_i^{(N)}(n)-S_i^{(N)}(k))\big],\;Q_i^{(N)}(0)+A^{(N)}(n)-S_i^{(N)}(n)\Big),
--   $$
--   and $Q^{(N)}_{(\alpha,\beta)}(n)=\max_{i\le N}Q_i^{(N)}(n)$ is the maximum queue length (2.3). Dropping the second term gives the maximum queue length of the system started empty (2.1). The file also defines $Q^{(N)}_{(\alpha,\beta)}(0)=\max_{i\le N}Q_i^{(N)}(0)$ and the second part $\max_{i\le N}(A^{(N)}(n)-S_i^{(N)}(n)+Q_i^{(N)}(0))$ of (2.3), the time $\lfloor tN^3\log N\rfloor$ and the spatial scale $N\log N$.
--
--   **Assumptions.** Assumption 2.3: $Q^{(N)}_{(\alpha,\beta)}(0)/(N\log N)\to q(0)\ge0$ in probability. Assumption 2.4: $U_i$ has a finite right endpoint. Assumption 2.5: $U_i$ is continuous and $\lim_{t\to\infty}\frac{-\log\mathbb P(U_i>vt)}{-\log\mathbb P(U_i>t)}=h(v)$ for all $v\in[0,1]$.
--
--   **Fluid limit.** With $g$ standing for $t\mapsto g(t,q(0))$,
--   $$
--   q(t)=\max\Big(\big(\sqrt{2\alpha t}-\beta t\big)\mathbb 1\big(t<\tfrac{\alpha}{2\beta^2}\big)+\tfrac{\alpha}{2\beta}\mathbb 1\big(t\ge\tfrac{\alpha}{2\beta^2}\big),\;g(t,q(0))-\beta t\Big),
--   $$
--   where $g(t,q(0))=q(0)+\sqrt{2\alpha t}$ under Assumption 2.4 (2.6) and $g(t,q(0))=\sup\{\sqrt{2\alpha t}\,u+q(0)v : u^2+h(v)\le1,\ 0\le u\le1,\ 0\le v\le1\}$ under Assumption 2.5 (2.7).
--
--   **Section 4 quantities (Definition 4.1).** $\tilde A^{(N)}(n)=A^{(N)}(n)/N-(1-\alpha/N)n/N$, $\tilde S_i^{(N)}(n)=-S_i^{(N)}(n)/N+(1-\alpha/N)n/N$, $\tilde R_i^{(N)}(n)=(\tilde A^{(N)}(n)+\tilde S_i^{(N)}(n))/\log N$ and the standardized service process $M_i^{(N)}(t)=\frac{\tilde S_i^{(N)}(tN^3\log N)}{\sqrt{\alpha t(1-\alpha/N)\log N}}\frac{\sqrt{tN^3\log N}}{\sqrt{\lfloor tN^3\log N\rfloor}}$. Finally, for Lemmas 4.4 and 4.9, the law of $N$ independent pairs $(X_i,U_i)$ with $X_i$ standard normal and $U_i$ distributed as $U_1$, and the function $\max_{i\le N}\big(\sqrt{\alpha t}X_i/\sqrt{\log N}+\lfloor r_NU_i\rfloor/(N\log N)\big)$ of such a sample.
--
--   These are the objects of Theorem 2.1 and of every lemma of Section 4.
--
--   **Formalization Note** The model hypothesis bundles Assumption 2.1 ($\alpha,\beta>0$), the Bernoulli laws of Definitions 2.1–2.2, Assumption 2.2 and measurability. Three conventions are added and disclosed: the Bernoulli laws are imposed only for $N\ge N_0$ (for small $N$ the number $p^{(N)}$ may be negative); within each $N\ge N_0$ the arrival indicators, the service indicators and the initial-condition variables $U_i$ are mutually independent (the paper never states that $(U_i)$ is independent of arrivals and services, but its proofs use it); servers are indexed $0,\dots,N-1$ instead of $1,\dots,N$. Assumption 2.5 adds that $\mathbb P(U_i>t)>0$ for every $t$ (an infinite right endpoint): the ratio in Assumption 2.5 is only meaningful then, and without it Lean's convention $\log 0=0$ would let bounded variables satisfy the condition. "Continuous" is encoded as "no atoms". Because the $U_i$ are identically distributed, Assumptions 2.4 and 2.5 are stated for $U_1$ (index $0$ in Lean). The indicator form of (2.5) is written as an `if` on $t<\alpha/(2\beta^2)$. The supremum (2.7) is a real `sSup`; its set is nonempty and bounded because $0\le u,v\le1$. The paper's real time arguments enter only through $\lfloor tN^3\log N\rfloor$, as in the paper.
-- source:
--   Schol, Vlasiou & Zwart, Large fork-join queues with nearly deterministic arrival and service times, arXiv:1912.11661v3, pp. 5–8, Definitions 2.1–2.3, (2.1), (2.3), Assumptions 2.1–2.5, Theorem 2.1 (2.5)–(2.7); pp. 15–16, Definition 4.1 (4.1)–(4.4); p. 17, Lemma 4.4 and p. 23, Lemma 4.9 (Gaussian pairs)

import Mathlib

namespace LargeForkJoin.FluidLimit

open MeasureTheory ProbabilityTheory Filter Topology

/-- `p^(N) = 1 - α/N - β/N²`, the arrival probability per slot (Definition 2.3, Assumption 2.1). -/
noncomputable def pArr (α β : ℝ) (N : ℕ) : ℝ := 1 - α / N - β / (N : ℝ) ^ 2

/-- `q^(N) = 1 - α/N`, the service probability per slot (Definition 2.3, Assumption 2.1). -/
noncomputable def qSrv (α : ℝ) (N : ℕ) : ℝ := 1 - α / N

/-- The primitive random data of the sequence of fork-join systems on one probability space:
`X N j` is the arrival indicator of slot `j` in the `N`-th system, `Y N i j` the service indicator
of server `i` (0-based) in slot `j`, `U i` the initial-condition variable of server `i`
(independent of `N`), and `r N` the scaling sequence `r_N` of Assumption 2.3. -/
structure ForkJoin (Ω : Type*) where
  X : ℕ → ℕ → Ω → ℝ
  Y : ℕ → ℕ → ℕ → Ω → ℝ
  U : ℕ → Ω → ℝ
  r : ℕ → ℝ

variable {Ω : Type*}

/-- `A^(N)(n) = Σ_{j=1}^{n} X^(N)(j)` (Definition 2.1). -/
def arr (M : ForkJoin Ω) (N n : ℕ) (ω : Ω) : ℝ := ∑ j ∈ Finset.Icc 1 n, M.X N j ω

/-- `S_i^(N)(n) = Σ_{j=1}^{n} Y_i^(N)(j)` (Definition 2.2). -/
def srv (M : ForkJoin Ω) (N i n : ℕ) (ω : Ω) : ℝ := ∑ j ∈ Finset.Icc 1 n, M.Y N i j ω

/-- `Q_i^(N)(0) = ⌊r_N U_i⌋` (Assumption 2.3). -/
noncomputable def initLen (M : ForkJoin Ω) (N i : ℕ) (ω : Ω) : ℝ := (⌊M.r N * M.U i ω⌋ : ℝ)

/-- Queue length of server `i` at time `n` when it starts empty:
`sup_{0≤k≤n} [(A(n) - A(k)) - (S_i(n) - S_i(k))]` (the per-server term of (2.1)). -/
def queueEmpty (M : ForkJoin Ω) (N i n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun k => (arr M N n ω - arr M N k ω) - (srv M N i n ω - srv M N i k ω))

/-- Queue length of server `i` at time `n` with initial content `Q_i(0)` (the per-server term of (2.3)). -/
noncomputable def queueLen (M : ForkJoin Ω) (N i n : ℕ) (ω : Ω) : ℝ :=
  max (queueEmpty M N i n ω) (initLen M N i ω + arr M N n ω - srv M N i n ω)

/-- `Q^(N)_(α,β)(n)` for the system started empty, (2.1). -/
noncomputable def maxQueueEmpty (M : ForkJoin Ω) (N n : ℕ) (ω : Ω) : ℝ :=
  ⨆ i : Fin N, queueEmpty M N i n ω

/-- `Q^(N)_(α,β)(n)` with initial condition `Q_i^(N)(0) = ⌊r_N U_i⌋`, (2.3). -/
noncomputable def maxQueue (M : ForkJoin Ω) (N n : ℕ) (ω : Ω) : ℝ :=
  ⨆ i : Fin N, queueLen M N i n ω

/-- `Q^(N)_(α,β)(0) = max_{i≤N} Q_i^(N)(0)` (Assumption 2.3). -/
noncomputable def maxInit (M : ForkJoin Ω) (N : ℕ) (ω : Ω) : ℝ :=
  ⨆ i : Fin N, initLen M N i ω

/-- `max_{i≤N} (A^(N)(n) - S_i^(N)(n) + Q_i^(N)(0))`, the second part of (2.3). -/
noncomputable def maxStartPart (M : ForkJoin Ω) (N n : ℕ) (ω : Ω) : ℝ :=
  ⨆ i : Fin N, (arr M N n ω - srv M N i n ω + initLen M N i ω)

/-- The time `⌊t N³ log N⌋`, on which `Q(t N³ log N) = Q(⌊t N³ log N⌋)` is evaluated. -/
noncomputable def tau (N : ℕ) (t : ℝ) : ℕ := ⌊t * (N : ℝ) ^ 3 * Real.log N⌋₊

/-- The spatial scaling `N log N`. -/
noncomputable def scale (N : ℕ) : ℝ := N * Real.log N

/-- The primitive variables used by the `N`-server system: arrivals and services
in slots `j ≥ 1`, and the initial content variables of its `N` servers. -/
def family (M : ForkJoin Ω) (N : ℕ) :
    {j : ℕ // 1 ≤ j} ⊕ (Fin N × {j : ℕ // 1 ≤ j}) ⊕ Fin N → Ω → ℝ :=
  Sum.elim (fun j => M.X N j.1)
    (Sum.elim (fun ij => M.Y N ij.1 ij.2.1) (fun i => M.U i))

/-- The model of §2: Assumption 2.1 (`α, β > 0`), the Bernoulli laws of Definitions 2.1–2.2 for
`N ≥ N₀`, mutual independence of all arrival, service and initial-condition variables within each
`N ≥ N₀` (the independence of `U` from the arrivals and services is an added, disclosed assumption),
measurability, and Assumption 2.2 (initial queue lengths nonnegative and identically distributed,
with `r_N ≥ 0`). -/
def IsModel [MeasurableSpace Ω] (P : Measure Ω) (M : ForkJoin Ω) (α β : ℝ) (N₀ : ℕ) : Prop :=
  0 < α ∧ 0 < β ∧
  (∀ N j, 1 ≤ j → Measurable (M.X N j)) ∧
  (∀ N, ∀ i : Fin N, ∀ j, 1 ≤ j → Measurable (M.Y N i j)) ∧
  (∀ i, Measurable (M.U i)) ∧
  (∀ N, N₀ ≤ N → ∀ j, 1 ≤ j →
      (∀ᵐ ω ∂P, M.X N j ω = 0 ∨ M.X N j ω = 1) ∧
      P {ω | M.X N j ω = 1} = ENNReal.ofReal (pArr α β N)) ∧
  (∀ N, N₀ ≤ N → ∀ i : Fin N, ∀ j, 1 ≤ j →
      (∀ᵐ ω ∂P, M.Y N i j ω = 0 ∨ M.Y N i j ω = 1) ∧
      P {ω | M.Y N i j ω = 1} = ENNReal.ofReal (qSrv α N)) ∧
  (∀ N, N₀ ≤ N → iIndepFun (family M N) P) ∧
  (∀ N, ∀ i : Fin N, ∀ᵐ ω ∂P, 0 ≤ initLen M N i ω) ∧
  (∀ i, IdentDistrib (M.U i) (M.U 0) P P) ∧ (∀ N, 0 ≤ M.r N)

/-- Assumption 2.3: `Q^(N)(0)/(N log N) → q(0)` in probability, with `q(0) ≥ 0`. -/
def Assumption23 [MeasurableSpace Ω] (P : Measure Ω) (M : ForkJoin Ω) (qInit : ℝ) : Prop :=
  0 ≤ qInit ∧ ∀ ε > 0,
    Tendsto (fun N : ℕ => P {ω | ε < |maxInit M N ω / scale N - qInit|}) atTop (𝓝 0)

/-- Assumption 2.4: `U_i` has a finite right endpoint. -/
def Assumption24 [MeasurableSpace Ω] (P : Measure Ω) (M : ForkJoin Ω) : Prop :=
  ∃ C : ℝ, ∀ᵐ ω ∂P, M.U 0 ω ≤ C

/-- Assumption 2.5: `U_i` is continuous (no atoms), has an infinite right endpoint (added: the
ratio below is only meaningful when `P(U_i > t) > 0` for all `t`), and
`lim_{t→∞} -log P(U_i > v t) / -log P(U_i > t) = h(v)` for all `v ∈ [0,1]`. -/
def Assumption25 [MeasurableSpace Ω] (P : Measure Ω) (M : ForkJoin Ω) (h : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, P {ω | M.U 0 ω = x} = 0) ∧
  (∀ t : ℝ, 0 < P {ω | t < M.U 0 ω}) ∧
  ∀ v ∈ Set.Icc (0 : ℝ) 1, Tendsto (fun t : ℝ =>
      -Real.log (P {ω | v * t < M.U 0 ω}).toReal / -Real.log (P {ω | t < M.U 0 ω}).toReal)
      atTop (𝓝 (h v))

/-- The fluid limit with empty start, the first argument of the max in (2.5):
`(√(2αt) - βt) 𝟙(t < α/(2β²)) + (α/(2β)) 𝟙(t ≥ α/(2β²))`. -/
noncomputable def fluidEmpty (α β t : ℝ) : ℝ :=
  if t < α / (2 * β ^ 2) then Real.sqrt (2 * α * t) - β * t else α / (2 * β)

/-- `g(t, q(0)) = q(0) + √(2αt)`, (2.6). -/
noncomputable def gFinite (α qInit t : ℝ) : ℝ := qInit + Real.sqrt (2 * α * t)

/-- `g(t, q(0)) = sup {√(2αt) u + q(0) v | u² + h(v) ≤ 1, 0 ≤ u ≤ 1, 0 ≤ v ≤ 1}`, (2.7). -/
noncomputable def gGumbel (α : ℝ) (h : ℝ → ℝ) (qInit t : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ u v : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧ u ^ 2 + h v ≤ 1 ∧
    x = Real.sqrt (2 * α * t) * u + qInit * v}

/-- The fluid limit `q(t) = max(fluidEmpty(t), g(t, q(0)) - βt)`, (2.5); `g` is `t ↦ g(t, q(0))`. -/
noncomputable def fluid (α β : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ := max (fluidEmpty α β t) (g t - β * t)

/-- `Ã^(N)(n) = A^(N)(n)/N - (1 - α/N) n/N`, (4.2). -/
noncomputable def Atil (M : ForkJoin Ω) (α : ℝ) (N n : ℕ) (ω : Ω) : ℝ :=
  arr M N n ω / N - (1 - α / N) * n / N

/-- `S̃_i^(N)(n) = -S_i^(N)(n)/N + (1 - α/N) n/N`, (4.3). -/
noncomputable def Stil (M : ForkJoin Ω) (α : ℝ) (N i n : ℕ) (ω : Ω) : ℝ :=
  -(srv M N i n ω) / N + (1 - α / N) * n / N

/-- `R̃_i^(N)(n) = (Ã^(N)(n) + S̃_i^(N)(n)) / log N`, (4.1). -/
noncomputable def Rtil (M : ForkJoin Ω) (α : ℝ) (N i n : ℕ) (ω : Ω) : ℝ :=
  (Atil M α N n ω + Stil M α N i n ω) / Real.log N

/-- `M_i^(N)(t) = S̃_i^(N)(tN³ log N) / √(αt(1 - α/N) log N) · √(tN³ log N) / √⌊tN³ log N⌋`, (4.4). -/
noncomputable def Mstd (M : ForkJoin Ω) (α : ℝ) (N i : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  Stil M α N i (tau N t) ω / Real.sqrt (α * t * (1 - α / N) * Real.log N) *
    (Real.sqrt (t * (N : ℝ) ^ 3 * Real.log N) / Real.sqrt (tau N t))

/-- The law of the pairs `(X_i, U_i)_{i < N}` used in Lemmas 4.4 and 4.9: `X_i` i.i.d. standard
normal, `U_i` i.i.d. with the law of `U_0` under `P`, all independent. -/
noncomputable def gaussPairLaw [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ForkJoin Ω) (N : ℕ) : Measure (Fin N → ℝ × ℝ) :=
  Measure.pi (fun _ : Fin N => (gaussianReal 0 1).prod (P.map (M.U 0)))

/-- `max_{i≤N} (√(αt) X_i / √(log N) + Q_i^(N)(0)/(N log N))` evaluated at a sample
`w i = (X_i, U_i)`, with `Q_i^(N)(0) = ⌊r_N U_i⌋`. -/
noncomputable def gaussPairMax (M : ForkJoin Ω) (α : ℝ) (N : ℕ) (t : ℝ) (w : Fin N → ℝ × ℝ) : ℝ :=
  ⨆ i : Fin N, (Real.sqrt (α * t) * (w i).1 / Real.sqrt (Real.log N) +
    (⌊M.r N * (w i).2⌋ : ℝ) / scale N)

end LargeForkJoin.FluidLimit


