-- Prove2me | Definitions.Def_BellWilliams2001_ThresholdPolicy_Model
-- name    : BellWilliams2001_ThresholdPolicy_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:57:23.842979+00:00
-- url     : https://prove2.me/theorems/eb590501-e21b-48a5-b4c3-ed6fd2c79cea
-- title:
--   The sequence of parallel server systems: primitives (15), Assumptions 3.1–3.3, scheduling control policies (6)–(14), scalings (16)–(20), (92)–(95), cost (24)
-- statement:
--   **The system.** Two job classes $k=1,2$ arrive to two servers. Server 1 serves class 1 (activity 1); server 2 serves class 1 (activity 2) and class 2 (activity 3). The systems are indexed by $r\to\infty$ through a sequence $r_n\in[1,\infty)$.
--
--   **Primitives.** On a probability space $(\Omega,\mathcal F,\mathbf P)$ there are, for $k=1,2$ and $j=1,2,3$, sequences $\check u_k(i)$, $\check v_j(i)$, $i=1,2,\dots$, not depending on $r$: strictly positive, i.i.d. within each sequence, all mutually independent, with mean one and finite variances $\alpha_k^2$, $\beta_j^2$. In system $r$ the interarrival and service times are (15)
--   $$u_k^r(i)=\check u_k(i)/\lambda_k^r,\qquad v_j^r(i)=\check v_j(i)/\mu_j^r,$$
--   with partial sums $\xi_k^r$, $\eta_j^r$ and renewal processes $A_k^r(t)=\sup\{n\ge0:\xi_k^r(n)\le t\}$, $S_j^r(t)=\sup\{n\ge0:\eta_j^r(n)\le t\}$, assumed finite for every $t\ge0$ everywhere on $\Omega$ (p. 614).
--
--   **Assumptions.** There are $\lambda_1,\lambda_2,\mu_1,\mu_2,\mu_3>0$ and $\theta_1,\theta_2\in\mathbb R$ with (Assumption 3.1) (i) $\lambda_1>\mu_1$, (ii) $1-(\lambda_1-\mu_1)/\mu_2=\lambda_2/\mu_3$, (iii) $\lambda_k^r\to\lambda_k$, (iv) $\mu_j^r\to\mu_j$,
--   $$\text{(v)}\ \ r\mu_2^r\Big(\frac{\lambda_1^r-\mu_1^r}{\mu_2^r}-\frac{\lambda_1-\mu_1}{\mu_2}\Big)\to\theta_1,\qquad \text{(vi)}\ \ r\mu_3^r\Big(\frac{\lambda_2^r}{\mu_3^r}-\frac{\lambda_2}{\mu_3}\Big)\to\theta_2 .$$
--   Holding costs $h_1,h_2>0$, a discount rate $\gamma>0$, Assumption 3.2 $h_1\mu_2\ge h_2\mu_3$, and Assumption 3.3: with $u_k(i)=\check u_k(i)/\lambda_k$, $v_j(i)=\check v_j(i)/\mu_j$, the moment generating functions $\mathbf E e^{lu_k(i)}$, $\mathbf E e^{lv_j(i)}$ are finite for $l$ in a neighbourhood of $0$.
--
--   **Scheduling control policies.** An allocation $T=(T_1,T_2,T_3)$ of system $r$ has idle times $I_1(t)=t-T_1(t)$, $I_2(t)=t-T_2(t)-T_3(t)$ and queue lengths
--   $$Q_1(t)=A_1(t)-S_1(T_1(t))-S_2(T_2(t)),\qquad Q_2(t)=A_2(t)-S_3(T_3(t)).$$
--   It is a scheduling control policy if (11) each $T_j(t)$ is a random variable, (12) each $T_j$ is continuous and nondecreasing with $T_j(0)=0$, (13) each $I_k$ is continuous and nondecreasing with $I_k(0)=0$, and (14) $Q_k(t)\ge0$ for $t\ge0$. Policies may anticipate the future.
--
--   **Scalings and cost.** $\hat Q^r(t)=r^{-1}Q^r(r^2t)$, $\hat I^r(t)=r^{-1}I^r(r^2t)$, $\bar T^r(t)=r^{-2}T^r(r^2t)$, and $\bar A^r,\bar S^r,\bar I^r,\bar Q^r$ likewise with $r^{-2}$. The cost (24) is
--   $$\hat J^r(T^r)=\mathbf E\Big(\int_0^\infty e^{-\gamma t}\,h\cdot\hat Q^r(t)\,dt\Big)\in[0,\infty],$$
--   and the fluid allocation (29) is $\bar T^*(t)=\big(t,\tfrac{\lambda_1-\mu_1}{\mu_2}t,\tfrac{\lambda_2}{\mu_3}t\big)$.
--
--   **Formalization Note** Classes are indexed by `Fin 2` and activities by `Fin 3` ($0\mapsto1$, $1\mapsto2$, $2\mapsto3$); the i.i.d. sequences keep the index base $i\ge1$. The $r$-th system is the $n$-th member, with $r=r_n$. Time is real and all conditions are imposed for $t\ge0$. Measurability (11) is measurability for the completion of $\mathbf P$ (the paper's space is complete). Finiteness of the renewal processes is the divergence of the partial sums of $\check u_k$, $\check v_j$ for every $\omega$ (p. 614, after removing a null set). Queue lengths are real, so no truncated subtraction occurs. The cost is an iterated lower Lebesgue integral with values in $[0,\infty]$. Assumption 3.3's open neighbourhood is an interval $(-\delta,\delta)$, which is equivalent.
-- source:
--   Bell and Williams, Dynamic scheduling of a system with two parallel servers in heavy traffic with resource pooling, Ann. Appl. Probab. 11 (2001), pp. 613–618, Sections 2–3, (2)–(20), (24), (26)–(29), Assumptions 3.1–3.3; p. 633, (92)–(95)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace BellWilliams2001.ThresholdPolicy

/-!
Bell and Williams (2001), Sections 2–3 (pp. 613–618): the sequence of parallel server systems.

Index conventions. Classes `k = 1, 2` are `Fin 2` (`0 ↦ 1`, `1 ↦ 2`); activities `j = 1, 2, 3`
are `Fin 3` (`0 ↦ 1`, `1 ↦ 2`, `2 ↦ 3`). The i.i.d. sequences keep the paper's index base:
`uC k i`, `vC j i` for `i = 1, 2, …` (the value at `i = 0` is never used). The paper's index
`r → ∞` through a sequence in `[1,∞)` (p. 615) is `r n`, `n : ℕ`, and every `r`-dependent object
is indexed by `n`. Time is real; all conditions quantify over `t ≥ 0`.
-/

/-- The data and standing assumptions of the sequence of parallel server systems.
Every field is a hypothesis of the paper:
* the probability space and the `r`-independent primitives `ǔ_k(i)`, `v̌_j(i)` of (15) (p. 615):
  strictly positive, i.i.d. within each sequence, the five sequences mutually independent
  (p. 613–614), mean one, finite squared coefficient of variation (finite variance);
* finiteness of the renewal counting processes everywhere on `Ω` (p. 614, after removing a null
  set), as divergence of the partial sums;
* the index sequence `r n ∈ [1,∞)`, `r n → ∞`, the rates `λ^r_k, μ^r_j > 0`;
* Assumption 3.1 (p. 615–616), the holding costs `h_k > 0` and discount rate `γ > 0` (p. 617,
  after (24)), Assumption 3.2 (p. 617) and Assumption 3.3 (p. 618). -/
structure SystemSequence (Ω : Type*) [MeasurableSpace Ω] where
  /-- the probability measure `P` -/
  P : Measure Ω
  isProb : IsProbabilityMeasure P
  /-- `ǔ_k(i)`, `i ≥ 1` -/
  uC : Fin 2 → ℕ → Ω → ℝ
  /-- `v̌_j(i)`, `i ≥ 1` -/
  vC : Fin 3 → ℕ → Ω → ℝ
  uC_meas : ∀ k i, Measurable (uC k i)
  vC_meas : ∀ j i, Measurable (vC j i)
  uC_pos : ∀ k i ω, 1 ≤ i → 0 < uC k i ω
  vC_pos : ∀ j i ω, 1 ≤ i → 0 < vC j i ω
  /-- all of `{ǔ_k(i)}`, `{v̌_j(i)}`, `i ≥ 1`, are mutually independent -/
  indep : iIndepFun (fun p : (Fin 2 × ℕ) ⊕ (Fin 3 × ℕ) =>
    Sum.elim (fun q : Fin 2 × ℕ => uC q.1 (q.2 + 1)) (fun q : Fin 3 × ℕ => vC q.1 (q.2 + 1)) p) P
  uC_ident : ∀ k i, 1 ≤ i → IdentDistrib (uC k i) (uC k 1) P P
  vC_ident : ∀ j i, 1 ≤ i → IdentDistrib (vC j i) (vC j 1) P P
  uC_memLp : ∀ k, MemLp (uC k 1) 2 P
  vC_memLp : ∀ j, MemLp (vC j 1) 2 P
  uC_mean : ∀ k, ∫ ω, uC k 1 ω ∂P = 1
  vC_mean : ∀ j, ∫ ω, vC j 1 ω ∂P = 1
  uC_finite : ∀ k ω, Tendsto (fun m => partialSum (fun i => uC k i ω) m) atTop atTop
  vC_finite : ∀ j ω, Tendsto (fun m => partialSum (fun i => vC j i ω) m) atTop atTop
  /-- the index `r` of the `n`-th system -/
  r : ℕ → ℝ
  r_ge : ∀ n, 1 ≤ r n
  r_tendsto : Tendsto r atTop atTop
  /-- `λ^r_k` -/
  lamR : ℕ → Fin 2 → ℝ
  /-- `μ^r_j` -/
  muR : ℕ → Fin 3 → ℝ
  lamR_pos : ∀ n k, 0 < lamR n k
  muR_pos : ∀ n j, 0 < muR n j
  /-- `λ_k` -/
  lam : Fin 2 → ℝ
  /-- `μ_j` -/
  mu : Fin 3 → ℝ
  /-- `θ_k` -/
  theta : Fin 2 → ℝ
  lam_pos : ∀ k, 0 < lam k
  mu_pos : ∀ j, 0 < mu j
  /-- Assumption 3.1 (i): `λ₁ > μ₁` -/
  a31_i : mu 0 < lam 0
  /-- Assumption 3.1 (ii): `1 − (λ₁ − μ₁)/μ₂ = λ₂/μ₃` -/
  a31_ii : 1 - (lam 0 - mu 0) / mu 1 = lam 1 / mu 2
  /-- Assumption 3.1 (iii): `λ^r_k → λ_k` -/
  a31_iii : ∀ k, Tendsto (fun n => lamR n k) atTop (𝓝 (lam k))
  /-- Assumption 3.1 (iv): `μ^r_j → μ_j` -/
  a31_iv : ∀ j, Tendsto (fun n => muR n j) atTop (𝓝 (mu j))
  /-- Assumption 3.1 (v): `r μ^r_2 ((λ^r_1 − μ^r_1)/μ^r_2 − (λ₁ − μ₁)/μ₂) → θ₁` -/
  a31_v : Tendsto (fun n => r n * muR n 1 *
    ((lamR n 0 - muR n 0) / muR n 1 - (lam 0 - mu 0) / mu 1)) atTop (𝓝 (theta 0))
  /-- Assumption 3.1 (vi): `r μ^r_3 (λ^r_2/μ^r_3 − λ₂/μ₃) → θ₂` -/
  a31_vi : Tendsto (fun n => r n * muR n 2 * (lamR n 1 / muR n 2 - lam 1 / mu 2)) atTop
    (𝓝 (theta 1))
  /-- holding costs `h_k` -/
  h : Fin 2 → ℝ
  h_pos : ∀ k, 0 < h k
  /-- discount rate `γ` -/
  gamma : ℝ
  gamma_pos : 0 < gamma
  /-- Assumption 3.2: `h₁ μ₂ ≥ h₂ μ₃` -/
  a32 : h 1 * mu 2 ≤ h 0 * mu 1
  /-- Assumption 3.3: with `u_k(i) = ǔ_k(i)/λ_k`, `v_j(i) = v̌_j(i)/μ_j`, the moment generating
  functions are finite on a neighbourhood `(−δ, δ)` of `0` (equivalent to the page's non-empty
  open neighbourhood `𝒪` of `0`). -/
  a33 : ∃ δ : ℝ, 0 < δ ∧ ∀ l ∈ Set.Ioo (-δ) δ,
    (∀ k i, 1 ≤ i → Integrable (fun ω => Real.exp (l * (uC k i ω / lam k))) P) ∧
    (∀ j i, 1 ≤ i → Integrable (fun ω => Real.exp (l * (vC j i ω / mu j))) P)

/-- A (three-dimensional) service time allocation process of one system, `T ω j t = T_j(t)(ω)`
((6), p. 614). -/
abbrev Allocation (Ω : Type*) := Ω → Fin 3 → ℝ → ℝ

namespace SystemSequence

variable {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)

/-- `ξ^r_k(m) = ∑_{i=1}^m u^r_k(i)` with `u^r_k(i) = ǔ_k(i)/λ^r_k` ((2), (15)). -/
noncomputable def xi (n : ℕ) (k : Fin 2) (ω : Ω) (m : ℕ) : ℝ :=
  partialSum (fun i => M.uC k i ω / M.lamR n k) m

/-- `η^r_j(m) = ∑_{i=1}^m v^r_j(i)` with `v^r_j(i) = v̌_j(i)/μ^r_j` ((4), (15)). -/
noncomputable def eta (n : ℕ) (j : Fin 3) (ω : Ω) (m : ℕ) : ℝ :=
  partialSum (fun i => M.vC j i ω / M.muR n j) m

/-- The arrival process `A^r_k(t) = sup{m ≥ 0 : ξ^r_k(m) ≤ t}` ((3)); it is finite because of
`uC_finite`, so `toNat` loses nothing. -/
noncomputable def A (n : ℕ) (k : Fin 2) (ω : Ω) (t : ℝ) : ℝ :=
  ((renewalCount (M.xi n k ω) t).toNat : ℝ)

/-- The service process `S^r_j(t) = sup{m ≥ 0 : η^r_j(m) ≤ t}` ((5)); finite by `vC_finite`. -/
noncomputable def S (n : ℕ) (j : Fin 3) (ω : Ω) (t : ℝ) : ℝ :=
  ((renewalCount (M.eta n j ω) t).toNat : ℝ)

/-- Idle times `I₁(t) = t − T₁(t)` (7) and `I₂(t) = t − T₂(t) − T₃(t)` (8). -/
def idle (T : Allocation Ω) (ω : Ω) (k : Fin 2) (t : ℝ) : ℝ :=
  if k = 0 then t - T ω 0 t else t - T ω 1 t - T ω 2 t

/-- Queue lengths `Q₁(t) = A₁(t) − S₁(T₁(t)) − S₂(T₂(t))` (9) and `Q₂(t) = A₂(t) − S₃(T₃(t))`
(10), computed in `ℝ` (no truncated subtraction). -/
noncomputable def queue (n : ℕ) (T : Allocation Ω) (ω : Ω) (k : Fin 2) (t : ℝ) : ℝ :=
  if k = 0 then M.A n 0 ω t - M.S n 0 ω (T ω 0 t) - M.S n 1 ω (T ω 1 t)
  else M.A n 1 ω t - M.S n 2 ω (T ω 2 t)

/-- A **scheduling control policy** for the `n`-th system (p. 614–615): `T` satisfies
(11) `T_j(t)` is a random variable for each `t ≥ 0` (measurable for the completion of `P`, the
paper's probability space being complete); (12) every path `T_j(·)` is continuous and
nondecreasing with `T_j(0) = 0`; (13) every path `I_k(·)` is continuous and nondecreasing with
`I_k(0) = 0`; (14) `Q_k(t) ≥ 0` for all `t ≥ 0`. Nothing else is required: allocations may
anticipate the future. -/
structure IsAdmissible (n : ℕ) (T : Allocation Ω) : Prop where
  meas : ∀ j t, 0 ≤ t → AEMeasurable (fun ω => T ω j t) M.P
  alloc_zero : ∀ ω j, T ω j 0 = 0
  alloc_cont : ∀ ω j, ContinuousOn (T ω j) (Set.Ici 0)
  alloc_mono : ∀ ω j, MonotoneOn (T ω j) (Set.Ici 0)
  idle_zero : ∀ ω k, idle T ω k 0 = 0
  idle_cont : ∀ ω k, ContinuousOn (idle T ω k) (Set.Ici 0)
  idle_mono : ∀ ω k, MonotoneOn (idle T ω k) (Set.Ici 0)
  queue_nonneg : ∀ ω k t, 0 ≤ t → 0 ≤ M.queue n T ω k t

/-- Diffusion-scaled queue length `Q̂^r(t) = r^{-1} Q^r(r² t)` (19). -/
noncomputable def Qhat (n : ℕ) (T : Allocation Ω) (ω : Ω) (t : ℝ) (k : Fin 2) : ℝ :=
  M.queue n T ω k (M.r n ^ 2 * t) / M.r n

/-- Diffusion-scaled idle time `Î^r(t) = r^{-1} I^r(r² t)` (20). -/
noncomputable def Ihat (n : ℕ) (T : Allocation Ω) (ω : Ω) (t : ℝ) (k : Fin 2) : ℝ :=
  idle T ω k (M.r n ^ 2 * t) / M.r n

/-- Fluid-scaled allocation `T̄^r(t) = r^{-2} T^r(r² t)` (16). -/
noncomputable def Tbar (n : ℕ) (T : Allocation Ω) (ω : Ω) (t : ℝ) (j : Fin 3) : ℝ :=
  T ω j (M.r n ^ 2 * t) / M.r n ^ 2

/-- Fluid-scaled arrivals `Ā^r(t) = r^{-2} A^r(r² t)` (92). -/
noncomputable def Abar (n : ℕ) (ω : Ω) (t : ℝ) (k : Fin 2) : ℝ :=
  M.A n k ω (M.r n ^ 2 * t) / M.r n ^ 2

/-- Fluid-scaled service processes `S̄^r(t) = r^{-2} S^r(r² t)` (93). -/
noncomputable def Sbar (n : ℕ) (ω : Ω) (t : ℝ) (j : Fin 3) : ℝ :=
  M.S n j ω (M.r n ^ 2 * t) / M.r n ^ 2

/-- Fluid-scaled idle time `Ī^r(t) = r^{-2} I^r(r² t)` (94). -/
noncomputable def Ibar (n : ℕ) (T : Allocation Ω) (ω : Ω) (t : ℝ) (k : Fin 2) : ℝ :=
  idle T ω k (M.r n ^ 2 * t) / M.r n ^ 2

/-- Fluid-scaled queue length `Q̄^r(t) = r^{-2} Q^r(r² t)` (95). -/
noncomputable def Qbar (n : ℕ) (T : Allocation Ω) (ω : Ω) (t : ℝ) (k : Fin 2) : ℝ :=
  M.queue n T ω k (M.r n ^ 2 * t) / M.r n ^ 2

/-- The cost (24): `Ĵ^r(T^r) = E(∫₀^∞ e^{−γt} h · Q̂^r(t) dt)`, as an iterated lower Lebesgue
integral with values in `[0,∞]` (for an admissible `T` the integrand is nonnegative, so
`ENNReal.ofReal` is the identity on it). -/
noncomputable def cost (n : ℕ) (T : Allocation Ω) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ t in Set.Ioi (0 : ℝ),
    ENNReal.ofReal (Real.exp (-M.gamma * t) * ∑ k, M.h k * M.Qhat n T ω t k) ∂volume ∂M.P

/-- The fluid allocation `T̄*(t) = (t, ((λ₁ − μ₁)/μ₂) t, (λ₂/μ₃) t)` (29). -/
noncomputable def fluidAllocation (t : ℝ) : Fin 3 → ℝ :=
  ![t, (M.lam 0 - M.mu 0) / M.mu 1 * t, M.lam 1 / M.mu 2 * t]

end SystemSequence

end BellWilliams2001.ThresholdPolicy


