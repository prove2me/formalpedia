-- Prove2me | Definitions.Def_FairDiffusionLimit_Dynamics
-- name    : FairDiffusionLimit_Dynamics
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:27:18.067793+00:00
-- url     : https://prove2.me/theorems/8cd03f4c-8167-47cf-88ca-df9a3ac53760
-- title:
--   Network dynamics (4)–(9), the Markov state $\Xi=(W,U,V)$, diffusion scaling (22)–(26), realizations, stationarity, positive Harris recurrence and the bounded workload condition (71)
-- statement:
--   This module builds the stochastic dynamics of network $k$ and the notions used in the interchange-of-limits results (pp. 9–12, 18, 21, 24).
--
--   **Dynamics.** $E_r(t)=\max\{i:\sum_{j\le i}u_r(j)\le t\}$ and $S_r(t)=\max\{i:\sum_{j\le i}v_r(j)\le t\}$ (4), where $u_r(1),v_r(1)$ are the residuals read off the initial state. A sample path satisfies
--   $$N_r(t)=N_r(0)+E_r(t)-S_r(D_r(t)),\qquad D_r(t)=\int_0^t\Lambda_r(N(s))\,ds\tag{6–7}$$
--   with $W_r=\nu^k_rN_r$ (8). The Markov state is $\Xi(t)=(W(t),U(t),V(t))$ with $U_r(t)=\sum_{i=1}^{E_r(t)+1}u_r(i)-t$ and $V_r(t)=\sum_{i=1}^{S_r(D_r(t))+1}v_r(i)-D_r(t)$ (9).
--
--   **Diffusion scaling.** $\hat\Xi^k(t)=\Xi^k(k^2t)/k$, $\hat W^k(t)=W^k(k^2t)/k$, $\tilde D^k(t)=D^k(k^2t)/k^2$, $\hat E^k_r(t)=(E^k_r(k^2t)-\lambda^k_rk^2t)/k$, $\hat S^k_r(t)=(S^k_r(k^2t)-k^2t/\nu^k_r)/k$, the free process $\hat X^k_r(t)=\nu^k_r(\hat E^k_r(t)-\hat S^k_r(\tilde D^k_r(t)))+k(\rho^k_r-\rho_r)t$ (24), $\hat Y^k(t)=k[ct-A\tilde D^k(t)]$ (25) and $\hat Z^k(t)=kH^T[\rho t-\tilde D^k(t)]$ (26).
--
--   **Realizations.** A primitive space carries the i.i.d. base primitives of (12); all networks and initial states built on one primitive space are coupled (the paper's $\Xi(t;x)$). A realization of network $k$ from an initial law $\mu$ is a primitive space with an initial state $\Xi(0)\sim\mu$ independent of the primitives and a queue-length process that solves the dynamics almost surely.
--
--   **Stationarity and recurrence.** $\pi$ is stationary for network $k$ if a realization from $\pi$ exists and every realization from $\pi$ has $\Xi^k(t)\sim\pi$ for all $t\ge0$; $\hat\pi^k$ is its image under $x\mapsto x/k$, and $\hat\pi^k_1$ the law of $\hat W^k(0)$. Positive Harris recurrence: some nonzero $\sigma$-finite $\varphi$ has every set of positive $\varphi$-measure visited for infinite total time from every initial state, almost surely, and a stationary distribution exists.
--
--   **Bounded workload condition (71).** There is $\kappa>0$ such that for every $k\ge1$, every sample path and every $t\ge0$,
--   $$\sup_{0\le s\le t}|\hat W^k(s)|\le\kappa\Big(|\hat W^k(0)|+\sup_{0\le s\le t}|\hat X^k(s)|\Big).$$
--
--   **Formalization Note** "Any sample-path" in (71) is read literally: every path satisfying the dynamics whose counts (4) are finite (`FiniteCounts`: the primitive partial sums are unbounded; otherwise the maxima in (4) are infinite and the sequence is not a sample path of the model), for every initial state and nonnegative primitive sequence; the suprema are written through bounds, so infinite suprema are handled. `Nat.card` gives $0$ for an infinite count, which only happens on a null set. Measurability of $\Xi(t)$, $D(t)$ and the counts is part of a realization.
-- source:
--   Ye, Yao, Diffusion limit of fair resource control — stationarity and interchange of limits, SSRN 2579541 (2015), §2, pp.9–12: (4)–(9), (12), (22)–(26); p.10 (Ξ(t; x)); p.16, p.18 (Theorem 7(b)); p.21 (71); p.24

import Mathlib
import Definitions.Def_FairDiffusionLimit_Network

open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace FairDiffusionLimit

/-- Number of renewal epochs in `[0, t]` of the sequence of times `x 0, x 1, …`: the number of
`n ≥ 0` with `x 0 + ⋯ + x n ≤ t`. With `x i = u_r(i + 1)` this is the delayed renewal count
`E_r(t) = max{i : ∑_{j=1}^i u_r(j) ≤ t}` of (4), p. 9 (for nonnegative times the set of such `i ≥ 1`
is `{1, …, E_r(t)}`).

**Formalization Note.** `Nat.card` of an infinite set is `0`; this happens only when the partial sums
stay bounded by `t`, which has probability zero under the standing assumptions. -/
noncomputable def countRenewals (x : ℕ → ℝ) (t : ℝ) : ℕ :=
  Nat.card {n : ℕ // ∑ l ∈ Finset.range (n + 1), x l ≤ t}

/-- The data of one sample path of a network: the initial state `x = (w, u(1), v(1))` (workload and
time-zero residuals), the base primitive sequences `ua r i = u¹_r(i + 2)`, `va r i = v¹_r(i + 2)`
(network 1's primitives, rescaled for network `k` by (12)), and the queue-length path `n(t) = N(t)`. -/
structure PathData (R : ℕ) where
  /-- The initial state `x = Ξ(0) = (W(0), u(1), v(1))`. -/
  x : State R
  /-- `ua r i = u¹_r(i + 2)`. -/
  ua : Fin R → ℕ → ℝ
  /-- `va r i = v¹_r(i + 2)`. -/
  va : Fin R → ℕ → ℝ
  /-- The queue lengths `N_r(t)`. -/
  n : ℝ → Fin R → ℕ

namespace NetSeq

variable {L R : ℕ} (S : NetSeq L R)

/-- The interarrival times of class `r` in network `k`: `u^k_r(1)` is the residual read off the
initial state, and `u^k_r(i) = (λ¹_r/λ^k_r) u¹_r(i)` for `i ≥ 2`, (12), p. 11. Index `i` stands for
`u^k_r(i + 1)`. -/
noncomputable def uSeq (k : ℕ) (π : PathData R) (r : Fin R) : ℕ → ℝ :=
  fun i => if i = 0 then π.x.2.1 r else S.lam 1 r / S.lam k r * π.ua r (i - 1)

/-- The work requirements of class `r` in network `k`: `v^k_r(1)` is the residual read off the
initial state, and `v^k_r(i) = (ν^k_r/ν¹_r) v¹_r(i)` for `i ≥ 2`, (12). Index `i` stands for
`v^k_r(i + 1)`. -/
noncomputable def vSeq (k : ℕ) (π : PathData R) (r : Fin R) : ℕ → ℝ :=
  fun i => if i = 0 then π.x.2.2 r else S.nu k r / S.nu 1 r * π.va r (i - 1)

/-- The arrival count `E_r(t)`, (4). -/
noncomputable def Ecount (k : ℕ) (π : PathData R) (r : Fin R) (t : ℝ) : ℕ :=
  countRenewals (S.uSeq k π r) t

/-- The service count `S_r(t)`, (4) (`t` is cumulative allocated capacity). -/
noncomputable def Scount (k : ℕ) (π : PathData R) (r : Fin R) (t : ℝ) : ℕ :=
  countRenewals (S.vSeq k π r) t

/-- The cumulative allocation `D_r(t) = ∫₀ᵗ Λ_r(N(s)) ds`, (7), p. 9. -/
noncomputable def Dalloc (π : PathData R) (t : ℝ) (r : Fin R) : ℝ :=
  ∫ s in (0 : ℝ)..t, S.Lam (fun r' => (π.n s r' : ℝ)) r

/-- `π` is a sample path of network `k` (pp. 8–10): the residuals and primitives are nonnegative,
the initial workload is `W(0) = ν^k N(0)` (8), the allocation `s ↦ Λ_r(N(s))` is integrable on every
`[0, t]`, and for all `t ≥ 0` and `r`
`N_r(t) = N_r(0) + E_r(t) − S_r(D_r(t))`, (6), with `D` as in (7). -/
def IsNetPath (k : ℕ) (π : PathData R) : Prop :=
  (∀ r, 0 ≤ π.x.2.1 r ∧ 0 ≤ π.x.2.2 r) ∧ (∀ r i, 0 ≤ π.ua r i ∧ 0 ≤ π.va r i) ∧
  (∀ r, π.x.1 r = S.nu k r * (π.n 0 r : ℝ)) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ r,
    IntervalIntegrable (fun s => S.Lam (fun r' => (π.n s r' : ℝ)) r) volume 0 t) ∧
  ∀ t : ℝ, 0 ≤ t → ∀ r,
    ((π.n t r : ℕ) : ℤ) = (π.n 0 r : ℤ) + (S.Ecount k π r t : ℤ) - (S.Scount k π r (S.Dalloc π t r) : ℤ)

/-- The Markov state `Ξ(t) = (W(t), U(t), V(t))` of network `k` (pp. 9–10): `W_r(t) = ν^k_r N_r(t)`
(8), `U_r(t) = ∑_{i=1}^{E_r(t)+1} u_r(i) − t` and `V_r(t) = ∑_{i=1}^{S_r(D_r(t))+1} v_r(i) − D_r(t)`
(9). -/
noncomputable def stateAt (k : ℕ) (π : PathData R) (t : ℝ) : State R :=
  (fun r => S.nu k r * (π.n t r : ℝ),
   fun r => (∑ i ∈ Finset.range (S.Ecount k π r t + 1), S.uSeq k π r i) - t,
   fun r => (∑ i ∈ Finset.range (S.Scount k π r (S.Dalloc π t r) + 1), S.vSeq k π r i)
      - S.Dalloc π t r)

/-- The diffusion-scaled state `Ξ̂^k(t) = Ξ^k(k²t)/k`, p. 12. -/
noncomputable def hatXi (k : ℕ) (π : PathData R) (t : ℝ) : State R :=
  (k : ℝ)⁻¹ • S.stateAt k π ((k : ℝ) ^ 2 * t)

/-- The diffusion-scaled workload `Ŵ^k(t) = W^k(k²t)/k`, p. 12. -/
noncomputable def hatW (k : ℕ) (π : PathData R) (t : ℝ) : Fin R → ℝ :=
  (S.hatXi k π t).1

/-- `Ê^k_r(t) = (E^k_r(k²t) − λ^k_r k²t)/k`, p. 12. -/
noncomputable def hatE (k : ℕ) (π : PathData R) (t : ℝ) (r : Fin R) : ℝ :=
  ((S.Ecount k π r ((k : ℝ) ^ 2 * t) : ℝ) - S.lam k r * (k : ℝ) ^ 2 * t) / k

/-- `Ŝ^k_r(s) = (S^k_r(k²s) − (ν^k_r)⁻¹k²s)/k`, p. 12. -/
noncomputable def hatS (k : ℕ) (π : PathData R) (s : ℝ) (r : Fin R) : ℝ :=
  ((S.Scount k π r ((k : ℝ) ^ 2 * s) : ℝ) - (k : ℝ) ^ 2 * s / S.nu k r) / k

/-- The fluid-scaled allocation `D̃^k(t) = D^k(k²t)/k²`, p. 12. -/
noncomputable def tildeD (k : ℕ) (π : PathData R) (t : ℝ) : Fin R → ℝ :=
  fun r => S.Dalloc π ((k : ℝ) ^ 2 * t) r / (k : ℝ) ^ 2

/-- The free process `X̂^k_r(t) = ν^k_r(Ê^k_r(t) − Ŝ^k_r(D̃^k_r(t))) + k(ρ^k_r − ρ_r)t`, (24), p. 12. -/
noncomputable def hatX (k : ℕ) (π : PathData R) (t : ℝ) : Fin R → ℝ :=
  fun r => S.nu k r * (S.hatE k π t r - S.hatS k π (S.tildeD k π t r) r)
    + (k : ℝ) * (S.rhoK k r - S.rho r) * t

/-- The regulator `Ŷ^k(t) = k[ct − AD̃^k(t)]`, (25), p. 12. -/
noncomputable def hatY (k : ℕ) (π : PathData R) (t : ℝ) : Fin L → ℝ :=
  (k : ℝ) • (t • S.c - S.A *ᵥ S.tildeD k π t)

/-- `Ẑ^k(t) = kHᵀ[ρt − D̃^k(t)]`, (26), p. 12. -/
noncomputable def hatZ (H : Matrix (Fin R) (Fin (R - L)) ℝ) (k : ℕ) (π : PathData R) (t : ℝ) :
    Fin (R - L) → ℝ :=
  (k : ℝ) • (Hᵀ *ᵥ (t • S.rho - S.tildeD k π t))

/-- A probability space carrying the **base primitives** `u¹_r(i)`, `v¹_r(i)` (`i ≥ 2`) of the
network sequence, i.i.d. with laws `F^a_r`, `F^s_r`, all independent (p. 8 and (12), p. 11). Every
network `k` is driven by these primitives through (12), so processes of different networks and from
different initial states built on one `PrimSpace` are coupled, as in the paper's `Ξ̂^k(t; x)`
(p. 10). -/
structure PrimSpace (S : NetSeq L R) : Type 1 where
  /-- The sample space. -/
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  /-- The probability measure. -/
  P : Measure Ω
  [isProb : IsProbabilityMeasure P]
  /-- `ua r i ω = u¹_r(i + 2)(ω)`. -/
  ua : Fin R → ℕ → Ω → ℝ
  /-- `va r i ω = v¹_r(i + 2)(ω)`. -/
  va : Fin R → ℕ → Ω → ℝ
  meas_ua : ∀ r i, Measurable (ua r i)
  meas_va : ∀ r i, Measurable (va r i)
  law : P.map (fun ω => ((fun q : Fin R × ℕ => ua q.1 q.2 ω), (fun q : Fin R × ℕ => va q.1 q.2 ω)))
    = S.primLaw

attribute [instance] PrimSpace.mΩ PrimSpace.isProb

/-- The vector of all base primitives of a `PrimSpace`. -/
def PrimSpace.prim {S : NetSeq L R} (C : PrimSpace S) (ω : C.Ω) :
    (Fin R × ℕ → ℝ) × (Fin R × ℕ → ℝ) :=
  ((fun q : Fin R × ℕ => C.ua q.1 q.2 ω), (fun q : Fin R × ℕ => C.va q.1 q.2 ω))

/-- The sample-path data at `ω` of the network started from `X0 ω` with queue-length process `N`. -/
def PrimSpace.pd {S : NetSeq L R} (C : PrimSpace S) (X0 : C.Ω → State R)
    (N : ℝ → C.Ω → Fin R → ℕ) (ω : C.Ω) : PathData R :=
  ⟨X0 ω, fun r i => C.ua r i ω, fun r i => C.va r i ω, fun t => N t ω⟩

/-- On the primitive space `C`, `N` is the queue-length process of network `k` started from the
(possibly random) initial state `X0`, which is independent of the primitives (the Markov setting of
p. 10): `X0` and every `N(t)` are measurable, and almost surely the path is a sample path of network
`k` (`IsNetPath`). The state `Ξ(t)`, the counts `E(t)`, `S(D(t))` and the allocation `D(t)` are
measurable for every `t`. -/
def IsPathOn (C : PrimSpace S) (k : ℕ) (X0 : C.Ω → State R) (N : ℝ → C.Ω → Fin R → ℕ) : Prop :=
  Measurable X0 ∧ IndepFun X0 C.prim C.P ∧ (∀ t, Measurable (N t)) ∧
  (∀ᵐ ω ∂(C.P), S.IsNetPath k (C.pd X0 N ω)) ∧
  (∀ t, Measurable fun ω => S.stateAt k (C.pd X0 N ω) t) ∧
  (∀ t, Measurable fun ω => S.Dalloc (C.pd X0 N ω) t) ∧
  (∀ t r, Measurable fun ω => S.Ecount k (C.pd X0 N ω) r t) ∧
  (∀ t r, Measurable fun ω => S.Scount k (C.pd X0 N ω) r (S.Dalloc (C.pd X0 N ω) t r))

/-- A **realization of network `k` started from the initial law `μ`** on `𝒳`: a primitive space
(`PrimSpace`) carrying an initial state `X0 ∼ μ`, independent of the primitives, and the
queue-length process `N` of network `k` from `X0` (`IsPathOn`). -/
structure Realization (S : NetSeq L R) (k : ℕ) (μ : Measure (State R)) : Type 1 where
  /-- The primitive space. -/
  C : PrimSpace S
  /-- The initial state `Ξ(0)`. -/
  X0 : C.Ω → State R
  /-- The queue-length process. -/
  N : ℝ → C.Ω → Fin R → ℕ
  isPath : S.IsPathOn C k X0 N
  law_X0 : C.P.map X0 = μ

/-- The sample-path data of a realization at `ω`. -/
def Realization.pd {S : NetSeq L R} {k : ℕ} {μ : Measure (State R)} (Rz : Realization S k μ)
    (ω : Rz.C.Ω) : PathData R :=
  Rz.C.pd Rz.X0 Rz.N ω

/-- `Ξ̂^k(t)` of a realization is a random element of `𝒳` (structural lemma). -/
theorem Realization.measurable_hatXi {S : NetSeq L R} {k : ℕ} {μ : Measure (State R)}
    (Rz : Realization S k μ) (t : ℝ) : Measurable fun ω => S.hatXi k (Rz.pd ω) t :=
  (continuous_const_smul _).measurable.comp (Rz.isPath.2.2.2.2.1 _)

/-- `Ŵ^k(t)` of a realization is a random vector (structural lemma). -/
theorem Realization.measurable_hatW {S : NetSeq L R} {k : ℕ} {μ : Measure (State R)}
    (Rz : Realization S k μ) (t : ℝ) : Measurable fun ω => S.hatW k (Rz.pd ω) t :=
  measurable_fst.comp (Rz.measurable_hatXi t)

/-- `π` is a **stationary distribution** of network `k` (pp. 18, 24): the network can be started from
`π`, and whenever `Ξ^k(0) ∼ π`, then `Ξ^k(t) ∼ π` for every `t ≥ 0`. The stationary distribution
`π̂^k` of the diffusion-scaled `Ξ̂^k(t) = Ξ^k(k²t)/k` is the image of `π` under `x ↦ x/k`.

**Formalization Note.** The conjunct "a realization from `π` exists" prevents the definition from
holding vacuously. -/
def IsStationary (k : ℕ) (π : Measure (State R)) : Prop :=
  Nonempty (Realization S k π) ∧
    ∀ Rz : Realization S k π, ∀ t : ℝ, 0 ≤ t → Rz.C.P.map (fun ω => S.stateAt k (Rz.pd ω) t) = π

/-- **Positive Harris recurrence** of network `k` (pp. 16, 18; Dai–Meyn [14]): there is a nonzero
σ-finite measure `φ` on `𝒳` such that, for every measurable `A` with `φ(A) > 0` and every initial
state `x`, the process started from `x` spends infinite total time in `A` almost surely; and the
process has a stationary distribution. (Recurrence of `Ξ^k` and of `Ξ̂^k(t) = Ξ^k(k²t)/k` coincide.) -/
def PositiveHarris (k : ℕ) : Prop :=
  (∃ φ : Measure (State R), φ ≠ 0 ∧ SigmaFinite φ ∧
    ∀ A : Set (State R), MeasurableSet A → 0 < φ A → ∀ x : State R,
      ∀ Rz : Realization S k (Measure.dirac x), ∀ᵐ ω ∂(Rz.C.P),
        ∫⁻ t in Set.Ici (0 : ℝ), A.indicator 1 (S.stateAt k (Rz.pd ω) t) = ⊤) ∧
  ∃ π : Measure (State R), S.IsStationary k π

/-- The counts `E_r(t)` and `S_r(t)` of (4), p. 9, are finite along `π` for every `t`: the partial
sums of the interarrival times and of the work requirements of network `k` are unbounded. On a
primitive sequence with bounded partial sums the paper's maxima in (4) are `+∞` (and
`countRenewals` returns its junk value `0`), so such a sequence is not a sample path of the model;
under the standing assumptions it occurs with probability zero. -/
def FiniteCounts (k : ℕ) (π : PathData R) : Prop :=
  ∀ r, Tendsto (fun n => ∑ l ∈ Finset.range (n + 1), S.uSeq k π r l) atTop atTop ∧
    Tendsto (fun n => ∑ l ∈ Finset.range (n + 1), S.vSeq k π r l) atTop atTop

/-- **The bounded workload condition** (71), p. 21: there is `κ > 0` such that for every network
`k ≥ 1`, every sample path and every `t ≥ 0`,
`sup_{0≤s≤t} |Ŵ^k(s)| ≤ κ(|Ŵ^k(0)| + sup_{0≤s≤t} |X̂^k(s)|)`.

**Formalization Note.** "Any sample-path" is read literally: every path satisfying the network
dynamics (`IsNetPath`) whose counts (4) are finite (`FiniteCounts`), for every initial state and
every nonnegative primitive sequence. The two suprema are written without `sSup`: for every bound
`M` of `|X̂^k|` on `[0, t]`, `|Ŵ^k(s)| ≤ κ(|Ŵ^k(0)| + M)` on `[0, t]` (equivalent, and meaningful
also when a supremum is infinite). -/
def BoundedWorkload : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ k : ℕ, 1 ≤ k → ∀ π : PathData R, S.IsNetPath k π → S.FiniteCounts k π →
    ∀ t : ℝ, 0 ≤ t → ∀ M : ℝ, (∀ s ∈ Set.Icc (0 : ℝ) t, l1 (S.hatX k π s) ≤ M) →
      ∀ s ∈ Set.Icc (0 : ℝ) t, l1 (S.hatW k π s) ≤ κ * (l1 (S.hatW k π 0) + M)

/-- The image `π̂^k` of a law `π` on `𝒳` under the diffusion scaling `x ↦ x/k`. -/
noncomputable def hatLaw (k : ℕ) (π : Measure (State R)) : Measure (State R) :=
  π.map (fun x => (k : ℝ)⁻¹ • x)

/-- The workload marginal `π̂^k_1` (p. 24): the law of `Ŵ^k(0) = W^k(0)/k` when `Ξ^k(0) ∼ π`. -/
noncomputable def wLaw (k : ℕ) (π : ProbabilityMeasure (State R)) : ProbabilityMeasure (Fin R → ℝ) :=
  π.map (f := fun x => (k : ℝ)⁻¹ • x.1)
    ((continuous_const_smul _).comp continuous_fst).measurable.aemeasurable

end NetSeq

/-- The law of a measurable random element, as a probability measure. -/
noncomputable def lawPM {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Ω → E) (hf : Measurable f) : ProbabilityMeasure E :=
  ⟨P.map f, Measure.isProbabilityMeasure_map hf.aemeasurable⟩

end FairDiffusionLimit


