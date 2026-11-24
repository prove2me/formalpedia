-- Prove2me | Definitions.Def_LeviBalancing_TripleBalancing_Supplement_Randomization
-- name    : LeviBalancing_TripleBalancing_Supplement_Randomization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:20:14.967724+00:00
-- url     : https://prove2.me/theorems/6697167f-69b7-4960-bae5-45add09b752a
-- title:
--   Private randomization and the recursively constructed integer dual-balancing policy
-- statement:
--   A probability space carries pre-coin information $\mathcal G_s$, post-coin information $\mathcal H_s$, and integer nonnegative demand, with $\mathcal G_s\subseteq\mathcal H_s\subseteq\mathcal G_{s+1}$. Past demands are known before the next order. The supplied conditional demand kernels have finite remaining-demand means at every specified information state. Conditional on $\mathcal G_s$, the joint law of the demand path and the current coin $U_s$ is the demand law times the uniform law on $[0,1)$.
--
--   A measurable root selector takes the current inventory position $x_s$ and pre-coin information to a finite nonnegative intersection $q'_s$ of the two interpolated integer cost functions. Write $n=\lfloor q'_s\rfloor$. The actual policy orders
--
--   $$
--   Q_s=\begin{cases} n,&U_s<n+1-q'_s,\ n+1,&U_s\ge n+1-q'_s.\end{cases}
--   $$
--
--   Its state then evolves by $x_{s+1}=x_s+Q_s-D_s$ from the published initial inventory position, and it orders zero after $T-L$. At an integral root the order is deterministic. Balance is required at the recursively reached states, before the current coin; neither balance nor the cost bound is postulated for the realized random order after that coin.
--
--   This defines an actual order process from conditional costs and private randomization. A finite measurable balancing selector is explicit data because the existence assertion on p. 293 fails with zero holding rates and an unbounded demand tail; see DISPROOF.md. It does not impose strict positivity or bounded support.
-- source:
--   Levi, Pál, Roundy & Shmoys, Approximation Algorithms for Stochastic Inventory Control Models, Math. Oper. Res. 32(2):284–302 (2007), DOI 10.1287/moor.1060.0205, pp. 288–289, 293, 295–296 (PDF 5–6, 10, 12–13), §2, §4.1, §4.3

import Mathlib
import Definitions.Def_LeviBalancing_TripleBalancing_Supplement_ConditionalCosts

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace LeviBalancing.TripleBalancing.Supplement
open LeviBalancing.DualBalancing

/-- The source's exogenous information, enlarged by past private coins. `pre s` precedes
coin s; `post s` includes that coin, but the next pre-information contains both. The
conditional law of (the full demand path, current coin) is demand-law × Uniform[0,1).
The law may have arbitrary correlations between periods and arbitrary external information. -/
structure RandomizedInput (Ω : Type*) [m : MeasurableSpace Ω] (I : Instance) where
  μ : Measure Ω
  probability : IsProbabilityMeasure μ
  pre : Filtration ℤ m
  post : Filtration ℤ m
  pre_post : ∀ s, pre s ≤ post s
  post_next : ∀ s, post s ≤ pre (s + 1)
  process : DemandProcess pre μ I.T
  integer_demand : ∀ s, 1 ≤ s → s ≤ (I.T : ℤ) → ∀ ω, ∃ n : ℕ, process.D s ω = n
  coin : ℤ → Ω → ℝ
  coin_range : ∀ s ω, coin s ω ∈ Set.Ico (0 : ℝ) 1
  coin_measurable : ∀ s, Measurable[post s] (coin s)
  law : ℤ → Kernel Ω (ℤ → ℝ)
  law_probability : ∀ s, IsMarkovKernel (law s)
  law_known : ∀ s (A : Set (ℤ → ℝ)), MeasurableSet A →
    Measurable[pre s] (fun ω => law s ω A)
  law_nonneg_integer : ∀ s ω, ∀ᵐ d ∂(law s ω),
    ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → ∃ n : ℕ, d j = (n : ℝ)
  conditional_mean : ∀ s j ω, 1 ≤ s → s ≤ j → j ≤ (I.T : ℤ) →
    Integrable (fun d : ℤ → ℝ => d j) (law s ω)
  /-- Conditional independence of CURRENT randomization and future demand, not independence
  of demands. Demands outside the horizon are canonically set to zero in the path map. -/
  joint_law : ∀ s (A : Set Ω) (C : Set ((ℤ → ℝ) × ℝ)),
    1 ≤ s → s ≤ (I.T : ℤ) → MeasurableSet[pre s] A → MeasurableSet C →
    μ (A ∩ {ω | ((fun j => if 1 ≤ j ∧ j ≤ (I.T : ℤ) then process.D j ω else 0),
      coin s ω) ∈ C}) =
      ∫⁻ ω in A, ((law s ω).prod (volume.restrict (Set.Ico (0 : ℝ) 1))) C ∂μ

/-- Select an interpolant root using only pre-coin information and the current inventory.
Balance is specified separately at the states reached by the recursive algorithm. -/
structure RootSelector {Ω : Type*} [MeasurableSpace Ω] {I : Instance}
    (M : RandomizedInput Ω I) where
  root : ℤ → Ω → ℝ → ℝ
  nonneg : ∀ s ω x, 0 ≤ root s ω x
  measurable : ∀ s, @Measurable (Ω × ℝ) ℝ
    ((M.pre s).prod inferInstance) inferInstance (fun z => root s z.1 z.2)

/-- Barycentric randomized rounding, including the integral root (probability one on the root). -/
def roundedOrder (q u : ℝ) : ℝ :=
  let n : ℤ := ⌊q⌋
  if u < (n : ℝ) + 1 - q then (n : ℝ) else (n : ℝ) + 1

def startingPosition (I : Instance) : ℝ :=
  I.ni0 + ∑ j ∈ Icc (1 - (I.L : ℤ)) 0, I.q j

/-- Inventory position before period n+1, computed from realized integer orders and demands. -/
def roundingState {Ω : Type*} [MeasurableSpace Ω] {I : Instance}
    (M : RandomizedInput Ω I) (r : RootSelector M) : ℕ → Ω → ℝ
  | 0, _ => startingPosition I
  | n + 1, ω =>
    let s : ℤ := (n : ℤ) + 1
    let x := roundingState M r n ω
    let q := if s ≤ (I.T : ℤ) - I.L then roundedOrder (r.root s ω x) (M.coin s ω) else 0
    x + q - M.process.D s ω

/-- The actual order process is recursively generated. It is not defined by a cost guarantee. -/
def randomizedPolicy {Ω : Type*} [MeasurableSpace Ω] {I : Instance}
    (M : RandomizedInput Ω I) (r : RootSelector M) (s : ℤ) (ω : Ω) : ℝ :=
  if 1 ≤ s ∧ s ≤ (I.T : ℤ) - I.L then
    roundedOrder (r.root s ω (roundingState M r (s - 1).toNat ω)) (M.coin s ω)
  else 0

/-- Exactly the source's interpolant-intersection rule, at every reached pre-coin state.
This witness is essential when zero holding rates make the printed existence claim fail. -/
def IsBalancingSelector {Ω : Type*} [MeasurableSpace Ω] {I : Instance}
    (M : RandomizedInput Ω I) (r : RootSelector M) : Prop :=
  ∀ s, 1 ≤ s → s ≤ (I.T : ℤ) - I.L → ∀ ω,
    let x := roundingState M r (s - 1).toNat ω
    let q := r.root s ω x
    integerInterpolation (conditionalHolding I (M.law s ω) s x) q =
      integerInterpolation (conditionalBacklog I (M.law s ω) s x) q

end LeviBalancing.TripleBalancing.Supplement


