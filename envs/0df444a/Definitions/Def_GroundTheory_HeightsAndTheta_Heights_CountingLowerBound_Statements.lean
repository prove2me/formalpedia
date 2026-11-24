-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:47.830082+00:00
-- url     : https://prove2.me/theorems/9675867a-0ffb-4df9-87b7-3ff7df1e62e0
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CountingLowerBound/Statements.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.LowerBound
open Real MeasureTheory Filter Topology
noncomputable section
universe u
structure ReductionSmallLast.Hyp
    (K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La : ℝ) : Prop where
  f_pos : 0 < f
  j'_pos : 0 < j'
  vol_pos : 0 < vol
  J_pos : 0 < J
  n_succ_pos : 0 < n + 1
  one_le_N : 1 ≤ N
  half_N_le_j : N / 2 ≤ j
  j_pos : 0 < j
  one_le_La : 1 ≤ La
  log_le_La : log (N + 1) ≤ La

  identity : f * j' * b0 = hh / ((n + 1) * J) - sl + rest / ((n + 1) * vol * J)

  bound_sum : |j * A0 + N * b0| ≤ K1 * N * La

  sl_lower : -(Ca * f * j' * La) ≤ sl

  hh_upper : hh / ((n + 1) * J) ≤ f * j' / 2 * log (N + 1)

  rest_bound : |rest| ≤ Cc * f * j' * (n + 1) * vol * J
def ReductionSmallLast.Statement : Prop :=
  ∀ K1 Ca Cc : ℝ, 0 ≤ K1 → 0 ≤ Ca → 0 ≤ Cc → ∃ C : ℝ,
    ∀ A0 b0 hh sl rest vol J f j' n N j La : ℝ,
      ReductionSmallLast.Hyp K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La → -(C * La) ≤ A0
structure ReductionSmallFirst.Hyp
    (K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La : ℝ) : Prop where
  f_pos : 0 < f
  j'_pos : 0 < j'
  vol_pos : 0 < vol
  J_pos : 0 < J
  n_succ_pos : 0 < n + 1
  one_le_N : 1 ≤ N
  half_N_le : N / 2 ≤ N - j
  sub_pos : 0 < N - j
  one_le_La : 1 ≤ La
  log_le_La : log (N + 1) ≤ La

  identity : f * j' * (A0 + b0) = sl - hh / ((n + 1) * J) - rest / ((n + 1) * vol * J)

  bound_sum : |j * A0 + N * b0| ≤ K1 * N * La

  sl_lower : -(Ca * f * j' * La) ≤ sl

  hh_upper : hh / ((n + 1) * J) ≤ f * j' / 2 * log (N + 1)

  rest_bound : |rest| ≤ Cc * f * j' * (n + 1) * vol * J
def ReductionSmallFirst.Statement : Prop :=
  ∀ K1 Ca Cc : ℝ, 0 ≤ K1 → 0 ≤ Ca → 0 ≤ Cc → ∃ C : ℝ,
    ∀ A0 b0 hh sl rest vol J f j' n N j La : ℝ,
      ReductionSmallFirst.Hyp K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La → -(C * La) ≤ A0
structure InteriorDichotomy.Hyp (C0 C1 C2 h hmu g fj La : ℝ) : Prop where
  one_le_g : 1 ≤ g
  one_le_fj : 1 ≤ fj
  g_le_exp : g ≤ exp La
  one_le_La : 1 ≤ La
  lower : -(fj * (C0 * log (2 + g + max h 0) + C1 * La)) ≤ hmu
  upper : h ≤ 2 * hmu + C2 * g * La
def InteriorDichotomy.Statement : Prop :=
  ∀ C0 C1 C2 : ℝ, 0 ≤ C0 → 0 ≤ C1 → 0 ≤ C2 → ∃ C : ℝ,
    ∀ h hmu g fj La : ℝ, InteriorDichotomy.Hyp C0 C1 C2 h hmu g fj La → -(C * fj * La) ≤ hmu
def AvoidMatrixLemma.Statement : Prop :=
  ∀ a c N x : ℝ, 0 < a → 0 < c → 0 < N → 0 ≤ x →
    -(a * log (c + 2 * a * N)) ≤ x / 2 - a * log (c + N * x)
def firstMinimum {V : Type*} [NormedAddCommGroup V] (L : Submodule ℤ V) : ℝ :=
  sInf {x : ℝ | ∃ v ∈ L, v ≠ 0 ∧ ‖v‖ = x}
def MinkowskiCovolumeBound.Statement : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V], 1 ≤ Module.finrank ℝ V →
    ∀ (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L],
      (firstMinimum L / √(Module.finrank ℝ V : ℝ)) ^ Module.finrank ℝ V ≤ ZLattice.covolume L
structure CuspWeightBound.Hyp (f j' ρ : ℕ) (rd lam NI covol : ℝ) : Prop where
  one_le_f : 1 ≤ f
  one_le_j' : 1 ≤ j'
  one_le_ρ : 1 ≤ ρ
  ρ_le_j' : ρ ≤ j'
  one_le_rd : 1 ≤ rd
  lam_pos : 0 < lam
  NI_pos : 0 < NI
  covol_pos : 0 < covol
  covol_eq : covol = NI * rd ^ (f * ρ)
  minkowski : (lam / √(2 * f * ρ : ℝ)) ^ (2 * f * ρ) ≤ covol
def CuspWeightBound.Statement : Prop :=
  ∀ (f j' ρ : ℕ) (rd lam NI covol : ℝ), CuspWeightBound.Hyp f j' ρ rd lam NI covol →
    -log NI ≤ f * j' * (2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd))
structure ShortVectorsOrthogonal.Hyp {L : Type*} [AddGroup L] (len : L → ℝ)
    (E : L →+ L →+ ℤ) (a : L →+ L) (vr : ℝ) : Prop where
  len_nonneg : ∀ v, 0 ≤ len v
  abs_E_le : ∀ v w, |(E v w : ℝ)| ≤ len v * len w
  len_a_le : ∀ v, len (a v) ≤ vr * len v
  vr_pos : 0 < vr
def ShortVectorsOrthogonal.Statement : Prop :=
  ∀ (L : Type u) [AddGroup L] (len : L → ℝ) (E : L →+ L →+ ℤ) (a : L →+ L) (vr : ℝ),
    ShortVectorsOrthogonal.Hyp len E a vr →
    ∀ v w : L, len v < vr ^ (-(1 / 2 : ℝ)) → len w < vr ^ (-(1 / 2 : ℝ)) → E (a v) w = 0
structure PackingCount.Hyp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : Set V) (W : Submodule ℝ V) (lam r : ℝ) (a : ℕ) : Prop where
  zero_mem : (0 : V) ∈ L
  sub_mem : ∀ x ∈ L, ∀ y ∈ L, x - y ∈ L
  lam_pos : 0 < lam
  lam_le_norm : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖
  finrank_eq : Module.finrank ℝ W = a
  one_le_a : 1 ≤ a
  short_mem : ∀ v ∈ L, ‖v‖ < r → v ∈ W
  lam_le_r : lam ≤ r
def PackingCount.Statement : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (L : Set V)
    (W : Submodule ℝ V) (lam r : ℝ) (a : ℕ), PackingCount.Hyp L W lam r a →
    {v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ < r}.Finite ∧
      ({v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ < r}.ncard : ℝ) ≤ (3 * r / lam) ^ a
def meanCount {X : Type*} [MeasurableSpace X] (μ : Measure X) (cnt : ℝ → X → ℝ) (t : ℝ) : ℝ :=
  ∫ z, cnt t z ∂μ
structure MeanCount.Hyp {X : Type*} [MeasurableSpace X] (μ : Measure X) (lam : X → ℝ)
    (cnt : ℝ → X → ℝ) (a : ℕ) (ka r : ℝ) : Prop where
  isProbability : IsProbabilityMeasure μ
  lam_meas : Measurable lam
  lam_pos : ∀ z, 0 < lam z
  cnt_meas : ∀ t, Measurable (cnt t)
  cnt_nonneg : ∀ t z, 0 ≤ cnt t z
  one_le_a : 1 ≤ a
  three_a_le_ka : 3 * (a : ℝ) ≤ ka
  r_pos : 0 < r
  integrable : ∀ t, 0 < t → Integrable (cnt t) μ
  count : ∀ t, 0 < t → t ≤ r → ∀ z, lam z < t → cnt t z ≤ (3 * t / lam z) ^ a
  zero : ∀ t, 0 < t → ∀ z, t ≤ lam z → cnt t z = 0
  one : ∀ t, 0 < t → t ≤ r → ∀ z, lam z < t → 1 ≤ cnt t z
  scaling : ∀ θ t, 0 < θ → 0 < t → meanCount μ cnt (θ * t) = θ ^ ka * meanCount μ cnt t
def MeanCountBound.Statement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) (lam : X → ℝ) (cnt : ℝ → X → ℝ) (a : ℕ)
    (ka r : ℝ), MeanCount.Hyp μ lam cnt a ka r → meanCount μ cnt r ≤ 2 * 36 ^ a
def TailBound.Statement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) (lam : X → ℝ) (cnt : ℝ → X → ℝ) (a : ℕ)
    (ka r : ℝ), MeanCount.Hyp μ lam cnt a ka r →
    ∀ x : ℝ, 0 ≤ x → μ.real {z | lam z < exp (-x) * r} ≤ min 1 (2 * 36 ^ a * exp (-(ka * x)))
def MeanLogPlus.Statement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) (lam : X → ℝ) (cnt : ℝ → X → ℝ) (a : ℕ)
    (ka r : ℝ), MeanCount.Hyp μ lam cnt a ka r →
    Integrable (fun z => max 0 (log (r / lam z))) μ ∧ ∫ z, max 0 (log (r / lam z)) ∂μ ≤ 3
structure MeanCuspWeight.Hyp {X : Type*} [MeasurableSpace X] (μ : Measure X) (U lam : X → ℝ)
    (f j' : ℕ) (vr rd : ℝ) : Prop where
  isProbability : IsProbabilityMeasure μ
  U_meas : Measurable U
  lam_meas : Measurable lam
  lam_pos : ∀ z, 0 < lam z
  U_nonneg : ∀ z, 0 ≤ U z
  U_le : ∀ z, U z ≤ f * j' * (2 * max 0 (log (1 / lam z)) + log (2 * f * j' * rd))
  one_le_f : 1 ≤ f
  one_le_j' : 1 ≤ j'
  one_le_vr : 1 ≤ vr
  one_le_rd : 1 ≤ rd
  logPlus_integrable : Integrable (fun z => max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z))) μ
  logPlus_mean : ∫ z, max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) ∂μ ≤ 3
def MeanCuspWeight.Statement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) (U lam : X → ℝ) (f j' : ℕ) (vr rd : ℝ),
    MeanCuspWeight.Hyp μ U lam f j' vr rd →
    ∫ z, U z ∂μ ≤ f * j' * (6 + log vr + log (2 * f * j' * rd))
structure TelescopeMetric.Hyp (n : ℕ) (A A' : ℝ) (I : ℕ → ℝ) : Prop where
  sum_eq : A' - A = 1 / 2 * ∑ i ∈ Finset.range (n + 1), I i
  antitone : ∀ i, i < n → I (i + 1) ≤ I i
def TelescopeMetric.Statement : Prop :=
  ∀ (n : ℕ) (A A' : ℝ) (I : ℕ → ℝ), TelescopeMetric.Hyp n A A' I →
    A' - (n + 1) / 2 * I 0 ≤ A
structure LimitInEpsilon.Hyp (n : ℕ) (P Q W : ℝ → ℝ) (W0 e' C1 : ℝ) : Prop where
  P_cont : ContinuousWithinAt P (Set.Ioi 0) 0
  Q_cont : ContinuousWithinAt Q (Set.Ioi 0) 0
  W_lim : Tendsto W (𝓝[>] 0) (𝓝 W0)
  bound : ∀ᶠ ε in 𝓝[>] 0, (n + 1) * ((e' - ε * C1) * Q ε - 1 / 2 * W ε) ≤ P ε
def LimitInEpsilon.Statement : Prop :=
  ∀ (n : ℕ) (P Q W : ℝ → ℝ) (W0 e' C1 : ℝ), LimitInEpsilon.Hyp n P Q W W0 e' C1 →
    (n + 1) * (e' * Q 0 - W0 / 2) ≤ P 0
end
end GroundTheory.Heights₂.Heights.LowerBound


