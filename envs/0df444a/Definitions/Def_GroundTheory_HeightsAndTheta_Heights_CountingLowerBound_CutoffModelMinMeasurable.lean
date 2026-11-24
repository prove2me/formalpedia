-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_CutoffModelMinMeasurable
-- name    : GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_CutoffModelMinMeasurable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:35.206264+00:00
-- url     : https://prove2.me/theorems/a1cef709-f5bc-42a3-a9f2-a3b194337b17
-- title:
--   Cutoff Model Min Measurable
-- statement:
--   Definitions and structural lemmas for Cutoff Model Min Measurable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CountingLowerBound/CutoffModelMinMeasurable.lean

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBound
open MeasureTheory Filter Topology
noncomputable section
universe u
structure ReductionSmallLast.Hyp (K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La : ℝ) : Prop where
  f_pos : 0 < f
  j'_pos : 0 < j'
  vol_pos : 0 < vol
  J_pos : 0 < J
  n_succ_pos : 0 < n + 1
  one_le_N : 1 ≤ N
  half_N_le_j : N / 2 ≤ j
  j_pos : 0 < j
  one_le_La : 1 ≤ La
  log_le_La : Real.log (N + 1) ≤ La
  formula : f * j' * b0 = hh / ((n + 1) * J) - sl + rest / ((n + 1) * vol * J)
  bound_c : |j * A0 + N * b0| ≤ K1 * N * La
  bound_sl : -(Ca * f * j' * La) ≤ sl
  bound_hh : hh / ((n + 1) * J) ≤ f * j' / 2 * Real.log (N + 1)
  bound_rest : |rest| ≤ Cc * f * j' * (n + 1) * vol * J
def ReductionSmallLast.Statement : Prop :=
  ∀ K1 Ca Cc : ℝ, 0 ≤ K1 → 0 ≤ Ca → 0 ≤ Cc → ∃ C : ℝ,
    ∀ A0 b0 hh sl rest vol J f j' n N j La : ℝ,
      ReductionSmallLast.Hyp K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La → -(C * La) ≤ A0
structure ReductionSmallFirst.Hyp (K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La : ℝ) : Prop where
  f_pos : 0 < f
  j'_pos : 0 < j'
  vol_pos : 0 < vol
  J_pos : 0 < J
  n_succ_pos : 0 < n + 1
  one_le_N : 1 ≤ N
  half_N_le : N / 2 ≤ N - j
  sub_pos : 0 < N - j
  one_le_La : 1 ≤ La
  log_le_La : Real.log (N + 1) ≤ La
  formula : f * j' * (A0 + b0) = sl - hh / ((n + 1) * J) - rest / ((n + 1) * vol * J)
  bound_c : |j * A0 + N * b0| ≤ K1 * N * La
  bound_sl : -(Ca * f * j' * La) ≤ sl
  bound_hh : hh / ((n + 1) * J) ≤ f * j' / 2 * Real.log (N + 1)
  bound_rest : |rest| ≤ Cc * f * j' * (n + 1) * vol * J
def ReductionSmallFirst.Statement : Prop :=
  ∀ K1 Ca Cc : ℝ, 0 ≤ K1 → 0 ≤ Ca → 0 ≤ Cc → ∃ C : ℝ,
    ∀ A0 b0 hh sl rest vol J f j' n N j La : ℝ,
      ReductionSmallFirst.Hyp K1 Ca Cc A0 b0 hh sl rest vol J f j' n N j La → -(C * La) ≤ A0
structure InteriorDichotomy.Hyp (C0 C1 C2 h hmu g fj La : ℝ) : Prop where
  one_le_g : 1 ≤ g
  one_le_fj : 1 ≤ fj
  g_le_exp : g ≤ Real.exp La
  one_le_La : 1 ≤ La
  lower : -(fj * (C0 * Real.log (2 + g + max h 0) + C1 * La)) ≤ hmu
  upper : h ≤ 2 * hmu + C2 * g * La
def InteriorDichotomy.Statement : Prop :=
  ∀ C0 C1 C2 : ℝ, 0 ≤ C0 → 0 ≤ C1 → 0 ≤ C2 → ∃ C : ℝ,
    ∀ h hmu g fj La : ℝ, InteriorDichotomy.Hyp C0 C1 C2 h hmu g fj La → -(C * fj * La) ≤ hmu
structure AvoidMatrixLemma.Hyp (a c N x : ℝ) : Prop where
  a_pos : 0 < a
  c_pos : 0 < c
  N_pos : 0 < N
  x_nonneg : 0 ≤ x
def AvoidMatrixLemma.Statement : Prop :=
  ∀ a c N x : ℝ, AvoidMatrixLemma.Hyp a c N x →
    -(a * Real.log (c + 2 * a * N)) ≤ x / 2 - a * Real.log (c + N * x)
def shortestLength {V : Type*} [NormedAddCommGroup V] (L : Submodule ℤ V) : ℝ :=
  sInf ((fun v : V => ‖v‖) '' {v : V | v ∈ L ∧ v ≠ 0})
def MinkowskiCovolumeBound.Statement : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L],
    1 ≤ Module.finrank ℝ V →
      (shortestLength L / Real.sqrt (Module.finrank ℝ V)) ^ Module.finrank ℝ V ≤
        ZLattice.covolume L
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
  minkowski : (lam / Real.sqrt (2 * f * ρ : ℝ)) ^ (2 * f * ρ) ≤ covol
def CuspWeightBound.Statement : Prop :=
  ∀ (f j' ρ : ℕ) (rd lam NI covol : ℝ), CuspWeightBound.Hyp f j' ρ rd lam NI covol →
    -Real.log NI ≤
      (f : ℝ) * j' * (2 * max 0 (Real.log (1 / lam)) + Real.log (2 * f * j' * rd))
structure ShortVectorsOrthogonal.Hyp {L : Type*} [AddGroup L] (len : L → ℝ) (E : L →+ L →+ ℤ)
    (a : L →+ L) (vr : ℝ) : Prop where
  len_nonneg : ∀ v, 0 ≤ len v
  form_le : ∀ v w, |(E v w : ℝ)| ≤ len v * len w
  map_le : ∀ v, len (a v) ≤ vr * len v
  vr_pos : 0 < vr
def ShortVectorsOrthogonal.Statement : Prop :=
  ∀ (L : Type u) [AddGroup L] (len : L → ℝ) (E : L →+ L →+ ℤ) (a : L →+ L) (vr : ℝ),
    ShortVectorsOrthogonal.Hyp len E a vr →
      ∀ v w : L, len v < vr ^ (-(1 / 2 : ℝ)) → len w < vr ^ (-(1 / 2 : ℝ)) → E (a v) w = 0
structure PackingCount.Hyp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : Set V) (lam : ℝ) (W : Submodule ℝ V) (a : ℕ) (r : ℝ) : Prop where
  zero_mem : (0 : V) ∈ L
  sub_mem : ∀ v ∈ L, ∀ w ∈ L, v - w ∈ L
  lam_pos : 0 < lam
  lam_le : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖
  finrank_eq : Module.finrank ℝ W = a
  one_le_a : 1 ≤ a
  short_mem : ∀ v ∈ L, ‖v‖ < r → v ∈ W
  lam_le_r : lam ≤ r
def PackingCount.Statement : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (L : Set V) (lam : ℝ)
    (W : Submodule ℝ V) (a : ℕ) (r : ℝ), PackingCount.Hyp L lam W a r →
      {v : V | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ < r}.Finite ∧
        (({v : V | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ < r}.ncard : ℕ) : ℝ) ≤ (3 * r / lam) ^ a
def meanCount {X : Type*} [MeasurableSpace X] (μ : Measure X) (cnt : ℝ → X → ℝ) (t : ℝ) : ℝ :=
  ∫ z, cnt t z ∂μ
structure MeanCountBound.Hyp {X : Type*} [MeasurableSpace X] (μ : Measure X) (lam : X → ℝ)
    (cnt : ℝ → X → ℝ) (a : ℕ) (ka : ℝ) : Prop where
  lam_meas : Measurable lam
  lam_pos : ∀ z, 0 < lam z
  cnt_meas : ∀ t, Measurable (cnt t)
  cnt_nonneg : ∀ t z, 0 ≤ cnt t z
  one_le_a : 1 ≤ a
  three_a_le_ka : 3 * (a : ℝ) ≤ ka
  integrable : ∀ t, 0 < t → Integrable (cnt t) μ
  count_le : ∀ t, 0 < t → ∀ z, lam z < t → cnt t z ≤ (3 * t / lam z) ^ a
  count_zero : ∀ t, 0 < t → ∀ z, t ≤ lam z → cnt t z = 0
  one_le_cnt : ∀ t z, lam z < t → 1 ≤ cnt t z
  scaling : ∀ θ t, 0 < θ → 0 < t → meanCount μ cnt (θ * t) = θ ^ ka * meanCount μ cnt t
def MeanCountBound.Statement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (lam : X → ℝ)
    (cnt : ℝ → X → ℝ) (a : ℕ) (ka : ℝ), MeanCountBound.Hyp μ lam cnt a ka →
      ∀ r : ℝ, 0 < r → meanCount μ cnt r ≤ 2 * 36 ^ a
def TailBound.Statement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (lam : X → ℝ)
    (cnt : ℝ → X → ℝ) (a : ℕ) (ka : ℝ), MeanCountBound.Hyp μ lam cnt a ka →
      ∀ r x : ℝ, 0 < r → 0 ≤ x →
        μ.real {z | lam z < Real.exp (-x) * r} ≤ min 1 (2 * 36 ^ a * Real.exp (-(ka * x)))
def MeanLogPlus.Statement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (lam : X → ℝ)
    (cnt : ℝ → X → ℝ) (a : ℕ) (ka : ℝ), MeanCountBound.Hyp μ lam cnt a ka →
      ∀ r : ℝ, 0 < r →
        Integrable (fun z => max 0 (Real.log (r / lam z))) μ ∧
          ∫ z, max 0 (Real.log (r / lam z)) ∂μ ≤ 3
structure MeanCountBoundUpTo.Hyp {X : Type*} [MeasurableSpace X] (μ : Measure X) (lam : X → ℝ)
    (cnt : ℝ → X → ℝ) (a : ℕ) (ka R : ℝ) : Prop where
  R_pos : 0 < R
  lam_meas : Measurable lam
  lam_pos : ∀ z, 0 < lam z
  cnt_meas : ∀ t, Measurable (cnt t)
  cnt_nonneg : ∀ t z, 0 ≤ cnt t z
  one_le_a : 1 ≤ a
  three_a_le_ka : 3 * (a : ℝ) ≤ ka
  integrable : ∀ t, 0 < t → Integrable (cnt t) μ
  count_le : ∀ t, 0 < t → t ≤ R → ∀ z, lam z < t → cnt t z ≤ (3 * t / lam z) ^ a
  count_zero : ∀ t, 0 < t → ∀ z, t ≤ lam z → cnt t z = 0
  one_le_cnt : ∀ t, t ≤ R → ∀ z, lam z < t → 1 ≤ cnt t z
  scaling : ∀ θ t, 0 < θ → 0 < t → meanCount μ cnt (θ * t) = θ ^ ka * meanCount μ cnt t
def MeanCountBoundUpTo.Statement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (lam : X → ℝ)
    (cnt : ℝ → X → ℝ) (a : ℕ) (ka R : ℝ), MeanCountBoundUpTo.Hyp μ lam cnt a ka R →
      ∀ r : ℝ, 0 < r → r ≤ R → meanCount μ cnt r ≤ 2 * 36 ^ a
def TailBoundUpTo.Statement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (lam : X → ℝ)
    (cnt : ℝ → X → ℝ) (a : ℕ) (ka R : ℝ), MeanCountBoundUpTo.Hyp μ lam cnt a ka R →
      ∀ r x : ℝ, 0 < r → r ≤ R → 0 ≤ x →
        μ.real {z | lam z < Real.exp (-x) * r} ≤ min 1 (2 * 36 ^ a * Real.exp (-(ka * x)))
def MeanLogPlusUpTo.Statement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (lam : X → ℝ)
    (cnt : ℝ → X → ℝ) (a : ℕ) (ka R : ℝ), MeanCountBoundUpTo.Hyp μ lam cnt a ka R →
      ∀ r : ℝ, 0 < r → r ≤ R →
        Integrable (fun z => max 0 (Real.log (r / lam z))) μ ∧
          ∫ z, max 0 (Real.log (r / lam z)) ∂μ ≤ 3
structure MeanCuspWeight.Hyp {X : Type*} [MeasurableSpace X] (μ : Measure X) (U lam : X → ℝ)
    (f j' : ℕ) (rd vr : ℝ) : Prop where
  U_meas : Measurable U
  lam_meas : Measurable lam
  lam_pos : ∀ z, 0 < lam z
  U_nonneg : ∀ z, 0 ≤ U z
  one_le_f : 1 ≤ f
  one_le_j' : 1 ≤ j'
  one_le_rd : 1 ≤ rd
  one_le_vr : 1 ≤ vr
  U_le : ∀ z, U z ≤ (f : ℝ) * j' * (2 * max 0 (Real.log (1 / lam z)) + Real.log (2 * f * j' * rd))
  integrable : Integrable (fun z => max 0 (Real.log (vr ^ (-(1 / 2 : ℝ)) / lam z))) μ
  mean_le : ∫ z, max 0 (Real.log (vr ^ (-(1 / 2 : ℝ)) / lam z)) ∂μ ≤ 3
def MeanCuspWeight.Statement : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (U lam : X → ℝ)
    (f j' : ℕ) (rd vr : ℝ), MeanCuspWeight.Hyp μ U lam f j' rd vr →
      Integrable U μ ∧
        ∫ z, U z ∂μ ≤ (f : ℝ) * j' * (6 + Real.log vr + Real.log (2 * f * j' * rd))
structure TelescopeMetric.Hyp (n : ℕ) (A A' : ℝ) (I : ℕ → ℝ) : Prop where
  telescope : A' - A = (1 / 2) * ∑ i ∈ Finset.range (n + 1), I i
  antitone : ∀ i, I (i + 1) ≤ I i
def TelescopeMetric.Statement : Prop :=
  ∀ (n : ℕ) (A A' : ℝ) (I : ℕ → ℝ), TelescopeMetric.Hyp n A A' I →
    A' - ((n + 1 : ℝ) / 2) * I 0 ≤ A
structure LimitInEpsilon.Hyp (n : ℕ) (P Q W : ℝ → ℝ) (W0 e' C1 : ℝ) : Prop where
  P_cont : ContinuousWithinAt P (Set.Ioi 0) 0
  Q_cont : ContinuousWithinAt Q (Set.Ioi 0) 0
  W_tendsto : Tendsto W (𝓝[>] 0) (𝓝 W0)
  ineq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ((n : ℝ) + 1) * ((e' - ε * C1) * Q ε - (1 / 2) * W ε) ≤ P ε
def LimitInEpsilon.Statement : Prop :=
  ∀ (n : ℕ) (P Q W : ℝ → ℝ) (W0 e' C1 : ℝ), LimitInEpsilon.Hyp n P Q W W0 e' C1 →
    ((n : ℝ) + 1) * (e' * Q 0 - W0 / 2) ≤ P 0
lemma one_le_log_three : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
  have := Real.exp_one_lt_d9
  linarith
lemma log_three_le_two : Real.log 3 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3)]
  have := Real.add_one_le_exp (2 : ℝ)
  linarith
example : ReductionSmallLast.Hyp 1 1 1 1 (1 / 2) 1 1 2 1 1 1 1 1 2 1 2 where
  f_pos := by norm_num
  j'_pos := by norm_num
  vol_pos := by norm_num
  J_pos := by norm_num
  n_succ_pos := by norm_num
  one_le_N := by norm_num
  half_N_le_j := by norm_num
  j_pos := by norm_num
  one_le_La := by norm_num
  log_le_La := by norm_num; exact log_three_le_two
  formula := by norm_num
  bound_c := by norm_num [abs_of_pos]
  bound_sl := by norm_num
  bound_hh := by norm_num; linarith [one_le_log_three]
  bound_rest := by norm_num
example : ReductionSmallFirst.Hyp 1 1 1 1 (-1 / 2) 1 1 0 1 1 1 1 1 2 1 2 where
  f_pos := by norm_num
  j'_pos := by norm_num
  vol_pos := by norm_num
  J_pos := by norm_num
  n_succ_pos := by norm_num
  one_le_N := by norm_num
  half_N_le := by norm_num
  sub_pos := by norm_num
  one_le_La := by norm_num
  log_le_La := by norm_num; exact log_three_le_two
  formula := by norm_num
  bound_c := by norm_num
  bound_sl := by norm_num
  bound_hh := by norm_num; linarith [one_le_log_three]
  bound_rest := by norm_num
example : InteriorDichotomy.Hyp 1 1 1 (-5) (-1) 1 1 1 where
  one_le_g := le_rfl
  one_le_fj := le_rfl
  g_le_exp := Real.one_le_exp zero_le_one
  one_le_La := le_rfl
  lower := by
    have : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    norm_num
    linarith
  upper := by norm_num
example : AvoidMatrixLemma.Hyp 2 3 5 7 := ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
example :
    DiscreteTopology (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)) ∧
      IsZLattice ℝ (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)) ∧
      1 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨inferInstance, inferInstance, by simp⟩
example : CuspWeightBound.Hyp 1 1 1 2 (1 / 2) 2 4 where
  one_le_f := le_rfl
  one_le_j' := le_rfl
  one_le_ρ := le_rfl
  ρ_le_j' := le_rfl
  one_le_rd := by norm_num
  lam_pos := by norm_num
  NI_pos := by norm_num
  covol_pos := by norm_num
  covol_eq := by norm_num
  minkowski := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
example : ShortVectorsOrthogonal.Hyp (fun v : ℤ => |(v : ℝ)|) (AddMonoidHom.mul : ℤ →+ ℤ →+ ℤ)
    (AddMonoidHom.mulLeft (2 : ℤ)) 2 where
  len_nonneg _ := abs_nonneg _
  form_le v w := by simp [abs_mul]
  map_le v := by simp [abs_mul]
  vr_pos := by norm_num
example : PackingCount.Hyp (Set.range (Int.cast : ℤ → ℝ)) 1 ⊤ 1 2 where
  zero_mem := ⟨0, by simp⟩
  sub_mem := by
    rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
    exact ⟨k - l, by push_cast; ring⟩
  lam_pos := by norm_num
  lam_le := by
    rintro _ ⟨k, rfl⟩ hk
    have hk' : k ≠ 0 := by rintro rfl; simp at hk
    rw [Real.norm_eq_abs, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hk'
  finrank_eq := by simp
  one_le_a := le_rfl
  short_mem _ _ _ := Submodule.mem_top
  lam_le_r := by norm_num
def cutoffModelMeasure : Measure ℝ := volume.restrict (Set.Ioc 0 1)
instance : IsProbabilityMeasure cutoffModelMeasure :=
  ⟨by simp [cutoffModelMeasure]⟩
def cutoffModelMin (x : ℝ) : ℝ := if 0 < x then x ^ ((3 : ℝ)⁻¹) else 1
def cutoffModelCount (t x : ℝ) : ℝ :=
  if cutoffModelMin x < t then (if t ≤ 1 then 1 else t ^ 3) else 0
lemma cutoffModelMin_measurable : Measurable cutoffModelMin :=
  Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const
lemma cutoffModelMin_pos (x : ℝ) : 0 < cutoffModelMin x := by
  unfold cutoffModelMin
  split_ifs with h
  · exact Real.rpow_pos_of_pos h _
  · exact one_pos
lemma cutoffModelMin_lt_iff {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    cutoffModelMin x < t ↔ x < t ^ 3 := by
  rw [cutoffModelMin, if_pos hx]
  have h0 : 0 ≤ x ^ ((3 : ℝ)⁻¹) := Real.rpow_nonneg hx.le _
  rw [← pow_lt_pow_iff_left₀ h0 ht.le (by norm_num : (3 : ℕ) ≠ 0)]
  have h3 : (x ^ ((3 : ℝ)⁻¹)) ^ 3 = x := by
    have := Real.rpow_inv_natCast_pow hx.le (n := 3) (by norm_num)
    simpa using this
  rw [h3]
lemma cutoffModelCount_eq (t : ℝ) :
    cutoffModelCount t = Set.indicator {x | cutoffModelMin x < t} (fun _ => if t ≤ 1 then 1 else t ^ 3) := by
  funext x
  simp only [cutoffModelCount, Set.indicator_apply, Set.mem_ofPred_eq]
lemma cutoffModel_set_meas (t : ℝ) : MeasurableSet {x | cutoffModelMin x < t} :=
  measurableSet_lt cutoffModelMin_measurable measurable_const
lemma cutoffModel_meanCount {t : ℝ} (ht : 0 < t) :
    meanCount cutoffModelMeasure cutoffModelCount t = t ^ 3 := by
  rw [meanCount, cutoffModelCount_eq, integral_indicator_const _ (cutoffModel_set_meas t),
    smul_eq_mul, measureReal_def, cutoffModelMeasure,
    Measure.restrict_apply (cutoffModel_set_meas t)]
  by_cases h1 : t ≤ 1
  · have hset : {x | cutoffModelMin x < t} ∩ Set.Ioc 0 1 = Set.Ioo 0 (t ^ 3) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc, Set.mem_Ioo]
      constructor
      · rintro ⟨h, hx0, -⟩
        exact ⟨hx0, (cutoffModelMin_lt_iff hx0 ht).1 h⟩
      · rintro ⟨hx0, hx⟩
        exact ⟨(cutoffModelMin_lt_iff hx0 ht).2 hx, hx0,
          hx.le.trans (pow_le_one₀ ht.le h1)⟩
    rw [hset, Real.volume_Ioo, if_pos h1, sub_zero, ENNReal.toReal_ofReal (by positivity), mul_one]
  · have h1' : 1 < t := lt_of_not_ge h1
    have hset : {x | cutoffModelMin x < t} ∩ Set.Ioc 0 1 = Set.Ioc 0 1 := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc]
      constructor
      · rintro ⟨-, h⟩
        exact h
      · rintro ⟨hx0, hx1⟩
        exact ⟨(cutoffModelMin_lt_iff hx0 ht).2 (hx1.trans_lt (one_lt_pow₀ h1' (by norm_num))),
          hx0, hx1⟩
    rw [hset, Real.volume_Ioc, if_neg h1]
    norm_num
example : MeanCountBoundUpTo.Hyp cutoffModelMeasure cutoffModelMin cutoffModelCount 1 3 1 where
  R_pos := one_pos
  lam_meas := cutoffModelMin_measurable
  lam_pos := cutoffModelMin_pos
  cnt_meas t := by
    rw [cutoffModelCount_eq]
    exact measurable_const.indicator (cutoffModel_set_meas t)
  cnt_nonneg t z := by
    unfold cutoffModelCount
    split_ifs with h1 h2
    · norm_num
    · exact pow_nonneg (by linarith) 3
    · exact le_rfl
  one_le_a := le_rfl
  three_a_le_ka := by norm_num
  integrable t _ := by
    rw [cutoffModelCount_eq]
    exact (integrable_const _).indicator (cutoffModel_set_meas t)
  count_le t ht htR z hz := by
    simp only [cutoffModelCount, if_pos hz, if_pos htR, pow_one]
    rw [le_div_iff₀ (cutoffModelMin_pos z)]
    linarith
  count_zero t _ z hz := by
    simp [cutoffModelCount, not_lt.2 hz]
  one_le_cnt t htR z hz := by
    simp [cutoffModelCount, hz, htR]
  scaling θ t hθ ht := by
    rw [cutoffModel_meanCount (mul_pos hθ ht), cutoffModel_meanCount ht,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
example : MeanCuspWeight.Hyp cutoffModelMeasure (fun _ => Real.log 2) (fun _ => 1 / 2) 1 1 1 1 where
  U_meas := measurable_const
  lam_meas := measurable_const
  lam_pos _ := by norm_num
  U_nonneg _ := Real.log_nonneg one_le_two
  one_le_f := le_rfl
  one_le_j' := le_rfl
  one_le_rd := le_rfl
  one_le_vr := le_rfl
  U_le _ := by
    have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
    norm_num [max_eq_right h2]
    linarith
  integrable := integrable_const _
  mean_le := by
    have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
    rw [integral_const]
    norm_num [max_eq_right h2]
    linarith [Real.log_two_lt_d9]
example : TelescopeMetric.Hyp 1 (1 / 4) 1 (fun i => 1 / ((i : ℝ) + 1)) where
  telescope := by
    simp [Finset.sum_range_succ]
    norm_num
  antitone i := by
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    linarith
example : LimitInEpsilon.Hyp 0 (fun ε => 1 + ε) (fun _ => 1) (fun _ => 0) 0 1 1 where
  P_cont := (continuous_const.add continuous_id).continuousWithinAt
  Q_cont := continuousWithinAt_const
  W_tendsto := tendsto_const_nhds
  ineq := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have : 0 < ε := Set.mem_Ioi.1 hε
    norm_num
    linarith
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBound


