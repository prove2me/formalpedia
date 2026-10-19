-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
-- name    : OAI_Analysis_C0Absorption_Coordinates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:01:21.294989+00:00
-- url     : https://prove2.me/theorems/d3aa9156-3feb-4b4c-9c27-34c3d12e1254
-- title:
--   Coordinates, cubes, grids and tails in c0
-- statement:
--   $c_0$ is the Banach space of real sequences tending to zero with the sup norm, $B$ is its closed unit ball, and for a finite set $I$ of coordinates the cube $[-1,1]^I$ is the image of $B$ under restriction to $I$.
--
--   1. **Coordinates.** Evaluation at $i$ is a continuous linear functional of norm at most $1$. The unit vectors $e_i$ span a dense subspace, so $c_0$ is separable. Truncations $\sum_{i<N}s_ie_i$ converge to $s$.
--   2. **Cubes.** Restriction $B\to[-1,1]^I$ and extension by zero $[-1,1]^I\to B$ are $1$-Lipschitz, and restriction after extension is the identity.
--   3. **Grids.** For $n>0$ the grid $\{k/n:|k|\le n\}$ in $[-1,1]$ is within $\frac1{2n}$ of every point. The operation grid at scale index $a$ uses $n=2^{a+3}$ in each coordinate of $I$, and $\mathrm{dyadic}(a)=2^{-a}$.
--   4. **Tails.** $\mathrm{tail}_N(s)=(s_i)_{i>N}$ and $\tau_N(s)=\|\mathrm{tail}_N(s)\|$, which is $1$-Lipschitz, at most $\|s\|$, and tends to $0$ as $N\to\infty$.
--   5. **Tail factor.**
--   $$
--   \mathrm{tailFactor}(c,N,s)=\min\bigl(1,\max(2-\tau_N(s)/c,0)\bigr),
--   $$
--   which is $1$ when $\tau_N(s)\le c$ and $0$ when $\tau_N(s)\ge2c$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Coordinates.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Coordinates.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the C0Absorption mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace C0Absorption
noncomputable section

abbrev C0Ball := Metric.closedBall (0 : C0) 1

abbrev Cube (I : Finset ℕ) := (i : I) → Icc (-1 : ℝ) 1

theorem c0_norm_apply_le (s : C0) (i : ℕ) : |s i| ≤ ‖s‖ := by
  exact s.toBCF.norm_coe_le_norm i

theorem c0_norm_le (s : C0) {a : ℝ} (ha : 0 ≤ a) (hs : ∀ i, |s i| ≤ a) : ‖s‖ ≤ a := by
  exact (s.toBCF.norm_le ha).mpr hs

def c0Eval (i : ℕ) : C0 →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun s : C0 => s i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (fun s => by simpa using c0_norm_apply_le s i)

@[simp] theorem c0Eval_apply (i : ℕ) (s : C0) : c0Eval i s = s i := rfl

def cubeRestrict (I : Finset ℕ) (s : C0Ball) : Cube I := fun i =>
  ⟨s.val i, by
    have hnorm : ‖s.val‖ ≤ 1 := by
      have hh := s.property
      change dist s.val 0 ≤ 1 at hh
      rwa [dist_zero_right] at hh
    exact abs_le.mp ((c0_norm_apply_le s.val i).trans hnorm)⟩

def finsuppToC0 (f : ℕ →₀ ℝ) : C0 where
  toFun := f
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := (HasCompactSupport.of_support_subset_isCompact
    f.hasFiniteSupport.isCompact (Set.Subset.refl _)).is_zero_at_infty

@[simp] theorem finsuppToC0_apply (f : ℕ →₀ ℝ) (i : ℕ) : finsuppToC0 f i = f i := rfl

def atom (i : ℕ) : C0 := finsuppToC0 (Finsupp.single i 1)

@[simp] theorem atom_apply (i j : ℕ) : atom i j = if i=j then 1 else 0 := by
  simp [atom, Finsupp.single_apply]

@[simp] theorem atom_norm (i : ℕ) : ‖atom i‖ = 1 := by
  apply le_antisymm
  · apply c0_norm_le _ zero_le_one
    intro j
    simp only [atom_apply]
    split <;> norm_num
  · simpa using c0_norm_apply_le (atom i) i

def truncate (N : ℕ) (s : C0) : C0 := ∑ i ∈ Finset.range N, s i • atom i

@[simp] theorem truncate_apply (N : ℕ) (s : C0) (i : ℕ) :
    truncate N s i = if i < N then s i else 0 := by
  classical
  change c0Eval i (∑ j ∈ Finset.range N, s j • atom j) = _
  simp only [map_sum, map_smul, smul_eq_mul, c0Eval_apply, atom_apply]
  by_cases hi : i < N
  · rw [ite_eq_left hi, Finset.sum_eq_single i]
    · simp
    · intro j hj hji; simp [hji]
    · intro hnot; exact (hnot (Finset.mem_range.mpr hi)).elim
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    have hji : j ≠ i := by intro h; subst j; exact hi (Finset.mem_range.mp hj)
    simp [hji]

theorem c0_tendsto_zero (s : C0) : Tendsto s atTop (nhds 0) := by
  simpa only [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using zero_at_infty s

theorem truncate_tendsto (s : C0) : Tendsto (fun N => truncate N s) atTop (nhds s) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he : ∀ᶠ i in atTop, |s i| < ε/2 := by
    simpa only [Real.dist_eq, sub_zero] using
      (Metric.tendsto_nhds.mp (c0_tendsto_zero s) (ε/2) (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ?_ (half_lt_self hε)
  apply c0_norm_le _ (by positivity : 0 ≤ ε/2)
  intro i
  simp only [ZeroAtInftyContinuousMap.sub_apply, truncate_apply]
  by_cases hi : i < n
  · simp [hi]; positivity
  · simp only [ite_eq_right hi, zero_sub, abs_neg]
    exact (hN i (hn.trans (Nat.le_of_not_gt hi))).le

theorem truncate_mem_span (N : ℕ) (s : C0) :
    truncate N s ∈ Submodule.span ℝ (Set.range atom) := by
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem c0_span_dense : Dense (↑(Submodule.span ℝ (Set.range atom)) : Set C0) := by
  intro s
  exact mem_closure_of_tendsto (truncate_tendsto s)
    (Filter.Eventually.of_forall (fun N => truncate_mem_span N s))

instance c0_separable : TopologicalSpace.SeparableSpace C0 := by
  apply TopologicalSpace.isSeparable_univ_iff.mp
  have hh := (Set.countable_range atom).isSeparable.span (R := ℝ)
  rw [← c0_span_dense.closure_eq]
  exact hh.closure

def extendFinite (I : Finset ℕ) (x : I → ℝ) : C0 := by
  classical
  exact finsuppToC0 (Finsupp.onFinset I (fun j => if h : j ∈ I then x ⟨j,h⟩ else 0)
    (by intro j hj; by_contra h; simp [h] at hj))

@[simp] theorem extendFinite_apply (I : Finset ℕ) (x : I → ℝ) (j : ℕ) :
    extendFinite I x j = if h : j ∈ I then x ⟨j,h⟩ else 0 := by
  classical
  rfl

theorem extendFinite_norm_le (I : Finset ℕ) (x : I → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hx : ∀ i, |x i| ≤ a) : ‖extendFinite I x‖ ≤ a := by
  classical
  apply c0_norm_le _ ha
  intro j
  rw [extendFinite_apply]
  split
  · exact hx _
  · simpa using ha

def cubeExtend (I : Finset ℕ) (x : Cube I) : C0Ball :=
  ⟨extendFinite I (fun i => (x i).val), by
    rw [Metric.mem_closedBall, dist_zero_right]
    apply extendFinite_norm_le _ _ zero_le_one
    intro i
    exact abs_le.mpr (x i).property⟩

@[simp] theorem cubeRestrict_extend (I : Finset ℕ) (x : Cube I) :
    cubeRestrict I (cubeExtend I x) = x := by
  classical
  ext i
  change extendFinite I (fun i => (x i).val) i = (x i).val
  simp

theorem cubeRestrict_lipschitz (I : Finset ℕ) : LipschitzWith 1 (cubeRestrict I) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  change dist (s.val i) (t.val i) ≤ dist s.val t.val
  exact BoundedContinuousFunction.dist_coe_le_dist (f := s.val.toBCF) (g := t.val.toBCF) i

theorem cubeExtend_lipschitz (I : Finset ℕ) : LipschitzWith 1 (cubeExtend I) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm]
  apply c0_norm_le _ dist_nonneg
  intro j
  change |extendFinite I (fun i => (s i).val) j-extendFinite I (fun i => (t i).val) j| ≤ dist s t
  simp only [extendFinite_apply]
  split
  · exact dist_le_pi_dist s t _
  · simp

abbrev GridIndex (n : ℕ) := Icc (-(n : ℤ)) (n : ℤ)

def gridPoint (n : ℕ) (hn : 0 < n) (z : GridIndex n) : Icc (-1 : ℝ) 1 :=
  ⟨(z.val : ℝ) / n, by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hl : -(n : ℝ) ≤ (z.val : ℝ) := by exact_mod_cast z.property.1
    have hu : (z.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast z.property.2
    constructor
    · apply (le_div_iff₀ hn').mpr; simpa using hl
    · apply (div_le_iff₀ hn').mpr; simpa using hu⟩

def nearestGridIndex (n : ℕ) (_hn : 0 < n) (x : Icc (-1 : ℝ) 1) : GridIndex n :=
  ⟨round ((n : ℝ) * x.val), by
    have hb := abs_le.mp (abs_sub_round ((n : ℝ) * x.val))
    have hxlo : -(n : ℝ) ≤ (n : ℝ) * x.val := by nlinarith [x.property.1, Nat.cast_nonneg (α := ℝ) n]
    have hxhi : (n : ℝ) * x.val ≤ n := by nlinarith [x.property.2, Nat.cast_nonneg (α := ℝ) n]
    constructor
    · by_contra h
      have hh : round ((n : ℝ) * x.val) ≤ -(n : ℤ)-1 := by omega
      have hh' : (round ((n : ℝ) * x.val) : ℝ) ≤ -(n : ℝ)-1 := by exact_mod_cast hh
      linarith
    · by_contra h
      have hh : (n : ℤ)+1 ≤ round ((n : ℝ) * x.val) := by omega
      have hh' : (n : ℝ)+1 ≤ (round ((n : ℝ) * x.val) : ℝ) := by exact_mod_cast hh
      linarith⟩

theorem nearestGrid_dist (n : ℕ) (hn : 0 < n) (x : Icc (-1 : ℝ) 1) :
    dist x (gridPoint n hn (nearestGridIndex n hn x)) ≤ 1 / (2*(n : ℝ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  change |x.val - (round ((n : ℝ)*x.val) : ℝ)/(n : ℝ)| ≤ _
  rw [show x.val - (round ((n : ℝ)*x.val) : ℝ)/(n : ℝ) =
    ((n : ℝ)*x.val-(round ((n : ℝ)*x.val) : ℝ))/(n : ℝ) by field_simp,
    abs_div, abs_of_pos hn', div_le_iff₀ hn']
  have hb := abs_sub_round ((n : ℝ)*x.val)
  have he : 1 / (2*(n : ℝ)) * (n : ℝ) = (1 : ℝ)/2 := by field_simp
  rwa [he]

def dyadic (a : ℕ) : ℝ := ((2 : ℝ)^a)⁻¹

theorem dyadic_pos (a : ℕ) : 0 < dyadic a := by unfold dyadic; positivity

abbrev OperationGrid (I : Finset ℕ) (a : ℕ) := I → GridIndex (2^(a+3))

def operationGridPoint (I : Finset ℕ) (a : ℕ) (q : OperationGrid I a) : Cube I :=
  fun i => gridPoint _ (by positivity) (q i)

def nearestOperationGrid (I : Finset ℕ) (a : ℕ) (x : Cube I) : OperationGrid I a :=
  fun i => nearestGridIndex _ (by positivity) (x i)

def coordinateTail (N : ℕ) (s : C0) : C0 := s - truncate (N+1) s

@[simp] theorem coordinateTail_apply (N : ℕ) (s : C0) (i : ℕ) :
    coordinateTail N s i = if N < i then s i else 0 := by
  simp only [coordinateTail, ZeroAtInftyContinuousMap.sub_apply, truncate_apply]
  split_ifs <;> simp_all; omega

def tau (N : ℕ) (s : C0) : ℝ := ‖coordinateTail N s‖

theorem tau_nonneg (N : ℕ) (s : C0) : 0 ≤ tau N s := norm_nonneg _

theorem coordinateTail_sub (N : ℕ) (s t : C0) :
    coordinateTail N (s-t) = coordinateTail N s-coordinateTail N t := by
  ext i
  simp only [coordinateTail_apply, ZeroAtInftyContinuousMap.sub_apply]
  split_ifs <;> simp

theorem tau_le_norm (N : ℕ) (s : C0) : tau N s ≤ ‖s‖ := by
  apply c0_norm_le _ (norm_nonneg s)
  intro i
  rw [coordinateTail_apply]
  split_ifs
  · exact c0_norm_apply_le s i
  · simp

theorem tau_lipschitz (N : ℕ) : LipschitzWith 1 (tau N) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [NNReal.coe_one, one_mul, Real.dist_eq]
  calc
    |tau N s-tau N t| ≤ ‖coordinateTail N s-coordinateTail N t‖ := abs_norm_sub_norm_le _ _
    _ = tau N (s-t) := by rw [tau, coordinateTail_sub]
    _ ≤ ‖s-t‖ := tau_le_norm _ _
    _ = dist s t := (dist_eq_norm _ _).symm

theorem tau_tendsto_zero (s : C0) : Tendsto (fun N => tau N s) atTop (nhds 0) := by
  have hh := ((show Tendsto (fun _ : ℕ => s) atTop (nhds s) from tendsto_const_nhds).sub (truncate_tendsto s)).norm
  have hshift : Tendsto (fun N : ℕ => N+1) atTop atTop := tendsto_add_atTop_nat 1
  simpa [Function.comp_def, tau, coordinateTail] using hh.comp hshift

def tailFactor (c : ℝ) (N : ℕ) (s : C0) : ℝ := min 1 (max (2-tau N s/c) 0)

end
end C0Absorption

end OAI


