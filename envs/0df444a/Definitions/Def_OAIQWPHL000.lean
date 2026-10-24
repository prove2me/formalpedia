-- Prove2me | Definitions.Def_OAIQWPHL000
-- name    : OAIQWPHL000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T16:49:40.244397+00:00
-- url     : https://prove2.me/theorems/dc385e77-4479-455d-a80a-af9ab7dd3f0d
-- title:
--   OpenAI planar halving-lines split: definitions bundle OAIQWPHL000
-- statement:
--   The definitions bundle of the split of OpenAI's proof of `OAI.PlanarHalving.power_bounds`: there are $\varepsilon > 0$ and $C$ such that every $n$-point set in general position, $n$ even and large, has at most $C n^{4/3-\varepsilon}$ halving lines, and every generic $n$-point set has at most $C n^{4/3-\varepsilon}$ switches at every rank. The bundle holds OpenAI's Lean definitions from the modules listed below of `lean/OAI/Combinatorics/HalvingLines` (OpenAI, *A power saving for planar halving lines*, OpenAI Math Release, September 25, 2026, result family 183, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. It also holds the lemmas these definitions use in their bodies, and OpenAI's `@[simp]` lemmas about them.
--
--   Among them: straight-line drawings and their crossings (`PlaneGraph.Drawing`, `PlaneGraph.Crosses`); the sweep systems of $R$ batches of distance $a$ (`Batches.System`) and the configurations carrying them (`RankLimits.Configuration`, `RankLimits.Configuration.SweepEmbedding`); dyadic time windows (`TimeWindows.Before`, `RankLimits.SeparatedBefore`); the rank labels of points and the limiting measures of vertices, edges and crossings (`RankLimits.Data`, `RankLimits.Converges`, `RankLimits.Data.conditional`); the rank charts and their linear normalizations (`RankLimits.Configuration.rankChart`, `RankLimits.commonChart`, `Zoom.RadialCompare`); and the physically normalized measures of Section 6 (`Enhancement.measures`, `Boundary.physical`).
--
--   The definitions of the published goal (`Point`, `orient`, `GeneralPosition`, `halvingCount`, `Generic`, `switchCount` and the rest) come from the published bundle `Def_HalvingLines`. It imports no other bundle of this split.
--
--   Modules: `Activity`, `ActivityRetention`, `AtomicBounds`, `Basic`, `Batches`, `Boundary`, `BoundaryTokens`, `Calculus`, `ChainDrawing`, `Chains`, `Compactness`, `Continuity`, `CrossingEstimate`, `Curves`, `Decomposition`, `Densities`, `Derivatives`, `Directions`, `Enhancement`, `Foliations`, `Greedy`, `Intersections`, `Labels`, `LocalZoom`, `MassEstimates`, `MeasureBounds`, `Noncollapse`, `Packing`, `Partition`, `PathLimits`, `Perturbation`, `PlaneGraph`, `RankCoordinates`, `RankMeasures`, `Rigidity`, `SpatialMass`, `Sweep`, `ThinStrips`, `Tokens`, `WindowMeasures`, `Windows`, `Zoom`, `ZoomControl`.
-- source:
--   OpenAI, A power saving for planar halving lines, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 183; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-planar-halving-lines-September-25-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/HalvingLines at commit adc7f12

import Mathlib
import Definitions.Def_HalvingLines

section
-- module Solutions.OAIQW_PlanarHalving.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

@[simp] theorem orient_left (p q : Point) : orient p q p = 0 := by
  simp [orient]

@[simp] theorem orient_right (p q : Point) : orient p q q = 0 := by
  unfold orient
  ring

@[simp] theorem switchCount_zero {n : ℕ} (P : Fin n → Point) :
    switchCount P 0 = 0 := by
  simp [switchCount]

@[simp] theorem switchCount_top {n : ℕ} (P : Fin n → Point) :
    switchCount P n = 0 := by
  simp [switchCount]

theorem orient_eq_proj_diff (p q r : Point) (hx : q.1 ≠ p.1) :
    orient p q r = (q.1 - p.1) *
      ((r.2 - slope p q * r.1) - (p.2 - slope p q * p.1)) := by
  unfold orient slope
  field_simp
  ring

lemma orient_zero_iff {n : ℕ} {P : Fin n → Point} (hP : GeneralPosition P)
    {i j : Fin n} (hij : i ≠ j) (l : Fin n) :
    orient (P i) (P j) (P l) = 0 ↔ l = i ∨ l = j := by
  constructor
  · intro hl
    by_contra! hh
    exact hP.2 i j l hij hh.2.symm hh.1.symm hl
  · rintro (rfl | rfl) <;> simp

end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Activity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

namespace Sweep

noncomputable def projection (s : ℝ) (p : Point) : ℝ := p.2 - s * p.1

def Separates {n : ℕ} (P : Fin n → Point) (s : ℝ) (M : Finset (Fin n)) : Prop :=
  ∀ i ∈ M, ∀ j ∉ M, projection s (P i) < projection s (P j)

lemma comparison_persists (p q : Point) {s₀ s t : ℝ} (h₀ : s₀ ≤ s) (ht : s ≤ t)
    (hbefore : projection s₀ q < projection s₀ p)
    (hafter : projection s p < projection s q) :
    p.1 > q.1 ∧ projection t p < projection t q := by
  unfold projection at *
  have hm : 0 < (s - s₀) * (p.1 - q.1) := by nlinarith only [hbefore, hafter]
  have hx : 0 < p.1 - q.1 := by
    rcases mul_pos_iff.mp hm with hh | hh
    · exact hh.2
    · exact False.elim ((not_lt_of_ge (sub_nonneg.mpr h₀)) hh.1)
  have hprod := mul_nonneg (sub_nonneg.mpr ht) hx.le
  constructor
  · exact sub_pos.mp hx
  · nlinarith only [hafter, hprod]

lemma exchange_rightward {n : ℕ} {P : Fin n → Point} {s t : ℝ}
    {M M' : Finset (Fin n)} (hst : s ≤ t)
    (hM : Separates P s M) (hM' : Separates P t M')
    {i j : Fin n} (hi : i ∈ M \ M') (hj : j ∈ M' \ M) : (P i).1 < (P j).1 := by
  exact (comparison_persists (P j) (P i) hst le_rfl
    (hM i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).2)
    (hM' j (Finset.mem_sdiff.mp hj).1 i (Finset.mem_sdiff.mp hi).2)).1

structure ProjectionIndex (n : ℕ) where
  down : Fin n

def projectionIndexEquiv (n : ℕ) : ProjectionIndex n ≃ Fin n where
  toFun := ProjectionIndex.down
  invFun := ProjectionIndex.mk
  left_inv _ := rfl
  right_inv _ := rfl

theorem exists_state {n k : ℕ} (P : Fin n → Point) (s : ℝ) (hk : k ≤ n)
    (hinj : Function.Injective (fun i => projection s (P i))) :
    ∃ M : Finset (Fin n), M.card = k ∧ Separates P s M := by
  classical
  let ind := projectionIndexEquiv n
  let : Fintype (ProjectionIndex n) := Fintype.ofEquiv (Fin n) ind.symm
  let : LinearOrder (ProjectionIndex n) :=
    LinearOrder.lift' (fun i => projection s (P (ind i))) (hinj.comp ind.injective)
  let e := Fintype.orderIsoFinOfCardEq (ProjectionIndex n)
    ((Fintype.card_congr ind).trans (Fintype.card_fin n))
  let f : Fin k ↪ Fin n := (Fin.castLEEmb hk).trans
    (e.toEmbedding.trans ind.toEmbedding)
  let M := Finset.univ.map f
  have hmem (z : Fin n) : z ∈ M ↔ (e.symm (ind.symm z)).val < k := by
    constructor
    · intro hz
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hz
      change (e.symm (ind.symm (ind (e (Fin.castLE hk a))))).val < k
      rw [ind.symm_apply_apply, e.symm_apply_apply]
      exact a.isLt
    · intro hz
      let a : Fin k := ⟨(e.symm (ind.symm z)).val, hz⟩
      apply Finset.mem_map.mpr
      refine ⟨a, Finset.mem_univ _, ?_⟩
      change ind (e (Fin.castLE hk a)) = z
      apply ind.symm.injective
      rw [ind.symm_apply_apply]
      apply e.symm.injective
      rw [e.symm_apply_apply]
      apply Fin.ext
      rfl
  refine ⟨M, by simp only [M, Finset.card_map, Finset.card_univ, Fintype.card_fin], ?_⟩
  intro i hi j hj
  have hi' := (hmem i).mp hi
  have hj' : k ≤ (e.symm (ind.symm j)).val := Nat.le_of_not_gt (fun h => hj ((hmem j).mpr h))
  have hlt : e.symm (ind.symm i) < e.symm (ind.symm j) := by
    change (e.symm (ind.symm i)).val < (e.symm (ind.symm j)).val
    exact lt_of_lt_of_le hi' hj'
  have he := e.strictMono hlt
  rw [e.apply_symm_apply, e.apply_symm_apply] at he
  change projection s (P (ind (ind.symm i))) < projection s (P (ind (ind.symm j))) at he
  simpa only [ind.apply_symm_apply] using he

end Sweep

namespace Sweep

noncomputable def activity {n : ℕ} {ι : Type*} [Fintype ι]
    (M : ι → Finset (Fin n)) (i₀ : ι) : Finset (Fin n) :=
  Finset.univ.filter fun u => ∃ i, (u ∈ M i ∧ u ∉ M i₀) ∨
    (u ∉ M i ∧ u ∈ M i₀)

lemma mem_activity {n : ℕ} {ι : Type*} [Fintype ι]
    {M : ι → Finset (Fin n)} {i₀ : ι} {u : Fin n} :
    u ∈ activity M i₀ ↔ ∃ i, (u ∈ M i ∧ u ∉ M i₀) ∨
      (u ∉ M i ∧ u ∈ M i₀) := by
  classical
  simp [activity]

lemma exchange_slope_between {n : ℕ} {P : Fin n → Point} {s t : ℝ}
    {M M' : Finset (Fin n)} (hst : s ≤ t)
    (hM : Separates P s M) (hM' : Separates P t M')
    {i j : Fin n} (hi : i ∈ M \ M') (hj : j ∈ M' \ M) :
    s < slope (P i) (P j) ∧ slope (P i) (P j) < t := by
  have hx := exchange_rightward hst hM hM' hi hj
  have h₀ := hM i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).2
  have h₁ := hM' j (Finset.mem_sdiff.mp hj).1 i (Finset.mem_sdiff.mp hi).2
  have hdx : 0 < (P j).1 - (P i).1 := sub_pos.mpr hx
  unfold slope
  constructor
  · apply (lt_div_iff₀ hdx).mpr
    unfold projection at h₀
    nlinarith only [h₀]
  · apply (div_lt_iff₀ hdx).mpr
    unfold projection at h₁
    nlinarith only [h₁]

end Sweep

end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Boundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

namespace Boundary

def dot (u v : Point) : ℝ := u.1 * v.1 + u.2 * v.2

def sqNorm (u : Point) : ℝ := u.1 ^ 2 + u.2 ^ 2

end Boundary

end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Curves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

namespace Zoom

open scoped NNReal Topology
open Filter

noncomputable def coneLevel (Q : Point ≃L[ℝ] Point) : Point →L[ℝ] ℝ :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ) + (ContinuousLinearMap.snd ℝ ℝ ℝ)).comp
    Q.toContinuousLinearMap

lemma coneLevel_apply (Q : Point ≃L[ℝ] Point) (x : Point) :
    coneLevel Q x = (Q x).1 + (Q x).2 := rfl

lemma norm_le_coneLevel (Q : Point ≃L[ℝ] Point) (q : Point)
    (hq₁ : 0 ≤ (Q q).1) (hq₂ : 0 ≤ (Q q).2) :
    ‖q‖ ≤ ‖Q.symm.toContinuousLinearMap‖ * coneLevel Q q := by
  have hn : ‖Q q‖ ≤ coneLevel Q q := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hq₁, abs_of_nonneg hq₂, coneLevel_apply]
    exact max_le (le_add_of_nonneg_right hq₂) (le_add_of_nonneg_left hq₁)
  calc
    ‖q‖ = ‖Q.symm (Q q)‖ := by rw [Q.symm_apply_apply]
    _ ≤ ‖Q.symm.toContinuousLinearMap‖ * ‖Q q‖ :=
      Q.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖Q.symm.toContinuousLinearMap‖ * coneLevel Q q :=
      mul_le_mul_of_nonneg_left hn (norm_nonneg _)

lemma coneLevel_strictMono (Q : Point ≃L[ℝ] Point) (g : ℝ → Point)
    (hg : Function.Injective g)
    (h₁ : Monotone (fun t => (Q (g t)).1))
    (h₂ : Monotone (fun t => (Q (g t)).2)) :
    StrictMono (fun t => coneLevel Q (g t)) := by
  intro t u htu
  have ha := h₁ htu.le
  have hb := h₂ htu.le
  simp only [coneLevel_apply]
  apply lt_of_le_of_ne (add_le_add ha hb)
  intro he
  have hpair : Q (g t) = Q (g u) := Prod.ext (by linarith) (by linarith)
  exact htu.ne (hg (Q.injective hpair))

lemma coneLevel_chord (Q : Point ≃L[ℝ] Point) (g : ℝ → Point)
    (h₁ : Monotone (fun t => (Q (g t)).1))
    (h₂ : Monotone (fun t => (Q (g t)).2)) (t u : ℝ) :
    ‖g t - g u‖ ≤ ‖Q.symm.toContinuousLinearMap‖ *
      |coneLevel Q (g t - g u)| := by
  have forward (a b : ℝ) (hab : a ≤ b) :
      ‖g b - g a‖ ≤ ‖Q.symm.toContinuousLinearMap‖ *
        coneLevel Q (g b - g a) := by
    apply norm_le_coneLevel
    · rw [map_sub]
      exact sub_nonneg.mpr (h₁ hab)
    · rw [map_sub]
      exact sub_nonneg.mpr (h₂ hab)
  rcases le_total u t with hut | htu
  · exact (forward u t hut).trans
      (mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _))
  · rw [norm_sub_rev, ← abs_neg, ← map_neg, neg_sub]
    exact (forward t u htu).trans
      (mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _))

end Zoom

end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Intersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

namespace Zoom

open scoped NNReal Topology
open Filter

def DirectionalLimit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → E → E) (v w : E) : Prop :=
  ∀ (ρ : ℕ → ℕ), StrictMono ρ → ∀ (x y : ℕ → E),
    (∀ n, ∃ t : ℝ, y n = x n + t • v) → ∀ a b : E,
    Tendsto (fun n => f (ρ n) (x n)) atTop (𝓝 a) →
    Tendsto (fun n => f (ρ n) (y n)) atTop (𝓝 b) →
    ∃ r : ℝ, b - a = r • w

def detPair (u v : Point) : ℝ := u.1 * v.2 - u.2 * v.1

lemma plane_span (u v : Point) (hdet : detPair u v ≠ 0) (x : Point) :
    ∃ r s : ℝ, x = r • u + s • v := by
  refine ⟨(x.1 * v.2 - x.2 * v.1) / detPair u v,
    (u.1 * x.2 - u.2 * x.1) / detPair u v, ?_⟩
  apply Prod.ext <;> dsimp
  · field_simp
    simp only [detPair]
    ring
  · field_simp
    simp only [detPair]
    ring

end Zoom

end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Rigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

namespace Zoom

open scoped NNReal Topology
open Filter

structure LineControl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → E → E) (v : E) where
  level : E →L[ℝ] ℝ
  constant : ℝ≥0
  positive : 0 < constant
  strict : ∀ n x, StrictMono (fun t : ℝ => level (f n (x + t • v) - f n x))
  chord : ∀ n x (t u : ℝ), ‖f n (x + t • v) - f n (x + u • v)‖ ≤
    constant * |level (f n (x + t • v) - f n (x + u • v))|

noncomputable def LineControl.of_monotone
    (f : ℕ → OpenPartialHomeomorph Point Point)
    (hsource : ∀ n, (f n).source = Set.univ)
    (v : Point) (hv : v ≠ 0) (Q : Point ≃L[ℝ] Point)
    (h₁ : ∀ n x, Monotone (fun t : ℝ => (Q (f n (x + t • v))).1))
    (h₂ : ∀ n x, Monotone (fun t : ℝ => (Q (f n (x + t • v))).2)) :
    LineControl (fun n => f n) v where
  level := coneLevel Q
  constant := ‖Q.symm.toContinuousLinearMap‖₊ + 1
  positive := by positivity
  strict n x := by
    have hginj : Function.Injective (fun t : ℝ => f n (x + t • v)) := by
      intro t u he
      apply smul_left_injective ℝ hv
      exact add_left_cancel ((f n).injOn (by rw [hsource]; trivial)
        (by rw [hsource]; trivial) he)
    have hh := coneLevel_strictMono Q _ hginj (h₁ n x) (h₂ n x)
    intro t u htu
    simp only [map_sub]
    exact sub_lt_sub_right (hh htu) _
  chord n x t u := by
    have hh := coneLevel_chord Q (fun t => f n (x + t • v)) (h₁ n x) (h₂ n x) t u
    exact hh.trans (mul_le_mul_of_nonneg_right (by simp) (abs_nonneg _))

lemma parallel_scalars_zero (u v : Point) (hdet : detPair u v ≠ 0)
    (r s : ℝ) (he : r • u = s • v) : r = 0 ∧ s = 0 := by
  have h₁ : r * u.1 = s * v.1 := congrArg Prod.fst he
  have h₂ : r * u.2 = s * v.2 := congrArg Prod.snd he
  have hr : r * detPair u v = 0 := by
    dsimp [detPair]
    linear_combination v.2 * h₁ - v.1 * h₂
  have hs : s * detPair u v = 0 := by
    dsimp [detPair]
    linear_combination u.2 * h₁ - u.1 * h₂
  exact ⟨(mul_eq_zero.mp hr).resolve_right hdet, (mul_eq_zero.mp hs).resolve_right hdet⟩

inductive Foliation where
  | horizontal
  | vertical
  | diagonal
  deriving DecidableEq

def Foliation.direction : Foliation → Point
  | .horizontal => (1, 0)
  | .vertical => (0, 1)
  | .diagonal => (1, 1)

structure FoliatedSequence where
  map : ℕ → OpenPartialHomeomorph Point Point
  source : ∀ n, (map n).source = Set.univ
  exhaust : ∀ K : Set Point, IsCompact K → ∀ᶠ n in atTop, K ⊆ (map n).target
  control : ∀ i : Foliation, LineControl (fun n => map n) i.direction
  direction : ∀ i : Foliation, DirectionalLimit (fun n => map n) i.direction i.direction

def FoliatedSequence.subseq (F : FoliatedSequence) (ρ : ℕ → ℕ) (hρ : StrictMono ρ) :
    FoliatedSequence where
  map n := F.map (ρ n)
  source n := F.source (ρ n)
  exhaust K hK := hρ.tendsto_atTop.eventually (F.exhaust K hK)
  control i := {
    level := (F.control i).level
    constant := (F.control i).constant
    positive := (F.control i).positive
    strict n x := (F.control i).strict (ρ n) x
    chord n x t u := (F.control i).chord (ρ n) x t u }
  direction i σ hσ x y hxy a b ha hb :=
    F.direction i (ρ ∘ σ) (hρ.comp hσ) x y hxy a b ha hb

def FoliatedSequence.Good (F : FoliatedSequence) (σ : ℝ) (x : Point) : Prop :=
  Tendsto (fun n => F.map n x) atTop (𝓝 (σ • x))

end Zoom

end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Zoom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

namespace Zoom

open scoped NNReal Topology
open Filter

noncomputable def FoliatedSequence.axisConstant (F : FoliatedSequence) (i : Foliation) : ℝ :=
  (F.control i).constant * ‖(F.control i).level‖

noncomputable def FoliatedSequence.rectConstant (F : FoliatedSequence) : ℝ :=
  F.axisConstant .horizontal * (2 * F.axisConstant .vertical + 1) + F.axisConstant .vertical

end Zoom

end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Calculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

namespace Calculus

open Filter MeasureTheory Set Metric Asymptotics
open scoped Topology ENNReal NNReal

def slopePiece (f : Point → ℝ) (m : ℕ) : Set Point :=
  {x | ∀ q : ℚ, 0 < q →
    f (x + ((q : ℝ), (q : ℝ))) - f (x - ((q : ℝ), (q : ℝ))) ≤ m * (q : ℝ)}

end Calculus

end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Compactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

namespace RankLimit

open Filter MeasureTheory Set Metric
open scoped Topology

abbrev RatPoint := ℚ × ℚ

def ratPoint (q : RatPoint) : Point := ((q.1 : ℝ), (q.2 : ℝ))

noncomputable def lowerGrid (g : RatPoint → unitInterval) (x : Point) : unitInterval :=
  ⨆ q : RatPoint, if (q.1 : ℝ) < x.1 ∧ (q.2 : ℝ) < x.2 then g q else ⊥

end RankLimit

end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.RankCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology
namespace PlanarHalving.RankCoordinates

abbrev UnitOpen := Set.Ioo (0 : ℝ) 1

structure Coordinate (l u : ℝ) where
  value : ℝ × ℝ → ℝ
  continuous_value : Continuous value
  mem : ∀ p, value p ∈ Set.Ioo 0 1
  strict_vertical : ∀ x, StrictMono (fun y => value (x,y))
  onto_vertical : ∀ x (v : UnitOpen), ∃ y, value (x,y) = v
  translate_lower : ∀ x y h, 0 ≤ h → value (x+h,y+l*h) ≤ value (x,y)
  translate_upper : ∀ x y h, 0 ≤ h → value (x,y) ≤ value (x+h,y+u*h)

namespace Coordinate
variable {l u : ℝ} (R : Coordinate l u)

noncomputable def level (x : ℝ) (v : UnitOpen) : ℝ :=
  Classical.choose (R.onto_vertical x v)

lemma value_level (x : ℝ) (v : UnitOpen) : R.value (x,R.level x v) = v :=
  Classical.choose_spec (R.onto_vertical x v)

lemma level_value (x y : ℝ) : R.level x ⟨R.value (x,y), R.mem (x,y)⟩ = y :=
  (R.strict_vertical x).injective (R.value_level x _)

lemma lt_level_iff (x y : ℝ) (v : UnitOpen) : y < R.level x v ↔ R.value (x,y) < v := by
  rw [← R.value_level x v]
  exact (R.strict_vertical x).lt_iff_lt.symm

lemma level_lt_iff (x y : ℝ) (v : UnitOpen) : R.level x v < y ↔ (v : ℝ) < R.value (x,y) := by
  rw [← R.value_level x v]
  exact (R.strict_vertical x).lt_iff_lt.symm

lemma le_level_iff (x y : ℝ) (v : UnitOpen) : y ≤ R.level x v ↔ R.value (x,y) ≤ v := by
  rw [← R.value_level x v]
  exact (R.strict_vertical x).le_iff_le.symm

lemma level_le_iff (x y : ℝ) (v : UnitOpen) : R.level x v ≤ y ↔ (v : ℝ) ≤ R.value (x,y) := by
  rw [← R.value_level x v]
  exact (R.strict_vertical x).le_iff_le.symm

lemma continuous_level : Continuous (fun p : ℝ × UnitOpen => R.level p.1 p.2) := by
  refine continuous_iff_continuousAt.mpr fun p => tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    have h := (R.lt_level_iff p.1 a p.2).mp ha
    have hr : Continuous (fun q : ℝ × UnitOpen => R.value (q.1,a)) :=
      R.continuous_value.comp (continuous_fst.prodMk continuous_const)
    have hv : Continuous (fun q : ℝ × UnitOpen => (q.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    filter_upwards [hr.continuousAt.eventually_lt hv.continuousAt h] with q hq
    exact (R.lt_level_iff q.1 a q.2).mpr hq
  · intro a ha
    have h := (R.level_lt_iff p.1 a p.2).mp ha
    have hr : Continuous (fun q : ℝ × UnitOpen => R.value (q.1,a)) :=
      R.continuous_value.comp (continuous_fst.prodMk continuous_const)
    have hv : Continuous (fun q : ℝ × UnitOpen => (q.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    filter_upwards [hv.continuousAt.eventually_lt hr.continuousAt h] with q hq
    exact (R.level_lt_iff q.1 a q.2).mpr hq

lemma level_slope {x x' : ℝ} (h : x ≤ x') (v : UnitOpen) :
    l*(x'-x) ≤ R.level x' v - R.level x v ∧
    R.level x' v - R.level x v ≤ u*(x'-x) := by
  have h₁ := R.translate_lower x (R.level x v) (x'-x) (sub_nonneg.mpr h)
  have h₂ := R.translate_upper x (R.level x v) (x'-x) (sub_nonneg.mpr h)
  rw [R.value_level] at h₁ h₂
  have he : x + (x'-x) = x' := by ring
  rw [he] at h₁ h₂
  have hl := (R.le_level_iff x' (R.level x v + l*(x'-x)) v).mpr h₁
  have hu := (R.level_le_iff x' (R.level x v + u*(x'-x)) v).mpr h₂
  constructor <;> linarith

end Coordinate

lemma exists_zero_of_strongAnti {f : ℝ → ℝ} (hf : Continuous f) {d : ℝ}
    (hd : 0 < d) (hs : ∀ x x', x ≤ x' → f x' - f x ≤ -d*(x'-x)) :
    ∃ x, f x = 0 := by
  let t := (|f 0|+1)/d
  have ht : 0 < t := div_pos (by positivity) hd
  have htprod : d*t = |f 0|+1 := by dsimp [t]; field_simp
  have hleft := hs (-t) 0 (by linarith)
  have hright := hs 0 t ht.le
  have hzero : (0:ℝ) ∈ Set.Icc (f t) (f (-t)) := by
    constructor
    · have h := le_abs_self (f 0); nlinarith
    · have h := neg_abs_le (f 0); nlinarith
  exact intermediate_value_univ t (-t) hf hzero

variable {lA uA lB uB : ℝ} (A : Coordinate lA uA) (B : Coordinate lB uB)

noncomputable def levelDiff (v : UnitOpen × UnitOpen) (x : ℝ) : ℝ :=
  A.level x v.1 - B.level x v.2

lemma continuous_levelDiff : Continuous (fun p : (UnitOpen × UnitOpen) × ℝ =>
    levelDiff A B p.1 p.2) := by
  exact (A.continuous_level.comp (continuous_snd.prodMk continuous_fst.fst)).sub
    (B.continuous_level.comp (continuous_snd.prodMk continuous_fst.snd))

lemma levelDiff_decay (v : UnitOpen × UnitOpen) {x x' : ℝ} (h : x ≤ x') :
    levelDiff A B v x' - levelDiff A B v x ≤ -(lB-uA)*(x'-x) := by
  have ha := (A.level_slope h v.1).2
  have hb := (B.level_slope h v.2).1
  dsimp [levelDiff]
  nlinarith only [ha, hb]

lemma levelDiff_strictAnti (hgap : uA < lB) (v : UnitOpen × UnitOpen) :
    StrictAnti (levelDiff A B v) := by
  intro x x' h
  have hh := levelDiff_decay A B v h.le
  have hp : 0 < (lB-uA)*(x'-x) := mul_pos (sub_pos.mpr hgap) (sub_pos.mpr h)
  linarith

lemma exists_intersection (hgap : uA < lB) (v : UnitOpen × UnitOpen) :
    ∃ x, levelDiff A B v x = 0 := by
  exact exists_zero_of_strongAnti
    ((continuous_levelDiff A B).comp (continuous_const.prodMk continuous_id))
    (sub_pos.mpr hgap) (fun _ _ h => levelDiff_decay A B v h)

noncomputable def intersectionX (hgap : uA < lB) (v : UnitOpen × UnitOpen) : ℝ :=
  Classical.choose (exists_intersection A B hgap v)

lemma levelDiff_intersectionX (hgap : uA < lB) (v : UnitOpen × UnitOpen) :
    levelDiff A B v (intersectionX A B hgap v) = 0 :=
  Classical.choose_spec (exists_intersection A B hgap v)

lemma lt_intersectionX_iff (hgap : uA < lB) (v : UnitOpen × UnitOpen) (x : ℝ) :
    x < intersectionX A B hgap v ↔ 0 < levelDiff A B v x := by
  rw [← levelDiff_intersectionX A B hgap v]
  exact (levelDiff_strictAnti A B hgap v).lt_iff_gt.symm

lemma intersectionX_lt_iff (hgap : uA < lB) (v : UnitOpen × UnitOpen) (x : ℝ) :
    intersectionX A B hgap v < x ↔ levelDiff A B v x < 0 := by
  rw [← levelDiff_intersectionX A B hgap v]
  exact (levelDiff_strictAnti A B hgap v).lt_iff_gt.symm

lemma continuous_intersectionX (hgap : uA < lB) : Continuous (intersectionX A B hgap) := by
  refine continuous_iff_continuousAt.mpr fun v => tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    have h := (lt_intersectionX_iff A B hgap v a).mp ha
    have hc := (continuous_levelDiff A B).comp (continuous_id.prodMk (continuous_const : Continuous fun _ : UnitOpen × UnitOpen => a))
    filter_upwards [continuousAt_const.eventually_lt hc.continuousAt h] with w hw
    exact (lt_intersectionX_iff A B hgap w a).mpr hw
  · intro a ha
    have h := (intersectionX_lt_iff A B hgap v a).mp ha
    have hc := (continuous_levelDiff A B).comp (continuous_id.prodMk (continuous_const : Continuous fun _ : UnitOpen × UnitOpen => a))
    filter_upwards [hc.continuousAt.eventually_lt continuousAt_const h] with w hw
    exact (intersectionX_lt_iff A B hgap w a).mpr hw

noncomputable def pairHomeomorph (hgap : uA < lB) :
    (ℝ × ℝ) ≃ₜ (UnitOpen × UnitOpen) where
  toFun p := (⟨A.value p,A.mem p⟩, ⟨B.value p,B.mem p⟩)
  invFun v := (intersectionX A B hgap v, A.level (intersectionX A B hgap v) v.1)
  left_inv p := by
    let v : UnitOpen × UnitOpen := (⟨A.value p,A.mem p⟩, ⟨B.value p,B.mem p⟩)
    have hz : levelDiff A B v p.1 = 0 := by
      dsimp [levelDiff,v]
      rw [A.level_value, B.level_value]
      ring
    have he : intersectionX A B hgap v = p.1 :=
      (levelDiff_strictAnti A B hgap v).injective
        ((levelDiff_intersectionX A B hgap v).trans hz.symm)
    change (intersectionX A B hgap v, A.level (intersectionX A B hgap v) v.1) = p
    rw [he]
    dsimp [v]
    rw [A.level_value]
  right_inv v := by
    have he : A.level (intersectionX A B hgap v) v.1 =
        B.level (intersectionX A B hgap v) v.2 :=
      sub_eq_zero.mp (levelDiff_intersectionX A B hgap v)
    apply Prod.ext <;> apply Subtype.ext
    · exact A.value_level _ _
    · change B.value (_, A.level _ v.1) = _
      rw [he, B.value_level]
  continuous_toFun := (A.continuous_value.subtype_mk _).prodMk (B.continuous_value.subtype_mk _)
  continuous_invFun := (continuous_intersectionX A B hgap).prodMk
    (A.continuous_level.comp ((continuous_intersectionX A B hgap).prodMk continuous_fst))

noncomputable def smoothed {m : ℕ} (g : Fin m → ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  (∑ i, Real.sigmoid ((p.2 - g i p.1)/ε)) / m

lemma continuous_smoothed {m : ℕ} (g : Fin m → ℝ → ℝ) (ε : ℝ)
    (hg : ∀ i, Continuous (g i)) : Continuous (smoothed g ε) := by
  unfold smoothed
  fun_prop

lemma smoothed_mem {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) :
    smoothed g ε p ∈ Set.Ioo 0 1 := by
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hn : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0,hm⟩, Finset.mem_univ _⟩
  constructor
  · exact div_pos (Finset.sum_pos (fun i _ => Real.sigmoid_pos _) hn) hmR
  · apply (div_lt_iff₀ hmR).mpr
    have hs := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin m)))
      (f := fun i => Real.sigmoid ((p.2 - g i p.1)/ε)) (g := fun _ => (1:ℝ))
      (fun i _ => (Real.sigmoid_lt_one _).le)
      ⟨⟨0,hm⟩, Finset.mem_univ _, Real.sigmoid_lt_one _⟩
    simpa using hs

lemma strict_vertical_smoothed {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ → ℝ)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) : StrictMono (fun y => smoothed g ε (x,y)) := by
  intro y y' h
  apply div_lt_div_of_pos_right _ (Nat.cast_pos.mpr hm)
  apply Finset.sum_lt_sum
  · intro i _
    exact (Real.sigmoid_strictMono (div_lt_div_of_pos_right (sub_lt_sub_right h _) hε)).le
  · exact ⟨⟨0,hm⟩, Finset.mem_univ _,
      Real.sigmoid_strictMono (div_lt_div_of_pos_right (sub_lt_sub_right h _) hε)⟩

lemma onto_vertical_smoothed {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ → ℝ)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) (v : UnitOpen) :
    ∃ y, smoothed g ε (x,y) = v := by
  obtain ⟨t, ht⟩ : (v : ℝ) ∈ Set.range Real.sigmoid := by
    rw [Real.range_sigmoid]
    exact v.property
  let T : ℝ := ∑ i, |g i x + ε*t|
  have hT (i : Fin m) : |g i x+ε*t| ≤ T :=
    Finset.single_le_sum (fun j _ => abs_nonneg (g j x+ε*t)) (Finset.mem_univ i)
  have hlo (i : Fin m) : (-T - g i x)/ε ≤ t := by
    apply (div_le_iff₀ hε).mpr
    have h := (neg_abs_le (g i x+ε*t)).trans' (neg_le_neg (hT i))
    linarith
  have hhi (i : Fin m) : t ≤ (T - g i x)/ε := by
    apply (le_div_iff₀ hε).mpr
    have h := (le_abs_self (g i x+ε*t)).trans (hT i)
    linarith
  have hleft : smoothed g ε (x,-T) ≤ v := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hm)).mpr
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => Real.sigmoid_monotone (hlo i))
    simpa only [ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using h
  have hright : (v : ℝ) ≤ smoothed g ε (x,T) := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr hm)).mpr
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => Real.sigmoid_monotone (hhi i))
    simpa only [ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using h
  have hc : Continuous (fun y => smoothed g ε (x,y)) := by
    simp only [smoothed]
    fun_prop
  exact intermediate_value_univ (-T) T hc ⟨hleft,hright⟩

noncomputable def smoothedCoordinate {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ → ℝ)
    {ε l u : ℝ} (hε : 0 < ε) (hg : ∀ i, Continuous (g i))
    (hs : ∀ i x x', x ≤ x' → l*(x'-x) ≤ g i x'-g i x ∧ g i x'-g i x ≤ u*(x'-x)) :
    Coordinate l u where
  value := smoothed g ε
  continuous_value := continuous_smoothed g ε hg
  mem := smoothed_mem hm g ε
  strict_vertical := strict_vertical_smoothed hm g hε
  onto_vertical := onto_vertical_smoothed hm g hε
  translate_lower x y h hh := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
    apply Finset.sum_le_sum
    intro i _
    apply Real.sigmoid_monotone
    apply (div_le_div_iff_of_pos_right hε).mpr
    have he := (hs i x (x+h) (by linarith)).1
    dsimp
    linarith
  translate_upper x y h hh := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
    apply Finset.sum_le_sum
    intro i _
    apply Real.sigmoid_monotone
    apply (div_le_div_iff_of_pos_right hε).mpr
    have he := (hs i x (x+h) (by linarith)).2
    dsimp
    linarith

noncomputable def inCoordinates {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (v : UnitOpen × UnitOpen) : ℝ :=
  C.value ((pairHomeomorph A B hgap).symm v)

end PlanarHalving.RankCoordinates

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.PlaneGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving
namespace PlaneGraph

noncomputable def height (p q : Point) (x : ℝ) : ℝ :=
  p.2 + (x - p.1) * PlanarHalving.slope p q

@[simp] lemma height_left (p q : Point) : height p q p.1 = p.2 := by simp [height]
@[simp] lemma height_right (p q : Point) (hx : p.1 ≠ q.1) : height p q q.1 = q.2 := by
  unfold height PlanarHalving.slope
  have h : q.1 - p.1 ≠ 0 := sub_ne_zero.mpr hx.symm
  field_simp
  ring

def Position {V : Type*} (P : V → Point) : Prop :=
  Function.Injective P ∧ ∀ i j l, i ≠ j → j ≠ l → i ≠ l →
    orient (P i) (P j) (P l) ≠ 0

variable {V : Type*} [Fintype V] {P : V → Point}

structure Drawing (P : V → Point) where
  vertices : Finset V
  edges : Finset (V × V)
  right : ∀ e ∈ edges, (P e.1).1 < (P e.2).1
  ends : ∀ e ∈ edges, e.1 ∈ vertices ∧ e.2 ∈ vertices

def Drawing.NonCrossing (D : Drawing P) : Prop :=
  ∀ e ∈ D.edges, ∀ f ∈ D.edges, e ≠ f →
    Disjoint (openSegment ℝ (P e.1) (P e.2)) (openSegment ℝ (P f.1) (P f.2))

def IsGap (D : Drawing P) (g : V × V × V) : Prop :=
  (g.1, g.2.1) ∈ D.edges ∧ (g.1, g.2.2) ∈ D.edges ∧
  PlanarHalving.slope (P g.1) (P g.2.1) < PlanarHalving.slope (P g.1) (P g.2.2) ∧
  ∀ w, (g.1, w) ∈ D.edges →
    PlanarHalving.slope (P g.1) (P g.2.1) < PlanarHalving.slope (P g.1) (P w) →
    PlanarHalving.slope (P g.1) (P g.2.2) ≤ PlanarHalving.slope (P g.1) (P w)

noncomputable def Drawing.gaps (D : Drawing P) : Finset (V × V × V) :=
  by classical exact Finset.univ.filter (IsGap D)

lemma height_lt_height_iff (p u v : Point) {x : ℝ} (hx : p.1 < x) :
    height p u x < height p v x ↔ PlanarHalving.slope p u < PlanarHalving.slope p v := by
  simp only [height, add_lt_add_iff_left, mul_lt_mul_iff_right₀ (sub_pos.mpr hx)]

def InWedge (P : V → Point) (g : V × V × V) (q : V) : Prop :=
  (P g.1).1 < (P q).1 ∧ (P q).1 ≤ (P g.2.1).1 ∧ (P q).1 ≤ (P g.2.2).1 ∧
  height (P g.1) (P g.2.1) (P q).1 ≤ (P q).2 ∧
  (P q).2 ≤ height (P g.1) (P g.2.2) (P q).1

def FirstVertex (P : V → Point) (s : Finset V) (g : V × V × V) (q : V) : Prop :=
  InWedge P g q ∧ ∀ r ∈ s, InWedge P g r → (P q).1 ≤ (P r).1

omit [Fintype V] in
lemma IsGap.width_pos {D : Drawing P} {g : V × V × V} (hg : IsGap D g)
    {x : ℝ} (hx : (P g.1).1 < x) : height (P g.1) (P g.2.1) x < height (P g.1) (P g.2.2) x :=
  (height_lt_height_iff _ _ _ hx).mpr hg.2.2.1

omit [Fintype V] in
lemma IsGap.exists_inWedge {D : Drawing P} {g : V × V × V} (hg : IsGap D g) :
    ∃ q ∈ D.vertices, InWedge P g q := by
  have hl := D.right _ hg.1
  have hu := D.right _ hg.2.1
  by_cases h : (P g.2.1).1 ≤ (P g.2.2).1
  · refine ⟨g.2.1, (D.ends _ hg.1).2, hl, le_rfl, h, ?_, ?_⟩
    · rw [height_right _ _ hl.ne]
    · simpa only [height_right _ _ hl.ne] using (hg.width_pos hl).le
  · refine ⟨g.2.2, (D.ends _ hg.2.1).2, hu, (not_le.mp h).le, le_rfl, ?_, ?_⟩
    · simpa only [height_right _ _ hu.ne] using (hg.width_pos hu).le
    · rw [height_right _ _ hu.ne]

omit [Fintype V] in
lemma IsGap.exists_firstVertex {D : Drawing P} {g : V × V × V} (hg : IsGap D g) :
    ∃ q : ↥D.vertices, FirstVertex P D.vertices g q := by
  classical
  let W := D.vertices.filter (InWedge P g)
  have he : W.Nonempty := by
    obtain ⟨q, hqv, hq⟩ := hg.exists_inWedge
    exact ⟨q, Finset.mem_filter.mpr ⟨hqv, hq⟩⟩
  obtain ⟨q, hq, hmin⟩ := W.exists_min_image (fun r => (P r).1) he
  refine ⟨⟨q, (Finset.mem_filter.mp hq).1⟩, (Finset.mem_filter.mp hq).2, ?_⟩
  intro r hrv hr
  exact hmin r (Finset.mem_filter.mpr ⟨hrv, hr⟩)

noncomputable def Drawing.first (D : Drawing P) (g : ↥D.gaps) : ↥D.vertices :=
  by classical exact Classical.choose ((Finset.mem_filter.mp g.property).2.exists_firstVertex)

noncomputable def Drawing.gapCharge (D : Drawing P) (g : ↥D.gaps) : ↥D.vertices × Bool :=
  by classical exact (D.first g, decide
    (height (P g.val.1) (P g.val.2.1) (P (D.first g)).1 < (P (D.first g)).2))

noncomputable def Drawing.edgeCharge (D : Drawing P) (e : ↥D.edges) : ↥D.vertices ⊕ ↥D.gaps := by
  classical
  exact if h : ∃ w, IsGap D (e.val.1, e.val.2, w) then
    Sum.inr ⟨(e.val.1, e.val.2, Classical.choose h), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Classical.choose_spec h⟩⟩
  else Sum.inl ⟨e.val.1, (D.ends _ e.property).1⟩

omit [Fintype V] in
lemma slope_eq_implies_eq_ne (hP : Position P) {v u w : V}
    (hu : (P v).1 ≠ (P u).1) (hw : (P v).1 ≠ (P w).1)
    (hs : PlanarHalving.slope (P v) (P u) = PlanarHalving.slope (P v) (P w)) : u = w := by
  by_contra hn
  have hvu : v ≠ u := fun h => hu (congrArg (fun i => (P i).1) h)
  have hvw : v ≠ w := fun h => hw (congrArg (fun i => (P i).1) h)
  have hyu := height_right (P v) (P u) hu
  have hyw := height_right (P v) (P w) hw
  rw [height, hs] at hyu
  rw [height] at hyw
  apply hP.2 v u w hvu hn hvw
  unfold orient
  have hu' : (P u).2 - (P v).2 = ((P u).1 - (P v).1) * PlanarHalving.slope (P v) (P w) := by linarith
  have hw' : (P w).2 - (P v).2 = ((P w).1 - (P v).1) * PlanarHalving.slope (P v) (P w) := by linarith
  rw [hu', hw']
  ring

lemma height_of_mem_openSegment {p q z : Point} (hx : p.1 ≠ q.1)
    (hz : z ∈ openSegment ℝ p q) : z.1 ≠ p.1 ∧ z.2 = height p q z.1 := by
  rw [openSegment_eq_image] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hd : q.1 - p.1 ≠ 0 := sub_ne_zero.mpr hx.symm
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor
  · have hmul : t * (q.1 - p.1) ≠ 0 := mul_ne_zero ht.1.ne' hd
    intro he
    apply hmul
    linarith
  · unfold height PlanarHalving.slope
    field_simp
    ring

lemma openSegment_horizontal_bounds {p q z : Point} (hx : p.1 < q.1)
    (hz : z ∈ openSegment ℝ p q) : p.1 < z.1 ∧ z.1 < q.1 := by
  rw [openSegment_eq_image] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
  constructor <;> nlinarith [mul_pos ht.1 (sub_pos.mpr hx),
    mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hx)]

def Crosses (P : V → Point) (e f : V × V) : Prop :=
  ¬ Disjoint (openSegment ℝ (P e.1) (P e.2)) (openSegment ℝ (P f.1) (P f.2))

noncomputable def edgeIndex : (V × V) ≃ Fin (Fintype.card (V × V)) := Fintype.equivFin _

noncomputable def Drawing.crossings (D : Drawing P) : Finset ((V × V) × (V × V)) := by
  classical
  exact (D.edges ×ˢ D.edges).filter (fun ef => edgeIndex ef.1 < edgeIndex ef.2 ∧ Crosses P ef.1 ef.2)

noncomputable def Drawing.uncross (D : Drawing P) : Drawing P := by
  classical
  exact ⟨D.vertices, D.edges \ D.crossings.image Prod.fst,
    fun e he => D.right e (Finset.mem_sdiff.mp he).1,
    fun e he => D.ends e (Finset.mem_sdiff.mp he).1⟩

end PlaneGraph
end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.CrossingEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.FiniteSampling
open scoped BigOperators

variable {V : Type*} [Fintype V]

noncomputable def weight (p : V → ℝ) (ω : V → Bool) : ℝ :=
  ∏ v, if ω v then p v else 1 - p v

noncomputable def expect (p : V → ℝ) (f : (V → Bool) → ℝ) : ℝ :=
  by classical exact ∑ ω, weight p ω * f ω

noncomputable def keep (s : Finset V) (ω : V → Bool) : ℝ :=
  if ∀ v ∈ s, ω v = true then 1 else 0

noncomputable def bit (F : Finset V) (ω : ↥F → Bool) (v : V) : Bool := by
  classical
  exact if hv : v ∈ F then ω ⟨v,hv⟩ else false

end PlanarHalving.FiniteSampling

namespace PlanarHalving.PlaneGraph
open scoped BigOperators
open FiniteSampling
variable {V : Type*} [Fintype V] {P : V → Point}

noncomputable def Drawing.sample (D : Drawing P) (ω : V → Bool) : Drawing P := by
  classical
  exact ⟨D.vertices.filter (fun v => ω v = true),
    D.edges.filter (fun e => ω e.1 = true ∧ ω e.2 = true),
    fun e he => D.right e (Finset.mem_filter.mp he).1,
    fun e he => ⟨Finset.mem_filter.mpr ⟨(D.ends _ (Finset.mem_filter.mp he).1).1,
      (Finset.mem_filter.mp he).2.1⟩,
      Finset.mem_filter.mpr ⟨(D.ends _ (Finset.mem_filter.mp he).1).2,
      (Finset.mem_filter.mp he).2.2⟩⟩⟩

def Drawing.Bipartite (D : Drawing P) (A : Finset V) : Prop :=
  ∀ e ∈ D.edges, (e.1 ∈ A ∧ e.2 ∉ A) ∨ (e.1 ∉ A ∧ e.2 ∈ A)

noncomputable def twoProb (A : Finset V) (p q : ℝ) (v : V) : ℝ :=
  by classical exact if v ∈ A then p else q

end PlanarHalving.PlaneGraph

namespace PlanarHalving.PlaneGraph
open scoped BigOperators
open FiniteSampling
variable {V : Type*} [Fintype V] {P : V → Point}

noncomputable def Drawing.cut (D : Drawing P) (F : Finset V) (ω : ↥F → Bool) : Drawing P := by
  classical
  exact ⟨D.vertices, D.edges.filter (fun e => bit F ω e.1 ≠ bit F ω e.2),
    fun e he => D.right e (Finset.mem_filter.mp he).1,
    fun e he => D.ends e (Finset.mem_filter.mp he).1⟩

noncomputable def Drawing.cutSide (D : Drawing P) (F : Finset V) (ω : ↥F → Bool) : Finset V := by
  classical
  exact D.vertices.filter (fun v => bit F ω v = true)

end PlanarHalving.PlaneGraph

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Batches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving
namespace Batches

variable {α : Type*} [DecidableEq α]

noncomputable def transport (M M' : Finset α) (e : ↥(M \ M') ≃ ↥(M' \ M)) :
    ↥M ≃ ↥M' where
  toFun u := if h : (u : α) ∈ M' then ⟨u, h⟩
    else let v := e ⟨u, Finset.mem_sdiff.mpr ⟨u.property, h⟩⟩
         ⟨v.val, (Finset.mem_sdiff.mp v.property).1⟩
  invFun v := if h : (v : α) ∈ M then ⟨v, h⟩
    else let u := e.symm ⟨v, Finset.mem_sdiff.mpr ⟨v.property, h⟩⟩
         ⟨u.val, (Finset.mem_sdiff.mp u.property).1⟩
  left_inv := by
    intro u
    by_cases h : (u : α) ∈ M'
    · simp only [h, u.property, ↓reduceDIte]
    · have hn := (Finset.mem_sdiff.mp (e ⟨u.val,
        Finset.mem_sdiff.mpr ⟨u.property, h⟩⟩).property).2
      simp only [h, hn, ↓reduceDIte]
      exact congrArg (fun w : ↥(M \ M') => (⟨w.val,
        (Finset.mem_sdiff.mp w.property).1⟩ : ↥M)) (e.symm_apply_apply _)
  right_inv := by
    intro v
    by_cases h : (v : α) ∈ M
    · simp only [h, v.property, ↓reduceDIte]
    · have hn := (Finset.mem_sdiff.mp (e.symm ⟨v.val,
        Finset.mem_sdiff.mpr ⟨v.property, h⟩⟩).property).2
      simp only [h, hn, ↓reduceDIte]
      exact congrArg (fun w : ↥(M' \ M) => (⟨w.val,
        (Finset.mem_sdiff.mp w.property).1⟩ : ↥M')) (e.apply_symm_apply _)

lemma transport_of_mem {M M' : Finset α} (e : ↥(M \ M') ≃ ↥(M' \ M))
    (u : ↥M) (hu : (u : α) ∈ M') : (transport M M' e u : α) = u := by
  simp [transport, hu]

lemma transport_of_not_mem {M M' : Finset α} (e : ↥(M \ M') ≃ ↥(M' \ M))
    (u : ↥M) (hu : (u : α) ∉ M') :
    (transport M M' e u : α) = (e ⟨u.val, Finset.mem_sdiff.mpr ⟨u.property, hu⟩⟩ : α) := by
  simp [transport, hu]

noncomputable def matching {a : ℕ} [NeZero a] {L G : Type*}
    (l : L ≃ Fin a) (g : G ≃ Fin a) (j : Fin a) : L ≃ G :=
  l.trans ((Equiv.addRight j).trans g.symm)

lemma matching_unique {a : ℕ} [NeZero a] {L G : Type*}
    (l : L ≃ Fin a) (g : G ≃ Fin a) (u : L) (v : G) :
    ∃! j, matching l g j u = v := by
  refine ⟨g v - l u, ?_, ?_⟩
  · apply g.injective
    simp [matching]
  · intro j hj
    have h : l u + j = g v := by
      simpa [matching] using congrArg g hj
    exact eq_sub_of_add_eq' h

structure System {n R k a : ℕ} (P : Fin n → Point) where
  slope : Fin (R + 1) → ℝ
  increasing : StrictMono slope
  marks : Fin (R + 1) → Finset (Fin n)
  card_marks : ∀ b, (marks b).card = k
  separates : ∀ b, Sweep.Separates P (slope b) (marks b)
  distance : ∀ b : Fin R, (marks b.castSucc \ marks b.succ).card = a

variable {n R k a : ℕ} {P : Fin n → Point}

noncomputable def System.loss (S : @System n R k a P) (b : Fin R) : Finset (Fin n) :=
  S.marks b.castSucc \ S.marks b.succ
noncomputable def System.gain (S : @System n R k a P) (b : Fin R) : Finset (Fin n) :=
  S.marks b.succ \ S.marks b.castSucc

lemma System.card_loss (S : @System n R k a P) (b : Fin R) : (S.loss b).card = a :=
  S.distance b
lemma System.card_gain (S : @System n R k a P) (b : Fin R) : (S.gain b).card = a := by
  rw [System.gain, Finset.card_sdiff_comm (by rw [S.card_marks, S.card_marks])]
  exact S.card_loss b

noncomputable def System.lossIndex (S : @System n R k a P) (b : Fin R) : ↥(S.loss b) ≃ Fin a :=
  Fintype.equivFinOfCardEq (by simpa using S.card_loss b)
noncomputable def System.gainIndex (S : @System n R k a P) (b : Fin R) : ↥(S.gain b) ≃ Fin a :=
  Fintype.equivFinOfCardEq (by simpa using S.card_gain b)

noncomputable def System.match (S : @System n R k a P) [NeZero a] (j : Fin a) (b : Fin R) :
    ↥(S.loss b) ≃ ↥(S.gain b) := matching (S.lossIndex b) (S.gainIndex b) j

noncomputable def System.transition (S : @System n R k a P) [NeZero a]
    (j : Fin a) (b : Fin R) : ↥(S.marks b.castSucc) ≃ ↥(S.marks b.succ) :=
  transport _ _ (S.match j b)

noncomputable def System.tokenState (S : @System n R k a P) [NeZero a]
    (j : Fin a) (b : Fin (R + 1)) : ↥(S.marks 0) ≃ ↥(S.marks b) :=
  Fin.induction (Equiv.refl _) (fun b e => e.trans (S.transition j b)) b

@[simp] lemma System.tokenState_zero (S : @System n R k a P) [NeZero a]
    (j : Fin a) : S.tokenState j 0 = Equiv.refl _ := by simp [System.tokenState]

lemma System.tokenState_succ (S : @System n R k a P) [NeZero a]
    (j : Fin a) (b : Fin R) (u : ↥(S.marks 0)) :
    S.tokenState j b.succ u = S.transition j b (S.tokenState j b.castSucc u) := by
  simp [System.tokenState, Fin.induction_succ]

lemma System.edge_right (S : @System n R k a P) (b : Fin R)
    {u v : Fin n} (hu : u ∈ S.loss b) (hv : v ∈ S.gain b) : (P u).1 < (P v).1 := by
  exact Sweep.exchange_rightward (S.increasing (Fin.castSucc_lt_succ (i := b))).le
    (S.separates b.castSucc) (S.separates b.succ) hu hv

lemma System.edge_slope (S : @System n R k a P) (b : Fin R)
    {u v : Fin n} (hu : u ∈ S.loss b) (hv : v ∈ S.gain b) :
    S.slope b.castSucc < PlanarHalving.slope (P u) (P v) ∧
    PlanarHalving.slope (P u) (P v) < S.slope b.succ :=
  Sweep.exchange_slope_between (S.increasing (Fin.castSucc_lt_succ (i := b))).le
    (S.separates b.castSucc) (S.separates b.succ) hu hv

end Batches
end PlanarHalving

namespace PlanarHalving.Batches
open PlaneGraph

lemma fin_between_le {R : ℕ} {f : Fin (R + 1) → ℝ} (i j : Fin (R + 1))
    (hij : i ≤ j)
    (hstep : ∀ r : Fin R, i ≤ r.castSucc → r.succ ≤ j → f r.castSucc ≤ f r.succ) :
    f i ≤ f j := by
  induction j using Fin.induction with
  | zero =>
    have hi : i = 0 := Fin.ext (by simpa using hij)
    subst i
    exact le_rfl
  | succ r ih =>
    by_cases hi : i ≤ r.castSucc
    · exact (ih hi (fun s hs ht => hstep s hs (ht.trans (Fin.castSucc_le_succ r)))).trans
        (hstep r hi le_rfl)
    · have he : i = r.succ := Fin.ext (by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at *; omega)
      subst i
      exact le_rfl

structure ConvexPath (R : ℕ) where
  point : Fin (R + 1) → Point
  right : ∀ r : Fin R, point r.castSucc = point r.succ ∨
    (point r.castSucc).1 < (point r.succ).1
  slopes : ∀ r s : Fin R, r < s → point r.castSucc ≠ point r.succ →
    point s.castSucc ≠ point s.succ →
    slope (point r.castSucc) (point r.succ) ≤ slope (point s.castSucc) (point s.succ)

lemma projection_step (p q : Point) {t : ℝ} (hx : p.1 ≠ q.1) :
    Sweep.projection t q - Sweep.projection t p =
      (q.1 - p.1) * (slope p q - t) := by
  unfold Sweep.projection slope
  field_simp
  ring

variable {R : ℕ}

lemma ConvexPath.support_vertex (C : ConvexPath R) (b : Fin R)
    (hb : C.point b.castSucc ≠ C.point b.succ) (c : Fin (R + 1)) :
    height (C.point b.castSucc) (C.point b.succ) (C.point c).1 ≤ (C.point c).2 := by
  let t := slope (C.point b.castSucc) (C.point b.succ)
  have hb' := (C.right b).resolve_left hb
  have hroot : Sweep.projection t (C.point b.castSucc) =
      Sweep.projection t (C.point b.succ) := by
    have hh := projection_step (C.point b.castSucc) (C.point b.succ) (t := t) hb'.ne
    simp only [t, sub_self, mul_zero] at hh
    linarith
  have hmin : Sweep.projection t (C.point b.castSucc) ≤ Sweep.projection t (C.point c) := by
    by_cases hc : c ≤ b.castSucc
    · have hh := fin_between_le (f := fun r => -Sweep.projection t (C.point r)) c b.castSucc hc
      apply neg_le_neg_iff.mp
      apply hh
      intro r _ hr
      rcases C.right r with he | hx
      · rw [he]
      · have hne : C.point r.castSucc ≠ C.point r.succ := fun he => hx.ne (congrArg Prod.fst he)
        have hlt : r < b := by simp only [Fin.le_def, Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at *; omega
        have hs := C.slopes r b hlt hne hb
        have hd := projection_step (C.point r.castSucc) (C.point r.succ) (t := t) hx.ne
        have hn := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx.le) (sub_nonpos.mpr hs)
        dsimp only [t] at hd ⊢
        linarith only [hd, hn]
    · have hc' : b.succ ≤ c := by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at *; omega
      rw [hroot]
      apply fin_between_le (f := fun r => Sweep.projection t (C.point r)) b.succ c hc'
      intro r hr _
      rcases C.right r with he | hx
      · rw [he]
      · have hne : C.point r.castSucc ≠ C.point r.succ := fun he => hx.ne (congrArg Prod.fst he)
        have hlt : b < r := by simp only [Fin.le_def, Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at *; omega
        have hs := C.slopes b r hlt hb hne
        have hd := projection_step (C.point r.castSucc) (C.point r.succ) (t := t) hx.ne
        have hn := mul_nonneg (sub_nonneg.mpr hx.le) (sub_nonneg.mpr hs)
        change Sweep.projection t (C.point r.castSucc) ≤ Sweep.projection t (C.point r.succ)
        dsimp only [t] at hd ⊢
        linarith only [hd, hn]
  unfold Sweep.projection at hmin
  unfold height
  dsimp only [t] at hmin
  linarith only [hmin]

lemma ConvexPath.support_segment (C : ConvexPath R) (b : Fin R)
    (hb : C.point b.castSucc ≠ C.point b.succ) (c : Fin R) {z : Point}
    (hz : z ∈ segment ℝ (C.point c.castSucc) (C.point c.succ)) :
    height (C.point b.castSucc) (C.point b.succ) z.1 ≤ z.2 := by
  rw [segment_eq_image] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  have h₀ := C.support_vertex b hb c.castSucc
  have h₁ := C.support_vertex b hb c.succ
  have hw₀ := mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr h₀)
  have hw₁ := mul_nonneg hu.1 (sub_nonneg.mpr h₁)
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, height] at *
  nlinarith only [hw₀, hw₁]

variable {n k a : ℕ} {P : Fin n → Point}

lemma System.token_step (S : @System n R k a P) [NeZero a]
    (j : Fin a) (u : ↥(S.marks 0)) (b : Fin R) :
    (S.tokenState j b.castSucc u : Fin n) = (S.tokenState j b.succ u : Fin n) ∨
      (S.tokenState j b.castSucc u : Fin n) ∈ S.loss b ∧
      (S.tokenState j b.succ u : Fin n) ∈ S.gain b := by
  rw [S.tokenState_succ]
  by_cases h : (S.tokenState j b.castSucc u : Fin n) ∈ S.marks b.succ
  · left
    exact (transport_of_mem (S.match j b) _ h).symm
  · right
    refine ⟨Finset.mem_sdiff.mpr ⟨(S.tokenState j b.castSucc u).property, h⟩, ?_⟩
    change (transport _ _ (S.match j b) _ : Fin n) ∈ _
    rw [transport_of_not_mem (S.match j b) _ h]
    exact (S.match j b ⟨_, Finset.mem_sdiff.mpr ⟨(S.tokenState j b.castSucc u).property, h⟩⟩).property

noncomputable def System.tokenPath (S : @System n R k a P) [NeZero a]
    (j : Fin a) (u : ↥(S.marks 0)) : ConvexPath R where
  point b := P (S.tokenState j b u)
  right b := by
    rcases S.token_step j u b with h | ⟨h₀,h₁⟩
    · exact Or.inl (congrArg P h)
    · exact Or.inr (S.edge_right b h₀ h₁)
  slopes b c hbc hb hc := by
    have hb' := (S.token_step j u b).resolve_left (fun h => hb (congrArg P h))
    have hc' := (S.token_step j u c).resolve_left (fun h => hc (congrArg P h))
    have hs₁ := S.edge_slope b hb'.1 hb'.2
    have hs₂ := S.edge_slope c hc'.1 hc'.2
    have horder : b.succ ≤ c.castSucc := by
      simp only [Fin.le_def, Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at *
      omega
    exact (hs₁.2.trans_le (S.increasing.monotone horder)).trans hs₂.1 |>.le

end PlanarHalving.Batches

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Chains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.PlaneGraph

variable {V : Type*} [Fintype V] {P : V → Point}

def Drawing.NoMultiple (D : Drawing P) : Prop :=
  ∀ e ∈ D.edges, ∀ f ∈ D.edges, e ≠ f → ∀ g ∈ D.edges,
    g ≠ e → g ≠ f → ∀ z : Point,
    z ∈ openSegment ℝ (P e.1) (P e.2) →
    z ∈ openSegment ℝ (P f.1) (P f.2) →
    z ∉ segment ℝ (P g.1) (P g.2)

lemma Drawing.crossing_props (D : Drawing P) (w : ↥D.crossings) :
    w.val.1 ∈ D.edges ∧ w.val.2 ∈ D.edges ∧
    edgeIndex w.val.1 < edgeIndex w.val.2 ∧ Crosses P w.val.1 w.val.2 := by
  classical
  have h := Finset.mem_filter.mp w.property
  exact ⟨(Finset.mem_product.mp h.1).1, (Finset.mem_product.mp h.1).2, h.2⟩

noncomputable def Drawing.crossingPoint (D : Drawing P) (w : ↥D.crossings) : Point :=
  (Set.not_disjoint_iff.mp (D.crossing_props w).2.2.2).choose

lemma Drawing.crossingPoint_mem (D : Drawing P) (w : ↥D.crossings) :
    D.crossingPoint w ∈ openSegment ℝ (P w.val.1.1) (P w.val.1.2) ∧
    D.crossingPoint w ∈ openSegment ℝ (P w.val.2.1) (P w.val.2.2) :=
  (Set.not_disjoint_iff.mp (D.crossing_props w).2.2.2).choose_spec

structure ConvexCover (D : Drawing P) (I : Type*) where
  owner : V × V → I
  support : ∀ e ∈ D.edges, ∀ f ∈ D.edges, owner e = owner f →
    ∀ z ∈ segment ℝ (P f.1) (P f.2), height (P e.1) (P e.2) z.1 ≤ z.2

structure ConcaveCover (D : Drawing P) (I : Type*) where
  owner : V × V → I
  support : ∀ e ∈ D.edges, ∀ f ∈ D.edges, owner e = owner f →
    ∀ z ∈ segment ℝ (P f.1) (P f.2), z.2 ≤ height (P e.1) (P e.2) z.1

end PlanarHalving.PlaneGraph

namespace PlanarHalving.Batches
open PlaneGraph

variable {n R k a : ℕ} {P : Fin n → Point}

noncomputable def System.edges (S : @System n R k a P) : Finset (Fin n × Fin n) :=
  Finset.univ.biUnion (fun b => S.loss b ×ˢ S.gain b)

lemma System.mem_edges (S : @System n R k a P) (e : Fin n × Fin n) :
    e ∈ S.edges ↔ ∃ b : Fin R, e.1 ∈ S.loss b ∧ e.2 ∈ S.gain b := by
  simp only [System.edges, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_product]

lemma System.batch_unique (S : @System n R k a P) {e : Fin n × Fin n}
    {b c : Fin R} (hb : e.1 ∈ S.loss b ∧ e.2 ∈ S.gain b)
    (hc : e.1 ∈ S.loss c ∧ e.2 ∈ S.gain c) : b = c := by
  have h₁ := S.edge_slope b hb.1 hb.2
  have h₂ := S.edge_slope c hc.1 hc.2
  by_contra h
  rcases lt_or_gt_of_ne h with hbc | hcb
  · have ht : b.succ ≤ c.castSucc := by
      simp only [Fin.le_def, Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at *
      omega
    have := S.increasing.monotone ht
    linarith only [h₁.2, h₂.1, this]
  · have ht : c.succ ≤ b.castSucc := by
      simp only [Fin.le_def, Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at *
      omega
    have := S.increasing.monotone ht
    linarith only [h₂.2, h₁.1, this]

noncomputable def System.vertices (S : @System n R k a P) : Finset (Fin n) :=
  S.edges.image Prod.fst ∪ S.edges.image Prod.snd

lemma System.edge_ends (S : @System n R k a P) {e : Fin n × Fin n} (he : e ∈ S.edges) :
    e.1 ∈ S.vertices ∧ e.2 ∈ S.vertices := by
  exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e,he,rfl⟩),
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e,he,rfl⟩)⟩

noncomputable def System.drawing (S : @System n R k a P) : Drawing P where
  vertices := S.vertices
  edges := S.edges
  right e he := by obtain ⟨b,hb,hc⟩ := (S.mem_edges e).mp he; exact S.edge_right b hb hc
  ends _ he := S.edge_ends he

structure System.EdgeTrace (S : @System n R k a P) [NeZero a] (e : Fin n × Fin n) where
  batch : Fin R
  number : Fin a
  token : ↥(S.marks 0)
  source : (S.tokenState number batch.castSucc token : Fin n) = e.1
  target : (S.tokenState number batch.succ token : Fin n) = e.2
  loss : e.1 ∈ S.loss batch
  gain : e.2 ∈ S.gain batch

lemma System.trace_exists (S : @System n R k a P) [NeZero a]
    {e : Fin n × Fin n} (he : e ∈ S.edges) : Nonempty (S.EdgeTrace e) := by
  obtain ⟨b,hl,hg⟩ := (S.mem_edges e).mp he
  obtain ⟨j,hj,_⟩ := matching_unique (S.lossIndex b) (S.gainIndex b) ⟨e.1,hl⟩ ⟨e.2,hg⟩
  let u : ↥(S.marks b.castSucc) := ⟨e.1, (Finset.mem_sdiff.mp hl).1⟩
  let t := (S.tokenState j b.castSucc).symm u
  have hsrc : S.tokenState j b.castSucc t = u := Equiv.apply_symm_apply _ _
  refine ⟨⟨b,j,t,congrArg Subtype.val hsrc, ?_, hl,hg⟩⟩
  rw [S.tokenState_succ, hsrc]
  have hn : (u : Fin n) ∉ S.marks b.succ := (Finset.mem_sdiff.mp hl).2
  change (transport _ _ (S.match j b) u : Fin n) = e.2
  rw [transport_of_not_mem (S.match j b) _ hn]
  exact congrArg Subtype.val hj

noncomputable def System.trace (S : @System n R k a P) [NeZero a]
    {e : Fin n × Fin n} (he : e ∈ S.edges) : S.EdgeTrace e :=
  Classical.choice (S.trace_exists he)

noncomputable def System.convexOwner (S : @System n R k a P) [NeZero n] [NeZero a]
    (e : Fin n × Fin n) : Fin a × Fin n :=
  if h : e ∈ S.edges then ((S.trace h).number, (S.trace h).token.val) else (0,0)

lemma System.convexOwner_eq (S : @System n R k a P) [NeZero n] [NeZero a]
    {e : Fin n × Fin n} (he : e ∈ S.edges) :
    S.convexOwner e = ((S.trace he).number, (S.trace he).token.val) := by
  simp only [System.convexOwner, dite_eq_left he]

noncomputable def System.convexCover (S : @System n R k a P) [NeZero n] [NeZero a] :
    ConvexCover S.drawing (Fin a × Fin n) where
  owner := S.convexOwner
  support e he f hf howner z hz := by
    have he' : e ∈ S.edges := he
    have hf' : f ∈ S.edges := hf
    rw [S.convexOwner_eq he', S.convexOwner_eq hf'] at howner
    have hj : (S.trace he').number = (S.trace hf').number := congrArg Prod.fst howner
    have hu : (S.trace he').token = (S.trace hf').token := Subtype.ext (congrArg Prod.snd howner)
    let C := S.tokenPath (S.trace he').number (S.trace he').token
    have h₀ : C.point (S.trace he').batch.castSucc = P e.1 := congrArg P (S.trace he').source
    have h₁ : C.point (S.trace he').batch.succ = P e.2 := congrArg P (S.trace he').target
    have h₂ : C.point (S.trace hf').batch.castSucc = P f.1 := by
      simp only [C, System.tokenPath, hj, hu, (S.trace hf').source]
    have h₃ : C.point (S.trace hf').batch.succ = P f.2 := by
      simp only [C, System.tokenPath, hj, hu, (S.trace hf').target]
    have hne : C.point (S.trace he').batch.castSucc ≠ C.point (S.trace he').batch.succ := by
      rw [h₀,h₁]
      exact fun h => (S.drawing.right _ he).ne (congrArg Prod.fst h)
    have hzs : z ∈ segment ℝ (C.point (S.trace hf').batch.castSucc) (C.point (S.trace hf').batch.succ) := by
      rwa [h₂,h₃]
    have h := C.support_segment (S.trace he').batch hne (S.trace hf').batch hzs
    rwa [h₀,h₁] at h

end PlanarHalving.Batches

namespace PlanarHalving.PlaneGraph
variable {V : Type*} [Fintype V] {P : V → Point} {I J : Type*} {D : Drawing P}

lemma slope_neg_reverse (p q : Point) : slope (-q) (-p) = slope p q := by
  simp only [slope, Prod.fst_neg, Prod.snd_neg]
  congr 1 <;> ring

lemma height_neg_reverse (p q : Point) (hx : p.1 ≠ q.1) (x : ℝ) :
    height (-q) (-p) (-x) = -height p q x := by
  have hy := height_right p q hx
  rw [height, slope_neg_reverse]
  simp only [Prod.fst_neg, Prod.snd_neg]
  unfold height at hy ⊢
  linarith only [hy]

end PlanarHalving.PlaneGraph

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.ChainDrawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Batches
open PlaneGraph
variable {n R k a : ℕ} {P : Fin n → Point}

noncomputable def System.flip (S : @System n R k a P) :
    @System n R (n-k) a (fun v => -P v) where
  slope := S.slope
  increasing := S.increasing
  marks b := (S.marks b)ᶜ
  card_marks b := by
    classical
    rw [Finset.card_compl, S.card_marks, Fintype.card_fin]
  separates b := by
    classical
    intro i hi j hj
    have hi' := Finset.mem_compl.mp hi
    have hj' : j ∈ S.marks b := by simpa using hj
    have h := S.separates b j hj' i hi'
    simp only [Sweep.projection, Prod.fst_neg, Prod.snd_neg] at *
    linarith
  distance b := by
    classical
    have he : (S.marks b.castSucc)ᶜ \ (S.marks b.succ)ᶜ = S.gain b := by
      ext u
      simp [System.gain, and_comm]
    rw [he, S.card_gain]

@[simp] lemma System.flip_loss (S : @System n R k a P) (b : Fin R) :
    S.flip.loss b = S.gain b := by
  classical
  ext u
  simp [System.loss, System.gain, System.flip, and_comm]
@[simp] lemma System.flip_gain (S : @System n R k a P) (b : Fin R) :
    S.flip.gain b = S.loss b := by
  classical
  ext u
  simp [System.loss, System.gain, System.flip, and_comm]

lemma System.flip_edge (S : @System n R k a P) (e : Fin n × Fin n) :
    e.swap ∈ S.flip.edges ↔ e ∈ S.edges := by
  rw [S.flip.mem_edges, S.mem_edges]
  simp only [Prod.fst_swap, Prod.snd_swap, System.flip_loss, System.flip_gain, and_comm]

noncomputable def System.concaveCover (S : @System n R k a P) [NeZero n] [NeZero a] :
    ConcaveCover S.drawing (Fin a × Fin n) where
  owner e := S.flip.convexOwner e.swap
  support e he f hf ho z hz := by
    have he' : e.swap ∈ S.flip.drawing.edges := (S.flip_edge e).mpr he
    have hf' : f.swap ∈ S.flip.drawing.edges := (S.flip_edge f).mpr hf
    have hz' : -z ∈ segment ℝ (-P f.2) (-P f.1) := by
      rw [segment_eq_image] at hz ⊢
      obtain ⟨u,hu,hz⟩ := hz
      refine ⟨1-u, ⟨by linarith only [hu.2], by linarith only [hu.1]⟩, ?_⟩
      rw [← hz]
      module
    have h := S.flip.convexCover.support e.swap he' f.swap hf' ho (-z) hz'
    change height (-P e.2) (-P e.1) (-z.1) ≤ -z.2 at h
    rw [height_neg_reverse _ _ (S.drawing.right e he).ne] at h
    exact neg_le_neg_iff.mp h

end PlanarHalving.Batches

namespace PlanarHalving.PlaneGraph
variable {n : ℕ} {P : Fin n → Point}

def sortEdge (e : Fin n × Fin n) : Fin n × Fin n :=
  if e.1 < e.2 then e else e.swap

lemma sortEdge_order (e : Fin n × Fin n) (he : e.1 ≠ e.2) :
    (sortEdge e).1 < (sortEdge e).2 := by
  unfold sortEdge
  split_ifs with h
  · exact h
  · exact lt_of_le_of_ne (le_of_not_gt h) he.symm

lemma sortEdge_cases (e : Fin n × Fin n) : sortEdge e = e ∨ sortEdge e = e.swap := by
  unfold sortEdge
  split_ifs <;> simp

lemma sortEdge_coincide {e f : Fin n × Fin n} (he : sortEdge e = sortEdge f) :
    e = f ∨ e = f.swap := by
  rcases sortEdge_cases e with hh | hh <;> rcases sortEdge_cases f with hg | hg <;> rw [hh,hg] at he
  · exact Or.inl he
  · exact Or.inr he
  · exact Or.inr (by simpa using congrArg Prod.swap he)
  · exact Or.inl (Prod.swap_injective he)

lemma Drawing.sortEdge_injective (D : Drawing P) :
    (↑D.edges : Set (Fin n × Fin n)).InjOn (@sortEdge n) := by
  intro e he f hf h
  rcases sortEdge_coincide h with h | h
  · exact h
  · have hx := D.right e he
    have hy := D.right f hf
    rw [h] at hx
    exact False.elim (lt_asymm hx hy)

lemma openSegment_sortEdge (e : Fin n × Fin n) :
    openSegment ℝ (P (sortEdge e).1) (P (sortEdge e).2) =
      openSegment ℝ (P e.1) (P e.2) := by
  rcases sortEdge_cases e with h | h
  · rw [h]
  · rw [h]
    exact openSegment_symm ℝ _ _

lemma segment_sortEdge (e : Fin n × Fin n) :
    segment ℝ (P (sortEdge e).1) (P (sortEdge e).2) =
      segment ℝ (P e.1) (P e.2) := by
  rcases sortEdge_cases e with h | h
  · rw [h]
  · rw [h]
    exact segment_symm ℝ _ _

lemma Drawing.noMultiple_of_generic (D : Drawing P) (hP : Generic P) : D.NoMultiple := by
  intro e he f hf hef g hg hge hgf z hze hzf hzg
  have ho (i : Fin n × Fin n) (hi : i ∈ D.edges) : (sortEdge i).1 < (sortEdge i).2 :=
    sortEdge_order i (fun h => (D.right i hi).ne (congrArg (fun v => (P v).1) h))
  have hne {i j : Fin n × Fin n} (hi : i ∈ D.edges) (hj : j ∈ D.edges) (hn : i ≠ j) :
      sortEdge i ≠ sortEdge j := fun h => hn (D.sortEdge_injective hi hj h)
  apply hP.2.2.2 _ _ _ _ _ _ (ho e he) (ho f hf) (ho g hg)
    (hne he hf hef) (hne hg he hge) (hne hg hf hgf) z
  · rwa [openSegment_sortEdge]
  · rwa [openSegment_sortEdge]
  · rwa [segment_sortEdge]

lemma Generic.x_injective (hP : Generic P) : Function.Injective (fun v => (P v).1) := by
  intro i j hij
  by_contra hn
  exact hP.2.1 i j hn hij

end PlanarHalving.PlaneGraph

namespace PlanarHalving.PlaneGraph
variable {V : Type*} [Fintype V] {P : V → Point}

noncomputable def Drawing.restrictEdges (D : Drawing P) (E : Finset (V × V)) : Drawing P := by
  classical
  exact {
    vertices := D.vertices
    edges := D.edges ∩ E
    right := fun e he => D.right e (Finset.mem_inter.mp he).1
    ends := fun e he => D.ends e (Finset.mem_inter.mp he).1 }

end PlanarHalving.PlaneGraph

namespace PlanarHalving.PlaneGraph
lemma height_of_mem_segment {p q z : Point} (hx : p.1 ≠ q.1)
    (hz : z ∈ segment ℝ p q) : z.2 = height p q z.1 := by
  rw [segment_eq_image] at hz
  obtain ⟨t,_,rfl⟩ := hz
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  unfold height slope
  field_simp
  ring
end PlanarHalving.PlaneGraph

namespace PlanarHalving.RankCoordinates
open Set

noncomputable def envelope {ι : Type*} [Fintype ι] [Nonempty ι]
    (m c : ι → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => m i*x+c i)

lemma le_envelope {ι : Type*} [Fintype ι] [Nonempty ι]
    (m c : ι → ℝ) (i : ι) (x : ℝ) : m i*x+c i ≤ envelope m c x :=
  Finset.le_sup' (fun j => m j*x+c j) (Finset.mem_univ i)

lemma envelope_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (m c : ι → ℝ) (x y : ℝ) (h : ∀ i, m i*x+c i ≤ y) : envelope m c x ≤ y :=
  Finset.sup'_le Finset.univ_nonempty _ (fun i _ => h i)

lemma envelope_attains {ι : Type*} [Fintype ι] [Nonempty ι]
    (m c : ι → ℝ) (x : ℝ) : ∃ i, envelope m c x = m i*x+c i := by
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun i => m i*x+c i) Finset.univ_nonempty
  exact ⟨i, le_antisymm (envelope_le m c x _ (fun j => hi j (Finset.mem_univ j))) (le_envelope m c i x)⟩

lemma continuous_envelope {ι : Type*} [Fintype ι] [Nonempty ι]
    (m c : ι → ℝ) : Continuous (envelope m c) := by
  have hh : Continuous (Finset.univ.sup' Finset.univ_nonempty (fun i => fun x : ℝ => m i*x+c i)) :=
    Continuous.finset_sup' Finset.univ_nonempty (fun _ _ => by fun_prop)
  convert hh using 1
  funext x
  simp only [envelope, Finset.sup'_apply]

lemma convexOn_envelope {ι : Type*} [Fintype ι] [Nonempty ι]
    (m c : ι → ℝ) : ConvexOn ℝ Set.univ (envelope m c) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  apply envelope_le
  intro i
  have h₁ := mul_le_mul_of_nonneg_left (le_envelope m c i x) ha
  have h₂ := mul_le_mul_of_nonneg_left (le_envelope m c i y) hb
  calc
    m i * (a*x+b*y)+c i = a*(m i*x+c i)+b*(m i*y+c i) := by
      have hh := congrArg (fun t => t * c i) hab
      nlinarith only [hh]
    _ ≤ _ := add_le_add h₁ h₂

lemma envelope_slopes {ι : Type*} [Fintype ι] [Nonempty ι]
    (m c : ι → ℝ) {l u : ℝ} (hm : ∀ i, l ≤ m i ∧ m i ≤ u)
    {x y : ℝ} (hxy : x ≤ y) :
    l*(y-x) ≤ envelope m c y - envelope m c x ∧
    envelope m c y - envelope m c x ≤ u*(y-x) := by
  obtain ⟨i,hi⟩ := envelope_attains m c x
  obtain ⟨j,hj⟩ := envelope_attains m c y
  have h₁ := le_envelope m c i y
  have h₂ := le_envelope m c j x
  have h₃ := mul_le_mul_of_nonneg_right (hm i).1 (sub_nonneg.mpr hxy)
  have h₄ := mul_le_mul_of_nonneg_right (hm j).2 (sub_nonneg.mpr hxy)
  constructor
  · rw [hi]
    linarith only [h₁,h₃]
  · rw [hj]
    linarith only [h₂,h₄]

end PlanarHalving.RankCoordinates

namespace PlanarHalving.Batches
open PlaneGraph RankCoordinates
variable {R : ℕ}

lemma ConvexPath.lower_ray (C : ConvexPath R) {l : ℝ}
    (hl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ → l ≤ slope (C.point b.castSucc) (C.point b.succ))
    (c : Fin (R+1)) :
    (C.point 0).2 + ( (C.point c).1 - (C.point 0).1)*l ≤ (C.point c).2 := by
  have h := fin_between_le (f := fun r => Sweep.projection l (C.point r)) 0 c (Fin.zero_le c) (by
    intro b _ _
    rcases C.right b with he | he
    · rw [he]
    · have hn : C.point b.castSucc ≠ C.point b.succ := fun h => he.ne (congrArg Prod.fst h)
      have hp := projection_step (C.point b.castSucc) (C.point b.succ) (t := l) he.ne
      have hprod := mul_nonneg (sub_nonneg.mpr he.le) (sub_nonneg.mpr (hl b hn))
      linarith only [hp,hprod])
  unfold Sweep.projection at h
  linarith only [h]

lemma ConvexPath.upper_ray (C : ConvexPath R) {u : ℝ}
    (hu : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ → slope (C.point b.castSucc) (C.point b.succ) ≤ u)
    (c : Fin (R+1)) :
    (C.point (Fin.last R)).2 + ((C.point c).1 - (C.point (Fin.last R)).1)*u ≤ (C.point c).2 := by
  have h := fin_between_le (f := fun r => -Sweep.projection u (C.point r)) c (Fin.last R) (Fin.le_last c) (by
    intro b _ _
    rcases C.right b with he | he
    · rw [he]
    · have hn : C.point b.castSucc ≠ C.point b.succ := fun h => he.ne (congrArg Prod.fst h)
      have hp := projection_step (C.point b.castSucc) (C.point b.succ) (t := u) he.ne
      have hprod := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr he.le) (sub_nonpos.mpr (hu b hn))
      linarith only [hp,hprod])
  unfold Sweep.projection at h
  linarith only [h]

noncomputable def ConvexPath.extensionSlopes (C : ConvexPath R) (l u : ℝ) : Fin R ⊕ Bool → ℝ
  | .inl b => if C.point b.castSucc = C.point b.succ then l else slope (C.point b.castSucc) (C.point b.succ)
  | .inr false => l
  | .inr true => u

noncomputable def ConvexPath.extensionIntercepts (C : ConvexPath R) (l u : ℝ) : Fin R ⊕ Bool → ℝ
  | .inl b => if C.point b.castSucc = C.point b.succ then (C.point 0).2 - l*(C.point 0).1
      else (C.point b.castSucc).2 - slope (C.point b.castSucc) (C.point b.succ)*(C.point b.castSucc).1
  | .inr false => (C.point 0).2 - l*(C.point 0).1
  | .inr true => (C.point (Fin.last R)).2 - u*(C.point (Fin.last R)).1

noncomputable def ConvexPath.extension (C : ConvexPath R) (l u : ℝ) : ℝ → ℝ :=
  envelope (C.extensionSlopes l u) (C.extensionIntercepts l u)

lemma ConvexPath.extension_slopes (C : ConvexPath R) {l u : ℝ} (hlu : l ≤ u)
    (hsl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧ slope (C.point b.castSucc) (C.point b.succ) ≤ u) :
    ∀ i, l ≤ C.extensionSlopes l u i ∧ C.extensionSlopes l u i ≤ u := by
  intro i
  cases i with
  | inl b =>
    by_cases hb : C.point b.castSucc = C.point b.succ
    · simp only [ConvexPath.extensionSlopes, ite_eq_left hb]
      exact ⟨le_rfl,hlu⟩
    · simpa only [ConvexPath.extensionSlopes, ite_eq_right hb] using hsl b hb
  | inr b => cases b <;> simp only [ConvexPath.extensionSlopes] <;> exact ⟨by order, by order⟩

lemma ConvexPath.extension_below_vertex (C : ConvexPath R) {l u : ℝ}
    (hsl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧ slope (C.point b.castSucc) (C.point b.succ) ≤ u)
    (c : Fin (R+1)) : C.extension l u (C.point c).1 ≤ (C.point c).2 := by
  apply envelope_le
  intro i
  have hl := C.lower_ray (fun b hb => (hsl b hb).1) c
  have hu := C.upper_ray (fun b hb => (hsl b hb).2) c
  cases i with
  | inl b =>
    by_cases hb : C.point b.castSucc = C.point b.succ
    · simp only [ConvexPath.extensionSlopes, ConvexPath.extensionIntercepts, ite_eq_left hb]
      linarith only [hl]
    · simp only [ConvexPath.extensionSlopes, ConvexPath.extensionIntercepts, ite_eq_right hb]
      have hh := C.support_vertex b hb c
      unfold height at hh
      linarith only [hh]
  | inr b => cases b <;> simp only [ConvexPath.extensionSlopes, ConvexPath.extensionIntercepts] <;> linarith only [hl,hu]

lemma ConvexPath.extension_edge (C : ConvexPath R) {l u : ℝ}
    (hsl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧ slope (C.point b.castSucc) (C.point b.succ) ≤ u)
    (b : Fin R) (hb : C.point b.castSucc ≠ C.point b.succ) {z : Point}
    (hz : z ∈ segment ℝ (C.point b.castSucc) (C.point b.succ)) :
    C.extension l u z.1 = z.2 := by
  apply le_antisymm
  · rw [segment_eq_image] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    have hc := convexOn_envelope (C.extensionSlopes l u) (C.extensionIntercepts l u)
    have hh := hc.2 (Set.mem_univ (C.point b.castSucc).1) (Set.mem_univ (C.point b.succ).1)
      (sub_nonneg.mpr ht.2) ht.1 (by ring : (1-t)+t=1)
    have h₀ := mul_le_mul_of_nonneg_left (C.extension_below_vertex hsl b.castSucc) (sub_nonneg.mpr ht.2)
    have h₁ := mul_le_mul_of_nonneg_left (C.extension_below_vertex hsl b.succ) ht.1
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at *
    exact hh.trans (add_le_add h₀ h₁)
  · have hh := le_envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) (.inl b) z.1
    simp only [ConvexPath.extensionSlopes, ConvexPath.extensionIntercepts, ite_eq_right hb] at hh
    have hz' := height_of_mem_segment (C.right b |>.resolve_left hb).ne hz
    unfold height at hz'
    change z.2 ≤ envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) z.1
    linarith only [hh,hz']

end PlanarHalving.Batches

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.PathLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Batches
open PlaneGraph RankCoordinates
variable {R : ℕ}

lemma ConvexPath.extension_vertex (C : ConvexPath R) {l u : ℝ}
    (hsl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧ slope (C.point b.castSucc) (C.point b.succ) ≤ u)
    (c : Fin (R+1)) : C.extension l u (C.point c).1 = (C.point c).2 := by
  induction c using Fin.induction with
  | zero =>
    apply le_antisymm (C.extension_below_vertex hsl 0)
    have hh := le_envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) (.inr false) (C.point 0).1
    simp only [ConvexPath.extensionSlopes, ConvexPath.extensionIntercepts] at hh
    change _ ≤ envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) (C.point 0).1
    linarith only [hh]
  | succ b ih =>
    by_cases hb : C.point b.castSucc = C.point b.succ
    · rw [← hb]
      exact ih
    · exact C.extension_edge hsl b hb (right_mem_segment ℝ _ _)

lemma ConvexPath.extension_left (C : ConvexPath R) {l u : ℝ} (hlu : l ≤ u)
    (hsl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧ slope (C.point b.castSucc) (C.point b.succ) ≤ u)
    {x : ℝ} (hx : x ≤ (C.point 0).1) :
    C.extension l u x = (C.point 0).2 + l*(x-(C.point 0).1) := by
  apply le_antisymm
  · apply envelope_le
    intro i
    have hi := le_envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) i (C.point 0).1
    change _ ≤ C.extension l u (C.point 0).1 at hi
    rw [C.extension_vertex hsl] at hi
    have hm := mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr (C.extension_slopes hlu hsl i).1) (sub_nonpos.mpr hx)
    nlinarith only [hi,hm]
  · have hh := le_envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) (.inr false) x
    simp only [ConvexPath.extensionSlopes, ConvexPath.extensionIntercepts] at hh
    change _ ≤ envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) x
    linarith only [hh]

lemma ConvexPath.extension_right (C : ConvexPath R) {l u : ℝ} (hlu : l ≤ u)
    (hsl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧ slope (C.point b.castSucc) (C.point b.succ) ≤ u)
    {x : ℝ} (hx : (C.point (Fin.last R)).1 ≤ x) :
    C.extension l u x = (C.point (Fin.last R)).2 + u*(x-(C.point (Fin.last R)).1) := by
  apply le_antisymm
  · apply envelope_le
    intro i
    have hi := le_envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) i (C.point (Fin.last R)).1
    change _ ≤ C.extension l u (C.point (Fin.last R)).1 at hi
    rw [C.extension_vertex hsl] at hi
    have hm := mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (C.extension_slopes hlu hsl i).2) (sub_nonneg.mpr hx)
    nlinarith only [hi,hm]
  · have hh := le_envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) (.inr true) x
    simp only [ConvexPath.extensionSlopes, ConvexPath.extensionIntercepts] at hh
    change _ ≤ envelope (C.extensionSlopes l u) (C.extensionIntercepts l u) x
    linarith only [hh]

lemma finite_intermediate {R : ℕ} (f : Fin (R+1) → ℝ) {x : ℝ}
    (h₀ : f 0 ≤ x) (h₁ : x < f (Fin.last R)) :
    ∃ b : Fin R, f b.castSucc ≤ x ∧ x < f b.succ := by
  have haux : ∀ c : Fin (R+1), x < f c → ∃ b : Fin R, f b.castSucc ≤ x ∧ x < f b.succ := by
    intro c
    induction c using Fin.induction with
    | zero => exact fun h => (not_lt_of_ge h₀ h).elim
    | succ b ih =>
      intro h
      by_cases hb : f b.castSucc ≤ x
      · exact ⟨b,hb,h⟩
      · exact ih (lt_of_not_ge hb)
  exact haux (Fin.last R) h₁

lemma ConvexPath.extension_middle (C : ConvexPath R) {l u : ℝ}
    (hsl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧ slope (C.point b.castSucc) (C.point b.succ) ≤ u)
    {x : ℝ} (h₀ : (C.point 0).1 ≤ x) (h₁ : x < (C.point (Fin.last R)).1) :
    ∃ b : Fin R, C.point b.castSucc ≠ C.point b.succ ∧
      (x,C.extension l u x) ∈ segment ℝ (C.point b.castSucc) (C.point b.succ) := by
  obtain ⟨b,hb₀,hb₁⟩ := finite_intermediate (fun c => (C.point c).1) h₀ h₁
  have hbx : (C.point b.castSucc).1 < (C.point b.succ).1 := hb₀.trans_lt hb₁
  have hb : C.point b.castSucc ≠ C.point b.succ := fun h => hbx.ne (congrArg Prod.fst h)
  let t := (x-(C.point b.castSucc).1)/((C.point b.succ).1-(C.point b.castSucc).1)
  have ht : t ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr hb₀) (sub_nonneg.mpr hbx.le), ?_⟩
    exact (div_le_one (sub_pos.mpr hbx)).mpr (by linarith only [hb₁])
  let z : Point := (1-t) • C.point b.castSucc + t • C.point b.succ
  have hz : z ∈ segment ℝ (C.point b.castSucc) (C.point b.succ) := by
    rw [segment_eq_image]
    exact ⟨t,ht,rfl⟩
  have hzx : z.1 = x := by
    dsimp [z,t]
    field_simp [ne_of_gt (sub_pos.mpr hbx)]
    ring
  have hzy := C.extension_edge hsl b hb hz
  rw [hzx] at hzy
  have he : (x,C.extension l u x) = z := Prod.ext hzx.symm hzy
  exact ⟨b,hb,he ▸ hz⟩

lemma ConvexPath.extension_cases (C : ConvexPath R) {l u : ℝ} (hlu : l ≤ u)
    (hsl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧ slope (C.point b.castSucc) (C.point b.succ) ≤ u)
    {z : Point} (hz : C.extension l u z.1 = z.2) :
    (z.1 ≤ (C.point 0).1 ∧ z.2 = (C.point 0).2 + l*(z.1-(C.point 0).1)) ∨
    ((C.point (Fin.last R)).1 ≤ z.1 ∧ z.2 = (C.point (Fin.last R)).2 + u*(z.1-(C.point (Fin.last R)).1)) ∨
    (∃ b : Fin R, C.point b.castSucc ≠ C.point b.succ ∧ z ∈ segment ℝ (C.point b.castSucc) (C.point b.succ)) := by
  by_cases hl : z.1 ≤ (C.point 0).1
  · exact Or.inl ⟨hl, hz.symm.trans (C.extension_left hlu hsl hl)⟩
  by_cases hu : (C.point (Fin.last R)).1 ≤ z.1
  · exact Or.inr (Or.inl ⟨hu,hz.symm.trans (C.extension_right hlu hsl hu)⟩)
  obtain ⟨b,hb,hz'⟩ := C.extension_middle hsl (le_of_not_ge hl) (lt_of_not_ge hu)
  rw [hz] at hz'
  exact Or.inr (Or.inr ⟨b,hb,hz'⟩)

end PlanarHalving.Batches

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Tokens
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankCoordinates
open Set

lemma exists_slope_avoiding (p : Point) (F : Finset Point) {l u : ℝ}
    (hlu : l < u) (hp : p ∉ F) :
    ∃ s ∈ Ioo l u, ∀ z ∈ F, z.2 ≠ p.2+s*(z.1-p.1) := by
  classical
  obtain ⟨s,hs,havoid⟩ := (Ioo_infinite hlu).exists_notMem_finset
    (F.image (fun z => (z.2-p.2)/(z.1-p.1)))
  refine ⟨s,hs,?_⟩
  intro z hz he
  by_cases hx : z.1 = p.1
  · have heq : z = p := Prod.ext hx (by rw [hx,sub_self,mul_zero,add_zero] at he; exact he)
    exact hp (heq ▸ hz)
  · apply havoid
    apply Finset.mem_image.mpr
    refine ⟨z,hz,?_⟩
    apply (div_eq_iff (sub_ne_zero.mpr hx)).mpr
    linarith only [he]

lemma exists_affine_avoiding (F : Finset Point) (s : ℝ) :
    ∃ c : ℝ, ∀ z ∈ F, s*z.1+c ≠ z.2 := by
  classical
  obtain ⟨c,_,hc⟩ := (Set.infinite_univ : (Set.univ : Set ℝ).Infinite).exists_notMem_finset
    (F.image (fun z => z.2-s*z.1))
  refine ⟨c,?_⟩
  intro z hz he
  apply hc
  exact Finset.mem_image.mpr ⟨z,hz,by linarith only [he]⟩

end PlanarHalving.RankCoordinates

namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates
variable {R : ℕ}

lemma ConvexPath.interior_slopes (C : ConvexPath R) {L U : ℝ}
    (hLU : L < U)
    (hedge : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      L < slope (C.point b.castSucc) (C.point b.succ) ∧
      slope (C.point b.castSucc) (C.point b.succ) < U) :
    ∃ l u : ℝ, L < l ∧ l ≤ u ∧ u < U ∧
      ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
        l < slope (C.point b.castSucc) (C.point b.succ) ∧
        slope (C.point b.castSucc) (C.point b.succ) < u := by
  classical
  let E := Finset.univ.filter (fun b : Fin R => C.point b.castSucc ≠ C.point b.succ)
  by_cases he : E.Nonempty
  · obtain ⟨b,hb,hbmin⟩ := Finset.exists_min_image E
      (fun b => slope (C.point b.castSucc) (C.point b.succ)) he
    obtain ⟨c,hc,hcmax⟩ := Finset.exists_max_image E
      (fun b => slope (C.point b.castSucc) (C.point b.succ)) he
    have hb' := (Finset.mem_filter.mp hb).2
    have hc' := (Finset.mem_filter.mp hc).2
    obtain ⟨l,hlL,hl⟩ := exists_between (hedge b hb').1
    obtain ⟨u,hu,huU⟩ := exists_between (hedge c hc').2
    refine ⟨l,u,hlL,((hl.trans_le (hbmin c hc)).trans hu).le,huU,?_⟩
    intro i hi
    have hi' : i ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩
    exact ⟨hl.trans_le (hbmin i hi'),(hcmax i hi').trans_lt hu⟩
  · obtain ⟨l,hlL,hlU⟩ := exists_between hLU
    refine ⟨l,l,hlL,le_rfl,hlU,?_⟩
    intro b hb
    exact (he ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩⟩).elim

lemma ConvexPath.exists_clean_extension (C : ConvexPath R) (F : Finset Point)
    {L U : ℝ} (hLU : L < U)
    (hp₀ : C.point 0 ∉ F) (hp₁ : C.point (Fin.last R) ∉ F)
    (hedge : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      L < slope (C.point b.castSucc) (C.point b.succ) ∧
      slope (C.point b.castSucc) (C.point b.succ) < U) :
    ∃ l u : ℝ, L < l ∧ l ≤ u ∧ u < U ∧
      (∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
        l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧
        slope (C.point b.castSucc) (C.point b.succ) ≤ u) ∧
      ∀ z ∈ F, C.extension l u z.1 = z.2 →
        ∃ b : Fin R, C.point b.castSucc ≠ C.point b.succ ∧
          z ∈ segment ℝ (C.point b.castSucc) (C.point b.succ) := by
  obtain ⟨l₀,u₀,hl₀,hlu₀,hu₀,hs₀⟩ := C.interior_slopes hLU hedge
  obtain ⟨l,hl,hlavoid⟩ := exists_slope_avoiding (C.point 0) F hl₀ hp₀
  obtain ⟨u,hu,huavoid⟩ := exists_slope_avoiding (C.point (Fin.last R)) F hu₀ hp₁
  have hlu : l ≤ u := ((hl.2.trans_le hlu₀).trans hu.1).le
  have hs (b : Fin R) (hb : C.point b.castSucc ≠ C.point b.succ) :
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧
      slope (C.point b.castSucc) (C.point b.succ) ≤ u :=
    ⟨(hl.2.trans (hs₀ b hb).1).le,((hs₀ b hb).2.trans hu.1).le⟩
  refine ⟨l,u,hl.1,hlu,hu.2,hs,?_⟩
  intro z hz hgraph
  rcases C.extension_cases hlu hs hgraph with hleft | hright | hmiddle
  · exact (hlavoid z hz hleft.2).elim
  · exact (huavoid z hz hright.2).elim
  · exact hmiddle

end PlanarHalving.Batches

namespace PlanarHalving.RankCoordinates
open Set

noncomputable def slot {ι : Type*} [Fintype ι] (g : ι → ℝ → ℝ) (p : Point) : ℕ :=
  (Finset.univ.filter (fun i => g i p.1 < p.2)).card

end PlanarHalving.RankCoordinates

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.AtomicBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.EdgeTrace.match_eq (S : @System n R k a P) [NeZero a]
    {e : Fin n × Fin n} (t : S.EdgeTrace e) :
    S.match t.number t.batch ⟨e.1,t.loss⟩ = ⟨e.2,t.gain⟩ := by
  apply Subtype.ext
  have hn : (S.tokenState t.number t.batch.castSucc t.token : Fin n) ∉ S.marks t.batch.succ := by
    rw [t.source]
    exact (Finset.mem_sdiff.mp t.loss).2
  have ht := t.target
  rw [S.tokenState_succ] at ht
  change (transport _ _ (S.match t.number t.batch) _ : Fin n) = e.2 at ht
  rw [transport_of_not_mem (S.match t.number t.batch) _ hn] at ht
  convert ht using 1
  apply congrArg (fun v : ↥(S.loss t.batch) => (S.match t.number t.batch v : Fin n))
  exact Subtype.ext t.source.symm

lemma System.EdgeTrace.same_path (S : @System n R k a P) [NeZero a]
    {e : Fin n × Fin n} (t t' : S.EdgeTrace e) :
    t.number = t'.number ∧ t.token = t'.token := by
  have hm₀ := t.match_eq S
  have hm₁ := t'.match_eq S
  rcases t with ⟨b,j,v,hs,ht,hl,hg⟩
  rcases t' with ⟨b',j',v',hs',ht',hl',hg'⟩
  have hb : b = b' := S.batch_unique ⟨hl,hg⟩ ⟨hl',hg'⟩
  subst b'
  have hj : j = j' := (matching_unique (S.lossIndex b) (S.gainIndex b)
    ⟨e.1,hl⟩ ⟨e.2,hg⟩).unique hm₀ hm₁
  refine ⟨hj,?_⟩
  apply (S.tokenState j b.castSucc).injective
  apply Subtype.ext
  rw [hs,hj,hs']

lemma System.convexOwner_of_trace (S : @System n R k a P) [NeZero n] [NeZero a]
    {e : Fin n × Fin n} (t : S.EdgeTrace e) :
    S.convexOwner e = (t.number,t.token.val) := by
  have he : e ∈ S.edges := (S.mem_edges e).mpr ⟨t.batch,t.loss,t.gain⟩
  rw [S.convexOwner_eq he]
  obtain ⟨hj,ht⟩ := (S.trace he).same_path S t
  rw [hj,ht]

lemma System.tokenPath_bounds (S : @System n R k a P) [NeZero a]
    (j : Fin a) (v : ↥(S.marks 0)) (b : Fin R)
    (hb : (S.tokenPath j v).point b.castSucc ≠ (S.tokenPath j v).point b.succ) :
    S.slope 0 < PlanarHalving.slope ((S.tokenPath j v).point b.castSucc) ((S.tokenPath j v).point b.succ) ∧
    PlanarHalving.slope ((S.tokenPath j v).point b.castSucc) ((S.tokenPath j v).point b.succ) < S.slope (Fin.last R) := by
  have hstep := (S.token_step j v b).resolve_left (fun h => hb (congrArg P h))
  have h := S.edge_slope b hstep.1 hstep.2
  exact ⟨(S.increasing.monotone (Fin.zero_le _)).trans_lt h.1,
    h.2.trans_le (S.increasing.monotone (Fin.le_last _))⟩

lemma System.tokenPath_segment_owner (S : @System n R k a P) [NeZero n] [NeZero a]
    (j : Fin a) (v : ↥(S.marks 0)) (b : Fin R)
    (hb : (S.tokenPath j v).point b.castSucc ≠ (S.tokenPath j v).point b.succ)
    {z : Point} (hz : z ∈ segment ℝ ((S.tokenPath j v).point b.castSucc) ((S.tokenPath j v).point b.succ)) :
    ∃ e ∈ S.edges, S.convexOwner e = (j,v.val) ∧ z ∈ segment ℝ (P e.1) (P e.2) := by
  have hstep := (S.token_step j v b).resolve_left (fun h => hb (congrArg P h))
  let e : Fin n × Fin n := ((S.tokenState j b.castSucc v).val,(S.tokenState j b.succ v).val)
  let t : S.EdgeTrace e := ⟨b,j,v,rfl,rfl,hstep.1,hstep.2⟩
  exact ⟨e,(S.mem_edges e).mpr ⟨b,hstep⟩,S.convexOwner_of_trace t,hz⟩

lemma System.exists_graph (S : @System n R k a P) [NeZero n] [NeZero a]
    (hR : 0 < R) (F : Finset Point) (hF : ∀ v, P v ∉ F) (i : Fin a × Fin n) :
    ∃ (l u : ℝ) (g : ℝ → ℝ), S.slope 0 < l ∧ l ≤ u ∧ u < S.slope (Fin.last R) ∧
      Continuous g ∧ ConvexOn ℝ univ g ∧
      (∀ x y, x ≤ y → l*(y-x) ≤ g y-g x ∧ g y-g x ≤ u*(y-x)) ∧
      (∀ e ∈ S.edges, S.convexOwner e = i → ∀ z ∈ segment ℝ (P e.1) (P e.2), g z.1 = z.2) ∧
      (∀ z ∈ F, g z.1 = z.2 → ∃ e ∈ S.edges, S.convexOwner e = i ∧ z ∈ segment ℝ (P e.1) (P e.2)) := by
  classical
  have hspan : S.slope 0 < S.slope (Fin.last R) := S.increasing (by simpa only [Fin.lt_def, Fin.val_zero, Fin.val_last] using hR)
  by_cases hi : i.2 ∈ S.marks 0
  · let v : ↥(S.marks 0) := ⟨i.2,hi⟩
    let C := S.tokenPath i.1 v
    have h₀ : C.point 0 ∉ F := hF _
    have h₁ : C.point (Fin.last R) ∉ F := hF _
    obtain ⟨l,u,hl,hlu,hu,hs,hclean⟩ := C.exists_clean_extension F hspan h₀ h₁ (S.tokenPath_bounds i.1 v)
    refine ⟨l,u,C.extension l u,hl,hlu,hu,
      continuous_envelope _ _,convexOn_envelope _ _,?_,?_,?_⟩
    · intro x y hxy
      exact envelope_slopes _ _ (C.extension_slopes hlu hs) hxy
    · intro e he heowner z hz
      have howner := S.convexOwner_eq he
      rw [heowner] at howner
      have hj : (S.trace he).number = i.1 := congrArg Prod.fst howner.symm
      have hv : (S.trace he).token = v := Subtype.ext (congrArg Prod.snd howner.symm)
      have hsrc : C.point (S.trace he).batch.castSucc = P e.1 := by
        simpa only [C,System.tokenPath,hj,hv] using congrArg P (S.trace he).source
      have htgt : C.point (S.trace he).batch.succ = P e.2 := by
        simpa only [C,System.tokenPath,hj,hv] using congrArg P (S.trace he).target
      have hne : C.point (S.trace he).batch.castSucc ≠ C.point (S.trace he).batch.succ := by
        rw [hsrc,htgt]
        exact fun heq => (S.drawing.right e he).ne (congrArg Prod.fst heq)
      exact C.extension_edge hs _ hne (by rwa [hsrc,htgt])
    · intro z hz hg
      obtain ⟨b,hb,hz'⟩ := hclean z hz hg
      exact S.tokenPath_segment_owner i.1 v b hb hz'
  · obtain ⟨l,hl,hu⟩ := exists_between hspan
    obtain ⟨c,hc⟩ := exists_affine_avoiding F l
    refine ⟨l,l,fun x => l*x+c,hl,le_rfl,hu,by fun_prop,?_,?_,?_,?_⟩
    · refine ⟨convex_univ, ?_⟩
      intro x _ y _ p q _ _ hpq
      simp only [smul_eq_mul]
      nlinarith [congrArg (fun t : ℝ => c*t) hpq]
    · intro x y _
      constructor <;> ring_nf <;> exact le_rfl
    · intro e he howner
      have ho := S.convexOwner_eq he
      rw [howner] at ho
      have hv := congrArg Prod.snd ho
      exact (hi (hv ▸ (S.trace he).token.property)).elim
    · intro z hz hg
      exact (hc z hz hg).elim

end PlanarHalving.Batches

namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates
variable {n R k a : ℕ} {P : Fin n → Point}

structure System.FullGraphs (S : @System n R k a P) [NeZero n] [NeZero a] (F : Finset Point) where
  lower : ℝ
  upper : ℝ
  lower_lt : S.slope 0 < lower
  lower_le_upper : lower ≤ upper
  upper_lt : upper < S.slope (Fin.last R)
  graph : Fin (a*n) → ℝ → ℝ
  continuous : ∀ i, Continuous (graph i)
  convex : ∀ i, ConvexOn ℝ univ (graph i)
  slopes : ∀ i x y, x ≤ y → lower*(y-x) ≤ graph i y-graph i x ∧
    graph i y-graph i x ≤ upper*(y-x)
  edge : ∀ e ∈ S.edges, ∀ z ∈ segment ℝ (P e.1) (P e.2),
    graph (finProdFinEquiv (S.convexOwner e)) z.1 = z.2
  clean : ∀ i z, z ∈ F → graph i z.1 = z.2 → ∃ e ∈ S.edges,
    finProdFinEquiv (S.convexOwner e) = i ∧ z ∈ segment ℝ (P e.1) (P e.2)

lemma System.fullGraphs_nonempty (S : @System n R k a P) [NeZero n] [NeZero a]
    (hR : 0 < R) (F : Finset Point) (hF : ∀ v, P v ∉ F) :
    Nonempty (S.FullGraphs F) := by
  classical
  choose l u g hl hlu hu hc hv hs he hclean using S.exists_graph hR F hF
  let ι := Fin a × Fin n
  let ls : Finset ℝ := Finset.univ.image l
  let us : Finset ℝ := Finset.univ.image u
  have hls : ls.Nonempty := ⟨l (0,0),Finset.mem_image.mpr ⟨(0,0),Finset.mem_univ _,rfl⟩⟩
  have hus : us.Nonempty := ⟨u (0,0),Finset.mem_image.mpr ⟨(0,0),Finset.mem_univ _,rfl⟩⟩
  let L := ls.min' hls
  let U := us.max' hus
  have hL i : L ≤ l i := Finset.min'_le ls _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have hU i : u i ≤ U := Finset.le_max' us _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have hL' : S.slope 0 < L := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.min'_mem ls hls)
    change S.slope 0 < ls.min' hls
    rw [← hi]
    exact hl i
  have hU' : U < S.slope (Fin.last R) := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.max'_mem us hus)
    change us.max' hus < S.slope (Fin.last R)
    rw [← hi]
    exact hu i
  refine ⟨⟨L,U,hL',(hL (0,0)).trans ((hlu (0,0)).trans (hU (0,0))),hU',
    fun i => g (finProdFinEquiv.symm i),fun i => hc _,fun i => hv _,?_,?_,?_⟩⟩
  · intro i x y hxy
    exact ⟨(mul_le_mul_of_nonneg_right (hL _) (sub_nonneg.mpr hxy)).trans (hs _ x y hxy).1,
      (hs _ x y hxy).2.trans (mul_le_mul_of_nonneg_right (hU _) (sub_nonneg.mpr hxy))⟩
  · intro e hh z hz
    simpa only [Equiv.symm_apply_apply] using he (S.convexOwner e) e hh rfl z hz
  · intro i z hz hgz
    obtain ⟨e,hh,ho,hz'⟩ := hclean _ z hz hgz
    exact ⟨e,hh,by rw [ho,Equiv.apply_symm_apply],hz'⟩

noncomputable def System.fullGraphs (S : @System n R k a P) [NeZero n] [NeZero a]
    (hR : 0 < R) (F : Finset Point) (hF : ∀ v, P v ∉ F) : S.FullGraphs F :=
  Classical.choice (S.fullGraphs_nonempty hR F hF)

lemma System.FullGraphs.unique_incidence (S : @System n R k a P) [NeZero n] [NeZero a]
    {F : Finset Point} (G : S.FullGraphs F)
    (hF : ∀ z ∈ F, ∀ e ∈ S.edges, ∀ f ∈ S.edges,
      z ∈ segment ℝ (P e.1) (P e.2) → z ∈ segment ℝ (P f.1) (P f.2) → e = f)
    {z : Point} (hz : z ∈ F) {i j : Fin (a*n)}
    (hi : G.graph i z.1 = z.2) (hj : G.graph j z.1 = z.2) : i = j := by
  obtain ⟨e,he,hei,hze⟩ := G.clean i z hz hi
  obtain ⟨f,hf,hfj,hzf⟩ := G.clean j z hz hj
  have h := hF z hz e he f hf hze hzf
  rw [← hei,← hfj,h]

end PlanarHalving.Batches

namespace PlanarHalving.RankCoordinates
open Filter Set
open scoped Topology
lemma sigmoid_scale_limit {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun t : ℝ => Real.sigmoid (x*t)) atTop (𝓝 (if 0 < x then 1 else 0)) := by
  split_ifs with h
  · exact Real.tendsto_sigmoid_atTop.comp ((tendsto_const_mul_atTop_of_pos h).mpr tendsto_id)
  · exact Real.tendsto_sigmoid_atBot.comp
      ((tendsto_const_mul_atBot_of_neg (lt_of_le_of_ne (le_of_not_gt h) hx)).mpr tendsto_id)

lemma smoothed_scale_limit {m : ℕ} (g : Fin m → ℝ → ℝ) {p : Point} (j : Fin m)
    (hj : g j p.1 = p.2) (hunique : ∀ i, g i p.1 = p.2 → i = j) :
    Tendsto (fun t : ℝ => smoothed g (1/t) p) atTop
      (𝓝 (((slot g p : ℝ) + 1/2)/m)) := by
  classical
  have hlim (i : Fin m) : Tendsto (fun t : ℝ => Real.sigmoid ((p.2-g i p.1)*t)) atTop
      (𝓝 ((if g i p.1 < p.2 then (1:ℝ) else 0) + if i = j then 1/2 else 0)) := by
    by_cases hi : i = j
    · subst i
      simp only [hj,lt_self_iff_false,ite_false,ite_true,sub_self,zero_mul,Real.sigmoid_zero,zero_add]
      simpa only [one_div] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2:ℝ)⁻¹) atTop (𝓝 (2:ℝ)⁻¹))
    · have hn : p.2-g i p.1 ≠ 0 := fun h => hi (hunique i (sub_eq_zero.mp h).symm)
      simpa only [sub_pos,hi,ite_false,add_zero] using sigmoid_scale_limit hn
  have ht := (tendsto_finsetSum Finset.univ (fun i _ => hlim i)).div_const (m : ℝ)
  have hs : (∑ i : Fin m, ((if g i p.1 < p.2 then (1:ℝ) else 0) + if i = j then 1/2 else 0)) =
      (slot g p : ℝ) + 1/2 := by
    rw [Finset.sum_add_distrib]
    simp [slot]
  rw [hs] at ht
  simpa only [smoothed,one_div,div_inv_eq_mul] using ht

theorem exists_smoothing_slot_error {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ → ℝ)
    (F : Finset Point) (hF : ∀ p ∈ F, ∃! j, g j p.1 = p.2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ F, |smoothed g ε p - (slot g p : ℝ)/m| ≤ 2/m := by
  classical
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hev : ∀ᶠ t : ℝ in atTop, ∀ p ∈ F,
      |smoothed g (1/t) p - (slot g p : ℝ)/m| ≤ 2/m := by
    rw [Filter.eventually_all_finset]
    intro p hp
    obtain ⟨j,hj,hju⟩ := hF p hp
    have ht := ((smoothed_scale_limit g j hj hju).sub_const ((slot g p : ℝ)/m)).abs
    have hb : |((slot g p : ℝ)+1/2)/m-(slot g p : ℝ)/m| < 2/m := by
      rw [add_div,add_sub_cancel_left,abs_of_pos (div_pos (by norm_num) hmR)]
      exact div_lt_div_of_pos_right (by norm_num) hmR
    exact (ht.eventually_lt_const hb).mono (fun _ h => h.le)
  obtain ⟨t,ht,hp⟩ := ( (eventually_gt_atTop (0:ℝ)).and hev).exists
  exact ⟨1/t,div_pos zero_lt_one ht,hp⟩
end PlanarHalving.RankCoordinates

namespace PlanarHalving.Batches
open Set PlaneGraph
variable {n R k a : ℕ} {P : Fin n → Point}

def System.window (S : @System n R k a P) (start len : ℕ) (h : start+len ≤ R) :
    @System n len k a P where
  slope b := S.slope ⟨start+b.val,by omega⟩
  increasing := by
    intro b c hbc
    apply S.increasing
    simpa only [Fin.lt_def] using Nat.add_lt_add_left hbc start
  marks b := S.marks ⟨start+b.val,by omega⟩
  card_marks _ := S.card_marks _
  separates _ := S.separates _
  distance b := S.distance ⟨start+b.val,by omega⟩

lemma System.window_edges (S : @System n R k a P) (start len : ℕ) (h : start+len ≤ R) :
    (S.window start len h).edges ⊆ S.edges := by
  intro e he
  obtain ⟨b,hb,hc⟩ := ((S.window start len h).mem_edges e).mp he
  exact (S.mem_edges e).mpr ⟨⟨start+b.val,by omega⟩,hb,hc⟩

end PlanarHalving.Batches

namespace PlanarHalving.PlaneGraph
open Set
variable {n : ℕ} {P : Fin n → Point}

lemma Generic.not_vertex_on_openSegment (hP : Generic P) {i j : Fin n}
    (hij : (P i).1 < (P j).1) (v : Fin n) :
    P v ∉ openSegment ℝ (P i) (P j) := by
  intro hv
  have hbounds := openSegment_horizontal_bounds hij hv
  have hheight := (height_of_mem_openSegment hij.ne hv).2
  have hzero : orient (P i) (P j) (P v) = 0 := by
    rw [orient_eq_proj_diff _ _ _ hij.ne.symm]
    have hh : (P v).2 - slope (P i) (P j) * (P v).1 -
        ((P i).2 - slope (P i) (P j) * (P i).1) = 0 := by
      unfold height at hheight
      nlinarith only [hheight]
    rw [hh,mul_zero]
  have hne : i ≠ j := by intro h; subst j; exact lt_irrefl _ hij
  rcases (orient_zero_iff hP.1 hne v).mp hzero with rfl | rfl
  · exact lt_irrefl _ hbounds.1
  · exact lt_irrefl _ hbounds.2

noncomputable def Drawing.exteriorCrossings (D : Drawing P) (E : Finset (Fin n × Fin n)) :
    Finset Point := by
  classical
  exact (Finset.univ.filter (fun w : ↥D.crossings =>
    (w.val.1 ∈ E ∧ w.val.2 ∉ E) ∨ (w.val.2 ∈ E ∧ w.val.1 ∉ E))).image D.crossingPoint

lemma Drawing.exteriorCrossings_not_vertex (D : Drawing P) (hP : Generic P)
    (E : Finset (Fin n × Fin n)) (v : Fin n) : P v ∉ D.exteriorCrossings E := by
  classical
  intro hv
  obtain ⟨w,_,hw⟩ := Finset.mem_image.mp hv
  have hz := (D.crossingPoint_mem w).1
  rw [hw] at hz
  exact Generic.not_vertex_on_openSegment hP (D.right _ (D.crossing_props w).1) v hz

lemma Drawing.exteriorCrossings_unique (D : Drawing P) (hD : D.NoMultiple)
    {E : Finset (Fin n × Fin n)} (hE : E ⊆ D.edges) {z : Point}
    (hz : z ∈ D.exteriorCrossings E) :
    ∃! e, e ∈ E ∧ z ∈ segment ℝ (P e.1) (P e.2) := by
  classical
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
  have hw' := (Finset.mem_filter.mp hw).2
  have hp := D.crossing_props w
  have hm := D.crossingPoint_mem w
  have hne : w.val.1 ≠ w.val.2 := fun h => hp.2.2.1.ne (congrArg edgeIndex h)
  have hloc (g : Fin n × Fin n) (hg : g ∈ E)
      (hm : D.crossingPoint w ∈ segment ℝ (P g.1) (P g.2)) :
      g = w.val.1 ∨ g = w.val.2 := by
    by_contra hh
    push Not at hh
    exact hD _ hp.1 _ hp.2.1 hne _ (hE hg) hh.1 hh.2 _
      (D.crossingPoint_mem w).1 (D.crossingPoint_mem w).2 hm
  rcases hw' with hw' | hw'
  · refine ⟨w.val.1,⟨hw'.1,openSegment_subset_segment ℝ _ _ hm.1⟩,?_⟩
    intro g hg
    exact (hloc g hg.1 hg.2).resolve_right (fun h => hw'.2 (h ▸ hg.1))
  · refine ⟨w.val.2,⟨hw'.1,openSegment_subset_segment ℝ _ _ hm.2⟩,?_⟩
    intro g hg
    exact (hloc g hg.1 hg.2).resolve_left (fun h => hw'.2 (h ▸ hg.1))

end PlanarHalving.PlaneGraph

namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates
variable {n R k a : ℕ} {P : Fin n → Point}

theorem System.window_coordinate (S : @System n R k a P) [NeZero n] [NeZero a]
    (hP : Generic P) (s l : ℕ) (h : s+l ≤ R) (hl : 0 < l) :
    ∃ (G : (S.window s l h).FullGraphs (S.drawing.exteriorCrossings (S.window s l h).edges))
      (ε : ℝ), 0 < ε ∧
      ∀ z ∈ S.drawing.exteriorCrossings (S.window s l h).edges,
        |smoothed G.graph ε z-(slot G.graph z : ℝ)/(a*n)| ≤ 2/(a*n) := by
  let T := S.window s l h
  let F := S.drawing.exteriorCrossings T.edges
  let G := T.fullGraphs hl F (S.drawing.exteriorCrossings_not_vertex hP T.edges)
  have hf (z : Point) (hz : z ∈ F) : ∃! j, G.graph j z.1 = z.2 := by
    obtain ⟨e,he,_⟩ := S.drawing.exteriorCrossings_unique (S.drawing.noMultiple_of_generic hP)
      (S.window_edges s l h) hz
    refine ⟨finProdFinEquiv (T.convexOwner e),G.edge e he.1 z he.2,?_⟩
    intro j hj
    apply G.unique_incidence T (fun q hq e he f hf hqe hqf => ?_) hz hj (G.edge e he.1 z he.2)
    obtain ⟨b,_,hb⟩ := S.drawing.exteriorCrossings_unique (S.drawing.noMultiple_of_generic hP)
      (S.window_edges s l h) hq
    exact (hb e ⟨he,hqe⟩).trans (hb f ⟨hf,hqf⟩).symm
  obtain ⟨ε,hε,herr⟩ := exists_smoothing_slot_error (Nat.mul_pos (NeZero.pos a) (NeZero.pos n)) G.graph F hf
  exact ⟨G,ε,hε,by simpa only [Nat.cast_mul] using herr⟩

end PlanarHalving.Batches

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Partition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.UniformPartition
open MeasureTheory Set
open scoped unitInterval

noncomputable def boundary (m : ℕ) [NeZero m] (i : Fin (m+1)) : I :=
  ⟨(i : ℝ)/(m : ℝ), by
    have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
    constructor
    · positivity
    · apply (div_le_one hm).mpr
      exact_mod_cast (Nat.le_of_lt_succ i.isLt)⟩

noncomputable def cell (m : ℕ) [NeZero m] (i : Fin m) : Set I :=
  if i.val+1=m then Icc (boundary m i.castSucc) (boundary m i.succ)
  else Ico (boundary m i.castSucc) (boundary m i.succ)

lemma mem_some_cell (m : ℕ) [NeZero m] (t : I) : ∃ i : Fin m, t ∈ cell m i := by
  have hm : 0 < m := NeZero.pos m
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  by_cases ht : (t : ℝ)=1
  · let i : Fin m := ⟨m-1, by omega⟩
    refine ⟨i, ?_⟩
    have hi : i.val+1=m := by dsimp [i]; omega
    rw [cell,ite_eq_left hi]
    constructor
    · change (i : ℝ)/(m : ℝ) ≤ (t : ℝ)
      rw [ht]
      apply (div_le_one hm').mpr
      exact_mod_cast i.isLt.le
    · change (t : ℝ) ≤ ((i.val+1 : ℕ) : ℝ)/(m : ℝ)
      rw [Nat.cast_add,Nat.cast_one,ht]
      have he : (i : ℝ)+1=(m : ℝ) := by exact_mod_cast hi
      rw [he,div_self hm'.ne']
  · have ht' : (t : ℝ)<1 := lt_of_le_of_ne t.property.2 ht
    have hx : 0 ≤ (m : ℝ)*(t : ℝ) := mul_nonneg hm'.le t.property.1
    have hi : ⌊(m : ℝ)*(t : ℝ)⌋₊ < m := by
      apply (Nat.floor_lt hx).mpr
      nlinarith
    let i : Fin m := ⟨⌊(m : ℝ)*(t : ℝ)⌋₊, hi⟩
    have hlo : (i : ℝ)/(m : ℝ) ≤ (t : ℝ) := by
      apply (div_le_iff₀ hm').mpr
      simpa [i,mul_comm] using Nat.floor_le hx
    have hup : (t : ℝ) < ((i : ℝ)+1)/(m : ℝ) := by
      apply (lt_div_iff₀ hm').mpr
      simpa [i,mul_comm] using Nat.lt_floor_add_one ((m : ℝ)*(t : ℝ))
    refine ⟨i, ?_⟩
    unfold cell
    split_ifs
    · refine ⟨hlo, ?_⟩
      change (t : ℝ) ≤ ((i.val+1 : ℕ) : ℝ)/(m : ℝ)
      simpa only [Nat.cast_add,Nat.cast_one] using hup.le
    · refine ⟨hlo, ?_⟩
      change (t : ℝ) < ((i.val+1 : ℕ) : ℝ)/(m : ℝ)
      simpa only [Nat.cast_add,Nat.cast_one] using hup

end PlanarHalving.UniformPartition

namespace PlanarHalving.UniformPartition
open MeasureTheory Set Filter
open scoped unitInterval Topology

noncomputable def index (m : ℕ) [NeZero m] (t : I) : Fin m :=
  (mem_some_cell m t).choose

noncomputable def grid (m : ℕ) [NeZero m] (t : I) : I := boundary m (index m t).castSucc

end PlanarHalving.UniformPartition

namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology unitInterval NNReal ENNReal

noncomputable def weightedAtoms {X : Type*} [MeasurableSpace X] {α : Type*} [Fintype α]
    (w : ℝ≥0) (x : α → X) : FiniteMeasure X :=
  ⟨w • (∑ i, Measure.dirac (x i) : Measure X), inferInstance⟩

end PlanarHalving.Limits

namespace PlanarHalving.UniformPartition
open MeasureTheory Set Filter PlanarHalving.Limits
open scoped Topology unitInterval NNReal ENNReal

noncomputable def gridPoint (m : ℕ) [NeZero m] (i : Fin m × Fin m) : I × I :=
  (boundary m i.1.castSucc,boundary m i.2.castSucc)

end PlanarHalving.UniformPartition

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Windows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.TimeWindows
open Set
open scoped unitInterval Classical

abbrev Window := Σ d : ℕ, Fin (2^d)

noncomputable def carrier (J : Window) : Set I := UniformPartition.cell (2^J.1) J.2

noncomputable def time (R : ℕ) [NeZero R] (b : Fin R) : I :=
  ⟨((b : ℝ)+1/2)/(R : ℝ),by
    have hR : (0 : ℝ)<R := Nat.cast_pos.mpr (NeZero.pos R)
    constructor
    · positivity
    · apply (div_le_one hR).mpr
      have hb : (b : ℝ)+1 ≤ R := by exact_mod_cast b.isLt
      linarith⟩

noncomputable def cut {α : Type*} [LinearOrder α] {R : ℕ} (t : Fin R → α) (x : α) : ℕ :=
  (Finset.univ.filter fun b => t b<x).card

lemma cut_le {α : Type*} [LinearOrder α] {R : ℕ} (t : Fin R → α) (x : α) : cut t x ≤ R := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)

lemma cut_mono {α : Type*} [LinearOrder α] {R : ℕ} (t : Fin R → α) : Monotone (cut t) := by
  intro x y hxy
  apply Finset.card_le_card
  intro b hb
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter.mp hb).2).trans_le hxy⟩

noncomputable def start (R : ℕ) [NeZero R] (J : Window) : ℕ :=
  cut (time R) (UniformPartition.boundary (2^J.1) J.2.castSucc)
noncomputable def stop (R : ℕ) [NeZero R] (J : Window) : ℕ :=
  cut (time R) (UniformPartition.boundary (2^J.1) J.2.succ)

lemma start_le_stop (R : ℕ) [NeZero R] (J : Window) : start R J ≤ stop R J := by
  apply cut_mono
  change (J.2 : ℝ)/(2^J.1 : ℕ) ≤ ((J.2.val+1 : ℕ) : ℝ)/(2^J.1 : ℕ)
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Nat.le_succ J.2.val
  · positivity

lemma stop_le (R : ℕ) [NeZero R] (J : Window) : stop R J ≤ R := cut_le _ _

noncomputable def length (R : ℕ) [NeZero R] (J : Window) : ℕ := stop R J-start R J
lemma start_add_length (R : ℕ) [NeZero R] (J : Window) : start R J+length R J=stop R J :=
  Nat.add_sub_of_le (start_le_stop R J)

end PlanarHalving.TimeWindows

namespace PlanarHalving.Batches
open MeasureTheory Set Limits
open scoped NNReal ENNReal Classical
variable {n R k a : ℕ} {P : Fin n → Point}

noncomputable def System.vertexMeasure (S : @System n R k a P)
    {X : Type*} [MeasurableSpace X] (z : Fin n → X) : FiniteMeasure X :=
  weightedAtoms (n : ℝ≥0)⁻¹ (fun v : ↥S.vertices => z v.val)

noncomputable def System.endpointMeasure (S : @System n R k a P)
    {X : Type*} [MeasurableSpace X] (z : Fin n → X) (E : ℝ≥0) : FiniteMeasure X :=
  weightedAtoms E⁻¹ (fun e : ↥S.edges => z e.val.1)

end PlanarHalving.Batches

namespace PlanarHalving.Batches
open Set TimeWindows
open scoped unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

noncomputable def System.timeWindow (S : @System n R k a P) [NeZero R] (J : Window) :
    @System n (length R J) k a P :=
  S.window (start R J) (length R J) (by rw [start_add_length]; exact stop_le R J)

noncomputable def System.edgeTime (S : @System n R k a P) [NeZero R] [NeZero a] (e : ↥S.edges) : I :=
  time R (S.trace e.property).batch

end PlanarHalving.Batches

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Directions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Directions
open MeasureTheory Set

abbrev Plane := ℝ × ℝ

def simplex (x : ℝ) : Plane := (x,1-x)

def allowed {ι : Type*} (Q : Plane ≃L[ℝ] Plane) (g : ι → Plane →L[ℝ] ℝ)
    (lo hi : ι → ℝ) (t : ℝ) : Set ℝ :=
  {x | x∈Icc 0 1 ∧ ∀ i, (hi i<t → 0≤g i (Q (simplex x))) ∧
    (t<lo i → g i (Q (simplex x))≤0)}

end PlanarHalving.Directions

namespace PlanarHalving.TimeWindows
open MeasureTheory Set Filter UniformPartition Limits
open scoped Topology unitInterval NNReal

noncomputable def midpointGrid (m : ℕ) [NeZero m] (t : I) : I := time m (index m t)

end PlanarHalving.TimeWindows

namespace PlanarHalving.Batches
open MeasureTheory Set Filter Limits TimeWindows
open scoped Topology NNReal ENNReal unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

noncomputable def System.labelTimeMeasure (S : @System n R k a P) [NeZero R] [NeZero a]
    {X : Type*} [MeasurableSpace X] (z : Fin n → X) : FiniteMeasure (X×I) :=
  weightedAtoms ((R : ℝ≥0)*(a : ℝ≥0)^2)⁻¹ (fun e : ↥S.edges => (z e.val.1,S.edgeTime e))

end PlanarHalving.Batches

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Labels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankCoordinates
open Set
open scoped unitInterval

structure Family (m : ℕ) where
  graph : Fin m → ℝ → ℝ
  continuous : ∀ j, Continuous (graph j)
  convex : ∀ j, ConvexOn ℝ univ (graph j)
  scale : ℝ
  scale_pos : 0 < scale

noncomputable def Family.value {m : ℕ} [NeZero m] (F : Family m) (p : Point) : I :=
  ⟨smoothed F.graph F.scale p, (smoothed_mem (NeZero.pos m) F.graph F.scale p).1.le,
    (smoothed_mem (NeZero.pos m) F.graph F.scale p).2.le⟩

noncomputable def Family.flat (m : ℕ) : Family m where
  graph := fun _ _ => 0
  continuous := fun _ => continuous_const
  convex := fun _ => convexOn_const _ (convex_univ)
  scale := 1
  scale_pos := zero_lt_one

end PlanarHalving.RankCoordinates
namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates TimeWindows
open scoped unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

noncomputable def System.rankFamily (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) (J : Window) : Family (a*n) := by
  classical
  by_cases hJ : 0 < length R J
  · let h := S.window_coordinate hP (start R J) (length R J)
      (by rw [start_add_length]; exact stop_le R J) hJ
    let G := h.choose
    exact ⟨G.graph,G.continuous,G.convex,h.choose_spec.choose,h.choose_spec.choose_spec.1⟩
  · exact Family.flat _

lemma System.rankFamily_spec (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) (J : Window) (hJ : 0 < length R J) :
    ∃ G : (S.timeWindow J).FullGraphs (S.drawing.exteriorCrossings (S.timeWindow J).edges),
      (S.rankFamily hP J).graph=G.graph ∧
      ∀ z ∈ S.drawing.exteriorCrossings (S.timeWindow J).edges,
        |(S.rankFamily hP J).value z-(slot G.graph z : ℝ)/(a*n)| ≤ 2/(a*n) := by
  classical
  unfold System.rankFamily
  rw [dite_eq_left hJ]
  exact ⟨_,rfl,(S.window_coordinate hP _ _ _ hJ).choose_spec.choose_spec.2⟩

abbrev Labels := Window → I

noncomputable instance labelsMetric : MetricSpace Labels := PiCountable.metricSpace

noncomputable def System.labels (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) (p : Point) : Labels := fun J => (S.rankFamily hP J).value p

end PlanarHalving.Batches
namespace PlanarHalving.TimeWindows
open Set
open scoped unitInterval

def Before (A B : Window) : Prop :=
  UniformPartition.boundary (2^A.1) A.2.succ ≤ UniformPartition.boundary (2^B.1) B.2.castSucc

lemma stop_le_start (R : ℕ) [NeZero R] {A B : Window} (hAB : Before A B) :
    stop R A ≤ start R B := cut_mono _ hAB

end PlanarHalving.TimeWindows
namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates TimeWindows MeasureTheory Limits
open scoped unitInterval NNReal ENNReal
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.timeWindow_graph_gap (S : @System n R k a P) [NeZero R] [NeZero n] [NeZero a]
    {A B : Window} (hAB : Before A B) {F H : Finset Point}
    (G : (S.timeWindow A).FullGraphs F) (G' : (S.timeWindow B).FullGraphs H) :
    G.upper < G'.lower := by
  apply G.upper_lt.trans_le
  apply le_trans _ G'.lower_lt.le
  change S.slope ⟨start R A+length R A, _⟩ ≤ S.slope ⟨start R B+0,_⟩
  apply S.increasing.monotone
  change start R A+length R A ≤ start R B+0
  rw [start_add_length,Nat.add_zero]
  exact stop_le_start R hAB

noncomputable def System.windowCrossings (S : @System n R k a P) [NeZero R] (A B : Window) :
    Finset ((Fin n × Fin n) × (Fin n × Fin n)) := by
  classical
  exact S.drawing.crossings.filter (fun w =>
    (w.1 ∈ (S.timeWindow A).edges ∧ w.2 ∈ (S.timeWindow B).edges) ∨
    (w.2 ∈ (S.timeWindow A).edges ∧ w.1 ∈ (S.timeWindow B).edges))

lemma System.windowCrossings_sub (S : @System n R k a P) [NeZero R] (A B : Window) :
    S.windowCrossings A B ⊆ S.drawing.crossings := Finset.filter_subset ..

noncomputable def System.windowCrossPoint (S : @System n R k a P) [NeZero R] (A B : Window)
    (w : ↥(S.windowCrossings A B)) : Point :=
  S.drawing.crossingPoint ⟨w.val,S.windowCrossings_sub A B w.property⟩

end PlanarHalving.Batches
namespace PlanarHalving.Batches
open MeasureTheory Set Limits TimeWindows PlaneGraph
open scoped NNReal ENNReal unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

noncomputable def System.windowCrossMeasure (S : @System n R k a P) [NeZero R]
    (A B : Window) {X : Type*} [MeasurableSpace X] (z : Point → X) : FiniteMeasure X :=
  weightedAtoms (((a*n : ℕ) : ℝ≥0)^2)⁻¹ (fun w => z (S.windowCrossPoint A B w))

end PlanarHalving.Batches
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

structure Configuration where
  n : ℕ
  R : ℕ
  k : ℕ
  a : ℕ
  n_pos : 0 < n
  R_pos : 0 < R
  a_pos : 0 < a
  point : Fin n → Point
  generic : Generic point
  system : @System n R k a point

instance instNeZeroNatN (F : Configuration) : NeZero F.n := ⟨ne_of_gt F.n_pos⟩
instance instNeZeroNatR (F : Configuration) : NeZero F.R := ⟨ne_of_gt F.R_pos⟩
instance instNeZeroNatA (F : Configuration) : NeZero F.a := ⟨ne_of_gt F.a_pos⟩

noncomputable def Configuration.label (F : Configuration) : Point → Labels := F.system.labels F.generic

noncomputable def Configuration.points (F : Configuration) : FiniteMeasure Labels :=
  weightedAtoms (F.n : ℝ≥0)⁻¹ (F.label ∘ F.point)
noncomputable def Configuration.vertices (F : Configuration) (J : Window) : FiniteMeasure Labels :=
  (F.system.timeWindow J).vertexMeasure (F.label ∘ F.point)
noncomputable def Configuration.edgeTime (F : Configuration) : FiniteMeasure (Labels×I) :=
  F.system.labelTimeMeasure (F.label ∘ F.point)
noncomputable def Configuration.crossings (F : Configuration) (A B : Window) : FiniteMeasure Labels :=
  F.system.windowCrossMeasure A B F.label
noncomputable def Configuration.timeRestrict (F : Configuration) (J : Window) : FiniteMeasure (Labels×I) :=
  ⟨(F.edgeTime : Measure (Labels×I)).restrict (Prod.snd ⁻¹' carrier J),inferInstance⟩

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.RankMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

inductive MeasureIndex where
  | point
  | vertices (J : Window)
  | time
  | restrict (J : Window)
  | cross (A B : Window)
  deriving Countable

abbrev LimitSpace : MeasureIndex → Type
  | .point => Labels
  | .vertices _ => Labels
  | .time => Labels × I
  | .restrict _ => Labels × I
  | .cross _ _ => Labels

noncomputable instance instMetricSpaceLimitSpace (i : MeasureIndex) : MetricSpace (LimitSpace i) := by
  cases i <;> dsimp only [LimitSpace] <;> exact inferInstanceAs (MetricSpace _)
instance instCompactSpaceLimitSpace (i : MeasureIndex) : CompactSpace (LimitSpace i) := by
  cases i <;> dsimp only [LimitSpace] <;> exact inferInstanceAs (CompactSpace _)
instance instNonemptyLimitSpace (i : MeasureIndex) : Nonempty (LimitSpace i) := by
  cases i <;> dsimp only [LimitSpace] <;> exact inferInstanceAs (Nonempty _)
noncomputable instance instMeasurableSpaceLimitSpace (i : MeasureIndex) : MeasurableSpace (LimitSpace i) := by
  cases i <;> dsimp only [LimitSpace] <;> exact inferInstanceAs (MeasurableSpace _)
instance instBorelSpaceLimitSpace (i : MeasureIndex) : BorelSpace (LimitSpace i) := by
  cases i <;> dsimp only [LimitSpace] <;> exact inferInstanceAs (BorelSpace _)

noncomputable def Configuration.measures (F : Configuration) : ∀ i, FiniteMeasure (LimitSpace i)
  | .point => F.points
  | .vertices J => F.vertices J
  | .time => F.edgeTime
  | .restrict J => F.timeRestrict J
  | .cross A B => F.crossings A B

structure Data where
  points : FiniteMeasure Labels
  vertices : Window → FiniteMeasure Labels
  edgeTime : FiniteMeasure (Labels × I)
  timeRestrict : Window → FiniteMeasure (Labels × I)
  crossings : Window → Window → FiniteMeasure Labels

noncomputable def Data.ofFamily (f : ∀ i, FiniteMeasure (LimitSpace i)) : Data where
  points := f .point
  vertices := fun J => f (.vertices J)
  edgeTime := f .time
  timeRestrict := fun J => f (.restrict J)
  crossings := fun A B => f (.cross A B)

structure Converges (F : ℕ → Configuration) (L : Data) : Prop where
  points : Tendsto (fun n => (F n).points) atTop (𝓝 L.points)
  vertices : ∀ J, Tendsto (fun n => (F n).vertices J) atTop (𝓝 (L.vertices J))
  edgeTime : Tendsto (fun n => (F n).edgeTime) atTop (𝓝 L.edgeTime)
  timeRestrict : ∀ J, Tendsto (fun n => (F n).timeRestrict J) atTop (𝓝 (L.timeRestrict J))
  crossings : ∀ A B, Tendsto (fun n => (F n).crossings A B) atTop (𝓝 (L.crossings A B))

end PlanarHalving.RankLimits
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

noncomputable def Data.edge (L : Data) : FiniteMeasure Labels := L.edgeTime.map Prod.fst
noncomputable def Data.edgeWindow (L : Data) (J : Window) : FiniteMeasure Labels :=
  (L.timeRestrict J).map Prod.fst

end PlanarHalving.RankLimits
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

noncomputable def Configuration.edgeWindow (F : Configuration) (J : Window) : FiniteMeasure Labels :=
  (F.timeRestrict J).map Prod.fst

end PlanarHalving.RankLimits
namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates TimeWindows
open scoped unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

noncomputable def System.rankGraphs (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) (J : Window) (hJ : 0 < length R J) :
    (S.timeWindow J).FullGraphs (S.drawing.exteriorCrossings (S.timeWindow J).edges) :=
  (S.rankFamily_spec hP J hJ).choose

noncomputable def System.rankCoordinate (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) (J : Window) (hJ : 0 < length R J) :
    Coordinate (S.rankGraphs hP J hJ).lower (S.rankGraphs hP J hJ).upper :=
  smoothedCoordinate (Nat.mul_pos (NeZero.pos a) (NeZero.pos n))
    (S.rankGraphs hP J hJ).graph (S.rankFamily hP J).scale_pos
    (S.rankGraphs hP J hJ).continuous (S.rankGraphs hP J hJ).slopes

noncomputable def System.rankHomeomorph (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) {A B : Window} (hAB : Before A B)
    (hA : 0 < length R A) (hB : 0 < length R B) : Point ≃ₜ (UnitOpen × UnitOpen) :=
  pairHomeomorph (S.rankCoordinate hP A hA) (S.rankCoordinate hP B hB)
    (S.timeWindow_graph_gap hAB _ _)

noncomputable def System.rankInCoordinates (S : @System n R k a P)
    [NeZero n] [NeZero a] [NeZero R] (hP : Generic P) {A B : Window} (hAB : Before A B)
    (hA : 0 < length R A) (hB : 0 < length R B) (C : Window) : UnitOpen × UnitOpen → ℝ :=
  fun p => (S.labels hP ((S.rankHomeomorph hP hAB hA hB).symm p) C : ℝ)

end PlanarHalving.Batches

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Sweep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Sweep
open Set

noncomputable def setDistance {n : ℕ} (M N : Finset (Fin n)) : ℕ := (M\N).card

lemma setDistance_self {n : ℕ} (M : Finset (Fin n)) : setDistance M M=0 := by
  simp [setDistance]

lemma setDistance_comm {n : ℕ} {M N : Finset (Fin n)} (hc : M.card=N.card) :
    setDistance M N=setDistance N M := Finset.card_sdiff_comm hc

lemma setDistance_triangle {n : ℕ} (M N K : Finset (Fin n)) :
    setDistance M K ≤ setDistance M N+setDistance N K := by
  classical
  apply (Finset.card_le_card (show M\K ⊆ (M\N)∪(N\K) from ?_)).trans
    (Finset.card_union_le _ _)
  intro x hx
  by_cases hxN : x∈N
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxN,(Finset.mem_sdiff.mp hx).2⟩)
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,hxN⟩)

structure States {n T k : ℕ} (P : Fin n → Point) where
  slope : Fin (T+1) → ℝ
  increasing : StrictMono slope
  marks : Fin (T+1) → Finset (Fin n)
  card_marks : ∀ i, (marks i).card=k
  separates : ∀ i, Separates P (slope i) (marks i)
  step : ∀ i : Fin T, setDistance (marks i.castSucc) (marks i.succ) ≤ 1

variable {n T k a : ℕ} {P : Fin n → Point}

noncomputable def States.distance (S : @States n T k P) (s t : Fin (T+1)) : ℕ :=
  setDistance (S.marks s) (S.marks t)

lemma States.distance_self (S : @States n T k P) (s : Fin (T+1)) : S.distance s s=0 :=
  setDistance_self _

lemma States.distance_comm (S : @States n T k P) (s t : Fin (T+1)) : S.distance s t=S.distance t s :=
  setDistance_comm (by rw [S.card_marks,S.card_marks])

lemma States.distance_triangle (S : @States n T k P) (s t u : Fin (T+1)) :
    S.distance s u ≤ S.distance s t+S.distance t u := setDistance_triangle _ _ _

noncomputable def States.eligible (S : @States n T k P) (s : Fin (T+1)) (a : ℕ) : Finset (Fin (T+1)) :=
  Finset.univ.filter (fun t => s<t ∧ a ≤ S.distance s t)

noncomputable def States.next (S : @States n T k P) (s : Fin (T+1)) (a : ℕ)
    (h : (S.eligible s a).Nonempty) : Fin (T+1) := (S.eligible s a).min' h

lemma States.next_spec (S : @States n T k P) (s : Fin (T+1)) (a : ℕ)
    (h : (S.eligible s a).Nonempty) : s<S.next s a h ∧ a≤S.distance s (S.next s a h) := by
  exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2

lemma States.before_next (S : @States n T k P) (s : Fin (T+1)) {a : ℕ} (ha : 0<a)
    (h : (S.eligible s a).Nonempty) {t : Fin (T+1)} (hst : s≤t) (ht : t<S.next s a h) :
    S.distance s t<a := by
  by_cases he : t=s
  · subst t; simpa only [S.distance_self] using ha
  by_contra hh
  have hmem : t∈S.eligible s a := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,lt_of_le_of_ne hst (Ne.symm he),le_of_not_gt hh⟩
  exact not_le_of_gt ht (Finset.min'_le _ _ hmem)

lemma States.next_distance (S : @States n T k P) (s : Fin (T+1)) {a : ℕ} (ha : 0<a)
    (h : (S.eligible s a).Nonempty) : S.distance s (S.next s a h)=a := by
  have hs := (S.next_spec s a h).1
  let b : Fin T := ⟨(S.next s a h).val-1,by have hn:=(S.next s a h).isLt; exact Nat.sub_lt_right_of_lt_add (by omega) (by omega)⟩
  have hb : b.succ=S.next s a h := by apply Fin.ext; dsimp [b]; omega
  have hb0 : s≤b.castSucc := by change s.val≤(S.next s a h).val-1; exact Nat.le_sub_one_of_lt hs
  have hb1 : b.castSucc<S.next s a h := by rw [← hb]; exact Fin.castSucc_lt_succ
  have hprev := S.before_next s ha h hb0 hb1
  have hjump := S.distance_triangle s b.castSucc b.succ
  have hstep := S.step b
  change S.distance b.castSucc b.succ≤1 at hstep
  rw [hb] at hjump hstep
  exact Nat.le_antisymm (by omega) (S.next_spec s a h).2

structure States.Greedy (S : @States n T k P) (s : Fin (T+1)) (a : ℕ) where
  count : ℕ
  index : Fin (count+1) → Fin (T+1)
  first : index 0=s
  increasing : StrictMono index
  distance : ∀ j : Fin count, S.distance (index j.castSucc) (index j.succ)=a
  hit : ∀ u v, s≤u → u≤v → 2*a-1≤S.distance u v →
    ∃ j : Fin count, u < index j.succ ∧ index j.succ ≤ v

lemma States.no_eligible_distance (S : @States n T k P) (s : Fin (T+1)) {a : ℕ} (ha : 0<a)
    (h : ¬(S.eligible s a).Nonempty) {t : Fin (T+1)} (hst : s≤t) : S.distance s t<a := by
  by_cases he : t=s
  · subst t; simpa only [S.distance_self] using ha
  by_contra hh
  exact h ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_le_of_ne hst (Ne.symm he),le_of_not_gt hh⟩⟩

lemma States.close_distance (S : @States n T k P) (s u v : Fin (T+1)) {a : ℕ}
    (ha : 0<a) (hu : S.distance s u<a) (hv : S.distance s v<a) : S.distance u v<2*a-1 := by
  have ht := S.distance_triangle u s v
  rw [S.distance_comm u s] at ht
  omega

noncomputable def States.greedy (S : @States n T k P) (s : Fin (T+1)) (a : ℕ) (ha : 0<a) :
    S.Greedy s a := by
  classical
  by_cases h : (S.eligible s a).Nonempty
  · let t := S.next s a h
    have ht : s<t := (S.next_spec s a h).1
    let Q := S.greedy t a ha
    refine ⟨Q.count+1,Fin.cons s Q.index,by simp,?_,?_,?_⟩
    · apply Fin.strictMono_cons.mpr
      refine ⟨?_,Q.increasing⟩
      intro j
      exact ht.trans_le (by simpa only [Q.first] using Q.increasing.monotone (Fin.zero_le j))
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa only [Fin.castSucc_zero,Fin.cons_zero,Fin.cons_succ,Q.first] using S.next_distance s ha h
      · simpa only [Fin.castSucc_succ,Fin.cons_succ] using Q.distance j
    · intro u v hsu huv hd
      by_cases htu : t≤u
      · obtain ⟨j,hj⟩ := Q.hit u v htu huv hd
        refine ⟨j.succ,?_⟩
        simpa only [Fin.cons_succ] using hj
      · have hut : u<t := lt_of_not_ge htu
        by_cases htv : t≤v
        · refine ⟨0,?_⟩
          simpa only [Fin.cons_succ,Q.first] using And.intro hut htv
        · have hv := S.before_next s ha h (hsu.trans huv) (lt_of_not_ge htv)
          have hu := S.before_next s ha h hsu hut
          exact False.elim (not_lt_of_ge hd (S.close_distance s u v ha hu hv))
  · refine ⟨0,fun _ => s,rfl,?_,?_,?_⟩
    · intro i j hij
      exact False.elim (by have hi:=i.isLt; have hj:=j.isLt; change i.val<j.val at hij; omega)
    · intro j; exact Fin.elim0 j
    · intro u v hsu huv hd
      exact False.elim (not_lt_of_ge hd (S.close_distance s u v ha
        (S.no_eligible_distance s ha h hsu) (S.no_eligible_distance s ha h (hsu.trans huv))))
termination_by T-s.val
decreasing_by
  have ht := (S.next_spec s a h).1
  change s.val<(S.next s a h).val at ht
  omega

noncomputable def States.greedySystem (S : @States n T k P) (a : ℕ) (ha : 0<a) :
    @Batches.System n (S.greedy 0 a ha).count k a P where
  slope := fun j => S.slope ((S.greedy 0 a ha).index j)
  increasing := S.increasing.comp (S.greedy 0 a ha).increasing
  marks := fun j => S.marks ((S.greedy 0 a ha).index j)
  card_marks := fun _j => S.card_marks _
  separates := fun _j => S.separates _
  distance := (S.greedy 0 a ha).distance

end PlanarHalving.Sweep
namespace PlanarHalving.Sweep
open Set

lemma slope_symm (p q : Point) : slope p q=slope q p := by
  unfold slope
  rw [← neg_sub q.2 p.2,← neg_sub q.1 p.1,neg_div_neg_eq]

noncomputable def criticalSlopes {n : ℕ} (P : Fin n → Point) : Finset ℝ :=
  (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1≠ij.2)).image
    (fun ij => slope (P ij.1) (P ij.2))

lemma mem_criticalSlopes {n : ℕ} (P : Fin n → Point) {i j : Fin n} (hij : i≠j) :
    slope (P i) (P j)∈criticalSlopes P := by
  classical
  exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩,rfl⟩

lemma projection_injective {n : ℕ} {P : Fin n → Point} (hx : Function.Injective (fun i => (P i).1))
    {s : ℝ} (hs : s∉criticalSlopes P) : Function.Injective (fun i => projection s (P i)) := by
  intro i j hij
  by_contra hn
  apply hs
  have hd : (P j).1-(P i).1≠0 := sub_ne_zero.mpr (fun h => hn (hx h.symm))
  have he : s=slope (P i) (P j) := by
    apply (eq_div_iff hd).mpr
    unfold projection at hij
    linarith
  rw [he]
  exact mem_criticalSlopes P hn

structure Traversal (C : Finset ℝ) where
  size : ℕ
  cut : Fin (size+2) → ℝ
  increasing : StrictMono cut
  critical : ∀ c, c∈C ↔ ∃ j : Fin size, cut j.succ.castSucc=c

lemma strictMono_snoc {m : ℕ} {f : Fin m → ℝ} {b : ℝ}
    (hf : StrictMono f) (hb : ∀ j, f j < b) : StrictMono (Fin.snoc f b) := by
  intro i j hij
  revert hij
  refine Fin.lastCases ?_ (fun j => ?_) j
  · intro hij
    have hi : i≠Fin.last m := ne_of_lt hij
    obtain ⟨i,rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    simpa only [Fin.snoc_castSucc,Fin.snoc_last] using hb i
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · intro hij
      exact False.elim (not_lt_of_ge (Fin.le_last _) hij)
    · intro hij
      simpa only [Fin.snoc_castSucc] using hf (Fin.castSucc_lt_castSucc_iff.mp hij)

noncomputable def traversal (C : Finset ℝ) : Traversal C := by
  classical
  let m := C.card
  let e := C.orderIsoOfFin rfl
  let lo := Classical.choose (C.finite_toSet.bddBelow.exists_le 0)
  have hlo := (Classical.choose_spec (C.finite_toSet.bddBelow.exists_le 0)).2
  let hi := Classical.choose (C.finite_toSet.bddAbove.exists_ge 0)
  have hhi := (Classical.choose_spec (C.finite_toSet.bddAbove.exists_ge 0)).2
  let upper := max lo hi
  have hup : ∀ c∈C, c≤upper := fun _ hc => (hhi _ hc).trans (le_max_right _ _)
  let f : Fin m → ℝ := fun j => (e j : ℝ)
  have hf : StrictMono f := fun i j hij => e.strictMono hij
  refine ⟨m,Fin.cons (lo-1) (Fin.snoc f (upper+1)),?_,?_⟩
  · apply Fin.strictMono_cons.mpr
    refine ⟨?_,strictMono_snoc hf ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.snoc_last]
        have hle : lo≤upper := le_max_left _ _
        linarith
      · simpa only [Fin.snoc_castSucc] using lt_of_lt_of_le (sub_lt_self lo (by norm_num : (0:ℝ) < 1)) (hlo _ (e i).property)
    · intro i
      exact lt_of_le_of_lt (hup _ (e i).property) (lt_add_one upper)
  · intro c
    constructor
    · intro hc
      refine ⟨e.symm ⟨c,hc⟩,?_⟩
      simpa only [Fin.castSucc_succ,Fin.cons_succ,Fin.snoc_castSucc,f] using
        congrArg Subtype.val (e.apply_symm_apply ⟨c,hc⟩)
    · rintro ⟨j,rfl⟩
      simpa only [Fin.castSucc_succ,Fin.cons_succ,Fin.snoc_castSucc,f] using (e j).property

variable {C : Finset ℝ}

noncomputable def Traversal.sample (T : Traversal C) (i : Fin (T.size+1)) : ℝ :=
  (T.cut i.castSucc+T.cut i.succ)/2

lemma Traversal.sample_bounds (T : Traversal C) (i : Fin (T.size+1)) :
    T.cut i.castSucc < T.sample i ∧ T.sample i < T.cut i.succ := by
  have h := T.increasing (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
  dsimp [Traversal.sample]
  constructor  <;> linarith

lemma Traversal.sample_increasing (T : Traversal C) : StrictMono T.sample := by
  intro i j hij
  have hc : i.succ≤j.castSucc := by change i.val+1≤j.val; exact Nat.succ_le_of_lt hij
  exact (T.sample_bounds i).2.trans_le (T.increasing.monotone hc) |>.trans (T.sample_bounds j).1

lemma Traversal.sample_not_mem (T : Traversal C) (i : Fin (T.size+1)) : T.sample i∉C := by
  intro h
  obtain ⟨j,hj⟩ := (T.critical _).mp h
  have hl := (T.sample_bounds i).1
  have hu := (T.sample_bounds i).2
  rw [← hj] at hl hu
  have hl' := T.increasing.lt_iff_lt.mp hl
  have hu' := T.increasing.lt_iff_lt.mp hu
  change i.val < j.val+1 at hl'
  change j.val+1 < i.val+1 at hu'
  omega

lemma Traversal.unique_critical (T : Traversal C) (i : Fin T.size) {c : ℝ} (hc : c∈C)
    (hl : T.sample i.castSucc < c) (hu : c < T.sample i.succ) : c=T.cut i.succ.castSucc := by
  obtain ⟨j,hj⟩ := (T.critical _).mp hc
  have hl' := (T.sample_bounds i.castSucc).1.trans hl
  have hu' := hu.trans (T.sample_bounds i.succ).2
  rw [← hj] at hl' hu'
  have hl'' := T.increasing.lt_iff_lt.mp hl'
  have hu'' := T.increasing.lt_iff_lt.mp hu'
  have he : j=i := by
    apply Fin.ext
    change i.val < j.val+1 at hl''
    change j.val+1 < i.val+1+1 at hu''
    omega
  simpa only [he] using hj.symm

lemma separates_step_distance {n k : ℕ} {P : Fin n → Point} (hP : Generic P)
    {s t : ℝ} (hst : s≤t) {M N : Finset (Fin n)} (hM : M.card=k) (hN : N.card=k)
    (hs : Separates P s M) (ht : Separates P t N)
    (hone : ∀ c∈criticalSlopes P, ∀ d∈criticalSlopes P,
      s < c → c < t → s < d → d < t → c=d) : setDistance M N≤1 := by
  classical
  rw [setDistance,Finset.card_le_one]
  intro i hi u hu
  have hne : (N\M).Nonempty := by
    have he := Finset.card_sdiff_comm (hM.trans hN.symm)
    have hp := Finset.card_pos.mpr (⟨i,hi⟩ : (M\N).Nonempty)
    rw [he] at hp
    exact Finset.card_pos.mp hp
  obtain ⟨j,hj⟩ := hne
  have hiJ : i≠j := by intro he; subst j; exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_sdiff.mp hi).1
  have huJ : u≠j := by intro he; subst j; exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_sdiff.mp hu).1
  have hsi := exchange_slope_between hst hs ht hi hj
  have hsu := exchange_slope_between hst hs ht hu hj
  have he := hone _ (mem_criticalSlopes P hiJ) _ (mem_criticalSlopes P huJ) hsi.1 hsi.2 hsu.1 hsu.2
  rw [slope_symm (P i) (P j),slope_symm (P u) (P j)] at he
  exact PlaneGraph.slope_eq_implies_eq_ne hP.1
    (hP.2.1 j i hiJ.symm) (hP.2.1 j u huJ.symm) he

noncomputable def states {n k : ℕ} (P : Fin n → Point) (hP : Generic P) (hk : k≤n) :
    @States n (traversal (criticalSlopes P)).size k P := by
  let T := traversal (criticalSlopes P)
  have hex (i : Fin (T.size+1)) := exists_state P (T.sample i) hk
    (projection_injective (PlaneGraph.Generic.x_injective hP) (T.sample_not_mem i))
  choose M hM hsep using hex
  refine ⟨T.sample,T.sample_increasing,M,hM,hsep,?_⟩
  intro i
  apply separates_step_distance hP (T.sample_increasing.monotone (Fin.castSucc_le_succ i)) (hM _) (hM _) (hsep _) (hsep _)
  intro c hc d hd hcs hct hds hdt
  exact (T.unique_critical i hc hcs hct).trans (T.unique_critical i hd hds hdt).symm

end PlanarHalving.Sweep
namespace PlanarHalving.Sweep
open Set
variable {n T k : ℕ} {P : Fin n → Point}

def StepDisjoint (C : Finset (Fin (T+1) × Fin (T+1))) : Prop :=
  ∀ p∈C, ∀ q∈C, p≠q → Disjoint (Ioc p.1 p.2) (Ioc q.1 q.2)

end PlanarHalving.Sweep
namespace PlanarHalving.Sweep
open Set
variable {n T k : ℕ} {P : Fin n → Point}

noncomputable def States.intervalActivity (S : @States n T k P)
    (u v : Fin (T+1)) (h : u≤v) : Finset (Fin n) :=
  activity (fun i : ↥(Finset.Icc u v) => S.marks i) ⟨u,Finset.mem_Icc.mpr ⟨le_rfl,h⟩⟩

lemma States.mem_intervalActivity (S : @States n T k P)
    {u v : Fin (T+1)} (h : u≤v) {x : Fin n} : x∈S.intervalActivity u v h ↔
    ∃ i, u ≤ i ∧ i ≤ v ∧ ((x∈S.marks i ∧ x∉S.marks u) ∨ (x∉S.marks i ∧ x∈S.marks u)) := by
  classical
  rw [States.intervalActivity,mem_activity]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i,(Finset.mem_Icc.mp i.property).1,(Finset.mem_Icc.mp i.property).2,hi⟩
  · rintro ⟨i,hu,hv,hi⟩
    exact ⟨⟨i,Finset.mem_Icc.mpr ⟨hu,hv⟩⟩,hi⟩

end PlanarHalving.Sweep

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.WindowMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval PiCountable

noncomputable def Data.conditional (L : Data) : Kernel Labels I :=
  (L.edgeTime : Measure (Labels×I)).condKernel
instance instIsMarkovKernelLabelsElemRealUnitIntervalConditional (L : Data) : IsMarkovKernel L.conditional := by
  unfold Data.conditional
  infer_instance

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Batches TimeWindows Sweep Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

structure Configuration.SweepEmbedding (F : Configuration) where
  rank_le : F.k≤F.n
  index : Fin (F.R+1) → Fin ((traversal (criticalSlopes F.point)).size+1)
  increasing : StrictMono index
  marks : ∀ j, F.system.marks j=(states F.point F.generic rank_le).marks (index j)

noncomputable def Configuration.SweepEmbedding.start {F : Configuration} (E : F.SweepEmbedding) (J : Window) :=
  E.index ⟨TimeWindows.start F.R J,lt_of_le_of_lt ((start_le_stop F.R J).trans (stop_le F.R J)) (Nat.lt_succ_self _)⟩
noncomputable def Configuration.SweepEmbedding.stop {F : Configuration} (E : F.SweepEmbedding) (J : Window) :=
  E.index ⟨TimeWindows.stop F.R J,lt_of_le_of_lt (stop_le F.R J) (Nat.lt_succ_self _)⟩

lemma Configuration.SweepEmbedding.start_le_stop {F : Configuration} (E : F.SweepEmbedding) (J : Window) :
    E.start J≤E.stop J := E.increasing.monotone (TimeWindows.start_le_stop F.R J)

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval PiCountable

noncomputable def timePartition (m : ℕ) : Finset Window :=
  Finset.univ.image (fun i : Fin (2^m) => (⟨m,i⟩ : Window))

end PlanarHalving.RankLimits
namespace PlanarHalving.PlaneGraph
open Set
variable {V : Type*} [Fintype V] {P : V → Point}

noncomputable def Drawing.pointOfPair (D : Drawing P) (w : (V×V)×(V×V)) : Point := by
  classical
  exact if h : w∈D.crossings then D.crossingPoint ⟨w,h⟩ else 0

end PlanarHalving.PlaneGraph
namespace PlanarHalving.Batches
open Set PlaneGraph TimeWindows MeasureTheory Limits
open scoped NNReal ENNReal unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

noncomputable def System.crossingsIn (S : @System n R k a P) [NeZero R]
    (A B : Window) {X : Type*} (z : Point → X) (U : Set X) := by
  classical
  exact (S.windowCrossings A B).filter (fun w => z (S.drawing.pointOfPair w)∈U)

end PlanarHalving.Batches

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.MeasureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

noncomputable def Configuration.longEdges (F : Configuration) (ρ : ℝ) : Finset (Fin F.n×Fin F.n) :=
  F.system.edges.filter (fun e => ENNReal.ofReal ρ ≤ Metric.ediam
    (F.label '' segment ℝ (F.point e.1) (F.point e.2)))

end PlanarHalving.RankLimits
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter PlaneGraph
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

noncomputable def Configuration.selectedEdges (F : Configuration) (W : Finset Window)
    (U : Set Labels) : Finset (Fin F.n×Fin F.n) := by
  classical
  exact W.biUnion (fun J => (F.system.timeWindow J).edges.filter (fun e : Fin F.n×Fin F.n => F.label (F.point e.1)∈U))

end PlanarHalving.RankLimits
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

noncomputable def localPartition (K : Window) (m : ℕ) : Finset Window :=
  (timePartition (K.1+m)).filter (fun J => carrier J⊆carrier K)

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Derivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

noncomputable def goodPartition (L : Data) (K : Window) (m : ℕ) : Finset Window :=
  (localPartition K (5*m)).filter (fun J => ((L.vertices J).mass : ℝ) ≤ 1/((2:ℝ)^m)^3)

end PlanarHalving.RankLimits
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

def CrossingPairs (K : Window) := {JH : Window×Window //
  carrier JH.1⊆carrier K ∧ carrier JH.2⊆carrier K ∧ Disjoint (carrier JH.1) (carrier JH.2)}

instance crossingPairsCountable (K : Window) : Countable (CrossingPairs K) := by
  unfold CrossingPairs
  infer_instance

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimit
open Filter Set MeasureTheory Metric
open scoped Topology unitInterval

noncomputable def extendRank {X : Type*} (p : X → Point) (c : X → I) (x : Point) : I :=
  ⨆ a : X, if p a ≤ x then c a else ⊥

end PlanarHalving.RankLimit

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows
open scoped Topology unitInterval

def signedPair (before : Bool) (p : Point) : Point :=
  if before then (p.1, -p.2) else (-p.1, p.2)

noncomputable def pairCoordinates (b : Bool) (A B : Window) (z : Labels) : Point :=
  signedPair b (z A, z B)

noncomputable def Configuration.extendedRank (F : Configuration) (b : Bool) (A B C : Window) :
    Point → I := RankLimit.extendRank (fun p => pairCoordinates b A B (F.system.labels F.generic p))
      (fun p => F.system.labels F.generic p C)

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Continuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.TimeWindows
open Set Filter MeasureTheory
open scoped unitInterval Topology

noncomputable def lower (J : Window) : I := UniformPartition.boundary (2^J.1) J.2.castSucc
noncomputable def upper (J : Window) : I := UniformPartition.boundary (2^J.1) J.2.succ

lemma lower_lt_upper (J : Window) : lower J < upper J := by
  change (J.2 : ℝ)/(2^J.1 : ℕ) < ((J.2.val+1 : ℕ) : ℝ)/(2^J.1 : ℕ)
  apply div_lt_div_of_pos_right _ (by positivity)
  simp

lemma closure_carrier (J : Window) : closure (carrier J) = Icc (lower J) (upper J) := by
  unfold carrier UniformPartition.cell
  split_ifs
  · exact isClosed_Icc.closure_eq
  · exact closure_Ico (lower_lt_upper J).ne

lemma endpoints_of_subset {J K : Window} (h : carrier J ⊆ carrier K) :
    lower K ≤ lower J ∧ upper J ≤ upper K := by
  have hh := closure_mono h
  rw [closure_carrier, closure_carrier] at hh
  exact ⟨(hh ⟨le_rfl,(lower_lt_upper J).le⟩).1,
    (hh ⟨(lower_lt_upper J).le,le_rfl⟩).2⟩

end PlanarHalving.TimeWindows

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Batches TimeWindows Limits
open scoped Topology unitInterval ENNReal

def SeparatedBefore (K H : Window) : Prop :=
  (0 : ℝ) < lower K ∧ upper K < lower H ∧ (upper H : ℝ) < 1

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Densities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Batches TimeWindows Limits
open scoped Topology unitInterval

def Subwindows (K : Window) := {J : Window // carrier J ⊆ carrier K}
instance instCountableSubwindows (K : Window) : Countable (Subwindows K) := by unfold Subwindows; infer_instance

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates
open scoped Topology unitInterval

noncomputable def reflectSecond : Point ≃L[ℝ] Point :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ)

@[simp] lemma reflectSecond_apply (p : Point) : reflectSecond p = (p.1,-p.2) := rfl

noncomputable def Configuration.rankChart (F : Configuration) {A B : Window}
    (hAB : Before A B) (hA : 0 < length F.R A) (hB : 0 < length F.R B) :
    OpenPartialHomeomorph Point Point :=
  let e := F.system.rankHomeomorph F.generic hAB hA hB
  let g : UnitOpen × UnitOpen → Point := Prod.map Subtype.val Subtype.val
  let hg : Topology.IsOpenEmbedding g :=
    isOpen_Ioo.isOpenEmbedding_subtypeVal.prodMap isOpen_Ioo.isOpenEmbedding_subtypeVal
  ((reflectSecond.toHomeomorph.isOpenEmbedding.comp hg).comp e.isOpenEmbedding).toOpenPartialHomeomorph _

noncomputable def Configuration.timeSlope (F : Configuration) (t : I) : ℝ :=
  F.system.slope ⟨cut (time F.R) t,Nat.lt_succ_of_le (cut_le _ _)⟩

end PlanarHalving.RankLimits
namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates
open scoped Topology unitInterval

noncomputable def reflectFirst : Point ≃L[ℝ] Point :=
  (ContinuousLinearEquiv.neg ℝ).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

@[simp] lemma reflectFirst_apply (p : Point) : reflectFirst p = (-p.1,p.2) := rfl

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.LocalZoom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Zoom
open Set

noncomputable def columnMap (u v : Point) : Point →L[ℝ] Point :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight u + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight v

@[simp] lemma columnMap_apply (u v x : Point) : columnMap u v x=x.1 • u+x.2 • v := rfl

noncomputable def columnEquiv (u v : Point) (h : detPair u v ≠ 0) : Point ≃L[ℝ] Point :=
  ContinuousLinearEquiv.ofBijective (columnMap u v)
    (LinearMap.ker_eq_bot.mpr (by
      intro x y hxy
      have he : (x.1-y.1) • u=(y.2-x.2) • v := by
        dsimp [columnMap] at hxy
        rw [sub_smul,sub_smul]
        linear_combination hxy
      have hz := parallel_scalars_zero u v h _ _ he
      exact Prod.ext (sub_eq_zero.mp hz.1) (sub_eq_zero.mp hz.2).symm))
    (LinearMap.range_eq_top.mpr (by
      intro x
      obtain ⟨a,b,hab⟩ := plane_span u v h x
      exact ⟨(a,b),hab.symm⟩))

@[simp] lemma columnEquiv_apply (u v : Point) (h : detPair u v ≠ 0) (x : Point) :
    columnEquiv u v h x=x.1 • u+x.2 • v := rfl

end PlanarHalving.Zoom

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

noncomputable def affineHomeomorph (p : Point) (q : ℝ) (hq : q≠0)
    (E : Point ≃L[ℝ] Point) : Point ≃ₜ Point where
  toFun x := p+q • E x
  invFun y := E.symm (q⁻¹ • (y-p))
  left_inv x := by simp only [add_sub_cancel_left,smul_smul,inv_mul_cancel₀ hq,one_smul,E.symm_apply_apply]
  right_inv y := by
    dsimp only
    rw [E.apply_symm_apply,smul_smul,mul_inv_cancel₀ hq,one_smul]
    abel
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] lemma affineHomeomorph_apply (p : Point) (q : ℝ) (hq : q≠0)
    (E : Point ≃L[ℝ] Point) (x : Point) : affineHomeomorph p q hq E x=p+q • E x := rfl

@[simp] lemma affineHomeomorph_symm_apply (p : Point) (q : ℝ) (hq : q≠0)
    (E : Point ≃L[ℝ] Point) (y : Point) : (affineHomeomorph p q hq E).symm y=E.symm (q⁻¹ • (y-p)) := rfl

noncomputable def affineZoom (f : OpenPartialHomeomorph Point Point)
    (E B : Point ≃L[ℝ] Point) (p x₀ : Point) (q h : ℝ) (hq : q≠0) (hh : h≠0) :
    OpenPartialHomeomorph Point Point :=
  ((affineHomeomorph x₀ q hq E).transOpenPartialHomeomorph f).transHomeomorph
    (affineHomeomorph p h hh B.symm).symm

@[simp] lemma affineZoom_apply (f : OpenPartialHomeomorph Point Point)
    (E B : Point ≃L[ℝ] Point) (p x₀ : Point) (q h : ℝ) (hq : q≠0) (hh : h≠0) (x : Point) :
    affineZoom f E B p x₀ q h hq hh x=B (h⁻¹ • (f (x₀+q • E x)-p)) := rfl

@[simp] lemma affineZoom_target (f : OpenPartialHomeomorph Point Point)
    (E B : Point ≃L[ℝ] Point) (p x₀ : Point) (q h : ℝ) (hq : q≠0) (hh : h≠0) :
    (affineZoom f E B p x₀ q h hq hh).target={w | p+h • B.symm w∈f.target} := rfl

end PlanarHalving.Zoom

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

def foliationTriple {α : Type*} (a b c : α) : Foliation → α
  | .horizontal => a
  | .vertical => c
  | .diagonal => b

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.ZoomControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

noncomputable def forwardUnit (F : Configuration) (E : Point ≃L[ℝ] Point) (t : I) : Point :=
  ‖E.symm (1,F.timeSlope t)‖⁻¹ • E.symm (1,F.timeSlope t)

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Foliations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

noncomputable def normalizedLinear (A : Point ≃L[ℝ] Point) : Point →L[ℝ] Point :=
  ‖A.toContinuousLinearMap‖⁻¹ • A.toContinuousLinearMap

end PlanarHalving.Zoom

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

@[simp] lemma affineZoom_symm_apply (f : OpenPartialHomeomorph Point Point)
    (E B : Point ≃L[ℝ] Point) (p x₀ : Point) (q h : ℝ) (hq : q≠0) (hh : h≠0) (y : Point) :
    (affineZoom f E B p x₀ q h hq hh).symm y=
      E.symm (q⁻¹ • (f.symm (p+h • B.symm y)-x₀)) := rfl

end PlanarHalving.Zoom

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

def RadialCompare (f : Point → Point) (p : Point) (h C T : ℝ) : Prop :=
  (∀ u v : Point, ‖u-p‖=h/T → ‖v-p‖=h →
    ‖f v-f p‖ ≤ C*T*‖f u-f p‖) ∧
  (∀ u v : Point, ‖u-p‖=h/T → ‖v-p‖=h →
    T*‖f u-f p‖ ≤ C*‖f v-f p‖)

end PlanarHalving.Zoom

namespace PlanarHalving.Zoom
open Set Filter Metric
open scoped Topology

def FrameCondition (B : Point ≃L[ℝ] Point) (S : Fin 3 → Set ℝ)
    (v : Fin 3 → Point) (ε : ℝ) : Prop :=
  ∀ (A : ℕ → Point ≃L[ℝ] Point) (u : ℕ → Fin 3 → Point),
    (∀ n i, ‖u n i‖=1) →
    (∀ ρ : ℕ → ℕ, StrictMono ρ → ∀ x : Fin 3 → Point,
      Tendsto (u ∘ ρ) atTop (𝓝 x) →
      ∀ i, ∃ z∈S i, detPair (x i) (B (RankLimits.reflectFirst (Directions.simplex z)))=0) →
    (∀ n i, detPair (A n (u n i)) (v i)=0) →
    ∀ᶠ n in atTop, ∀ x : Point, ‖x‖=1 → ε ≤ ‖normalizedLinear (A n) x‖

end PlanarHalving.Zoom

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Noncollapse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.TimeWindows
open Set Filter MeasureTheory
open scoped Topology unitInterval

def CommonChoice (K : Window) := {q : Window × Window × Window //
  lower K<lower q.1 ∧ upper q.1<lower q.2.1 ∧ upper q.2.1<upper K ∧
  lower q.1<lower q.2.2 ∧ upper q.2.2<upper q.1}
instance instCountableCommonChoice (K : Window) : Countable (CommonChoice K) := by unfold CommonChoice; infer_instance

noncomputable def CommonChoice.time {K : Window} (q : CommonChoice K) : Fin 3 → I :=
  ![lower q.val.1,upper q.val.1,upper q.val.2.1]

end PlanarHalving.TimeWindows

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.SpatialMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Spatial
open Set Filter Metric
open scoped Topology

abbrev UnitSphere := {u : Point // ‖u‖=1}
instance instNonemptyUnitSphere : Nonempty UnitSphere := ⟨⟨(1,0),by simp [Prod.norm_def]⟩⟩
instance instCompactSpaceUnitSphere : CompactSpace UnitSphere := by
  have hc : IsCompact (sphere (0:Point) 1) := isCompact_sphere _ _
  have he : sphere (0:Point) 1 = {u | ‖u‖=1} := by ext x; simp
  rw [he] at hc
  exact isCompact_iff_compactSpace.mp hc

noncomputable def radialU (f : Point → Point) (p : Point) (h : ℝ) : ℝ :=
  sSup (range fun u : UnitSphere => dist (f (p+h • (u:Point))) (f p))
noncomputable def radialV (f : Point → Point) (p : Point) (h : ℝ) : ℝ :=
  sInf (range fun u : UnitSphere => dist (f (p+h • (u:Point))) (f p))

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Filter MeasureTheory Metric Zoom
open scoped Topology

noncomputable def rankCore (h : ℝ) : Set Point :=
  Icc (2*h) (1-2*h) ×ˢ Icc (-1+2*h) (-2*h)

def ScaleGood (f : ℕ → Point → Point) (h q α β : ℝ) : Set Point :=
  {p | p∈rankCore h ∧ ∀ j : ℕ, ∀ᶠ n in atTop,
    α*radialU (f n) p (h*q^j)≤radialV (f n) p (h*q^(j+1)) ∧
    radialU (f n) p (h*q^(j+1))≤β*radialV (f n) p (h*q^j)}

end PlanarHalving.Spatial

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.MassEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Spatial
open Set Filter Metric Zoom
open scoped Topology

noncomputable def normalizeChart (f : OpenPartialHomeomorph Point Point)
    (p : Point) (U : ℝ) (hU : U≠0) : OpenPartialHomeomorph Point Point :=
  (affineHomeomorph (f.symm p) U hU (ContinuousLinearEquiv.refl ℝ Point)).transOpenPartialHomeomorph f

@[simp] lemma normalizeChart_symm (f : OpenPartialHomeomorph Point Point)
    (p : Point) (U : ℝ) (hU : U≠0) (x : Point) :
    (normalizeChart f p U hU).symm x=U⁻¹ • (f.symm x-f.symm p) := rfl

@[simp] lemma normalizeChart_target (f : OpenPartialHomeomorph Point Point)
    (p : Point) (U : ℝ) (hU : U≠0) : (normalizeChart f p U hU).target=f.target := rfl

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal unitInterval

abbrev Cube := I × I
noncomputable def encode (p : Point) : Cube := (unitInterval.sigmoid p.1,unitInterval.sigmoid p.2)
noncomputable def decode (p : Cube) : Point :=
  (-Real.log ((p.1:ℝ)⁻¹-1),-Real.log ((p.2:ℝ)⁻¹-1))

@[simp] lemma decode_encode (p : Point) : decode (encode p)=p := by
  have hn (t : ℝ) : -Real.log ((unitInterval.sigmoid t:ℝ)⁻¹-1)=t := by
    change -Real.log (((1+Real.exp (-t))⁻¹)⁻¹-1)=t
    simp
  exact Prod.ext (hn p.1) (hn p.2)

end PlanarHalving.Spatial

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Enhancement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Enhancement
open RankLimits Batches TimeWindows Limits Spatial MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

abbrev Space := Labels × Cube
noncomputable def label (F : Configuration) (ψ : Point → Point) (p : Point) : Space :=
  (F.label p,encode (ψ p))
noncomputable def points (F : Configuration) (ψ : Point → Point) : FiniteMeasure Space :=
  weightedAtoms (F.n:ℝ≥0)⁻¹ (fun v => label F ψ (F.point v))
noncomputable def vertices (F : Configuration) (ψ : Point → Point) (J : Window) : FiniteMeasure Space :=
  (F.system.timeWindow J).vertexMeasure (fun v => label F ψ (F.point v))
noncomputable def edges (F : Configuration) (ψ : Point → Point) (J : Window) : FiniteMeasure Space :=
  (F.system.timeWindow J).endpointMeasure (fun v => label F ψ (F.point v)) ((F.R:ℝ≥0)*F.a^2)

inductive Index where
  | point
  | vertex (J : Window)
  | edge (J : Window)
  deriving Countable

noncomputable def measures (F : Configuration) (ψ : Point → Point) : Index → FiniteMeasure Space
  | .point => points F ψ
  | .vertex J => vertices F ψ J
  | .edge J => edges F ψ J
noncomputable def old (L : Data) : Index → FiniteMeasure Labels
  | .point => L.points
  | .vertex J => L.vertices J
  | .edge J => L.edgeWindow J

end PlanarHalving.Enhancement

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.BoundaryTokens
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Boundary
open Set
open scoped Classical

def InSquare (a b : ℝ) (x : Point) : Prop := a<x.1 ∧ x.1<b ∧ a<x.2 ∧ x.2<b

end PlanarHalving.Boundary

namespace PlanarHalving.Boundary
open Set
open scoped Classical

noncomputable def rawNormal (t : ℝ) : Point := (-t,1-t)
noncomputable def frameWeight (a b l u s : ℝ) : ℝ := a*(s-l)+b*(u-s)
noncomputable def frameParameter (a b l u s : ℝ) : ℝ := a*(s-l)/frameWeight a b l u s

end PlanarHalving.Boundary

namespace PlanarHalving.Boundary
open Set
open scoped Classical

noncomputable def physical (E : Point ≃L[ℝ] Point) (o : Point) (r : ℝ) (p : Point) : Point :=
  r • E.symm (p-o)

end PlanarHalving.Boundary

namespace PlanarHalving.Boundary
open Set
open scoped Classical

noncomputable def clipCut (c : ℝ) : ℝ := max (-4) (min 4 c)

end PlanarHalving.Boundary

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.ThinStrips
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Spatial
open Set Filter MeasureTheory Boundary
open scoped Topology unitInterval

noncomputable def awayStrips (t θ : ℝ) (c : Fin 3 → ℝ) : Set Point :=
  {x | InSquare (-2) 2 x ∧ ∀ j, 18*θ < |dot (rawNormal t) x-c j|}

end PlanarHalving.Spatial

namespace PlanarHalving.Boundary
open Set
open scoped Classical

noncomputable def batchRange (R s m : ℕ) : Finset (Fin R) :=
  Finset.univ.filter fun i => s ≤ i.val ∧ i.val < s+m

end PlanarHalving.Boundary

namespace PlanarHalving.TimeWindows
open Set

lemma cuts_of_subset (R : ℕ) [NeZero R] {J K : Window} (h : carrier J⊆carrier K) :
    start R K ≤ start R J ∧ stop R J ≤ stop R K := by
  obtain ⟨hl,hu⟩ := endpoints_of_subset h
  exact ⟨cut_mono _ hl,cut_mono _ hu⟩

lemma relative_end_le (R : ℕ) [NeZero R] {J K : Window} (h : carrier J⊆carrier K) :
    start R J-start R K+length R J≤length R K := by
  have hcut := cuts_of_subset R h
  have hJ := start_add_length R J
  have hK := start_add_length R K
  omega

end PlanarHalving.TimeWindows

namespace PlanarHalving.Boundary
open Set Filter
open scoped Topology unitInterval PiCountable

abbrev CompactParams := Icc (0:ℝ) 4 × I × I × (Fin 3 → Icc (-4:ℝ) 4)

end PlanarHalving.Boundary

namespace PlanarHalving.Batches
open Set Boundary
open scoped Classical
variable {n R k a : ℕ} {P : Fin n → Point}

noncomputable def System.boundaryCount (S : @System n R k a P) [NeZero a]
    (p : Fin n → Point) (j : Fin a) (i : Fin R) : ℕ :=
  (Finset.univ.filter fun u : ↥(S.marks 0) =>
    ¬(InSquare (-2) 2 (p (S.tokenState j i.castSucc u)) ↔
      InSquare (-2) 2 (p (S.tokenState j i.succ u)))).card

end PlanarHalving.Batches

namespace PlanarHalving.TimeWindows
open Set Boundary
open scoped Classical
abbrev Subwindow (K : Window) := {J : Window // carrier J ⊆ carrier K}

end PlanarHalving.TimeWindows

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.ActivityRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Set TimeWindows Boundary
open scoped Classical

lemma localPartition_subset {K J : Window} {m : ℕ} (h : J∈localPartition K m) : carrier J⊆carrier K :=
  (Finset.mem_filter.mp h).2

noncomputable def subPartition (K : Window) (m : ℕ) : Finset (Subwindow K) :=
  (localPartition K m).attach.image (fun J => (⟨J.val,localPartition_subset J.property⟩ : Subwindow K))

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Batches TimeWindows Limits
open scoped Topology unitInterval ENNReal

noncomputable def commonSet (L : Data) {K : Window} (q : CommonChoice K) : Set Labels :=
  {z | L.conditional z (carrier q.val.1)≠0 ∧ L.conditional z (carrier q.val.2.1)≠0 ∧
    L.conditional z (carrier q.val.2.2)≠0}

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Packing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows Zoom
open scoped Topology unitInterval

noncomputable def commonDirection : Fin 3 → Point := ![(1,0),(1,1),(0,1)]

noncomputable def commonChart (F : Configuration) {A B : Window} (hAB : Before A B)
    (hA : 0<length F.R A) (hB : 0<length F.R B) (E : Point ≃L[ℝ] Point) :
    OpenPartialHomeomorph Point Point :=
  E.toHomeomorph.transOpenPartialHomeomorph (F.rankChart hAB hA hB)

@[simp] lemma commonChart_symm (F : Configuration) {A B : Window} (hAB : Before A B)
    (hA : 0<length F.R A) (hB : 0<length F.R B) (E : Point ≃L[ℝ] Point) (p : Point) :
    (commonChart F hAB hA hB E).symm p=E.symm ((F.rankChart hAB hA hB).symm p) := rfl

end PlanarHalving.RankLimits

namespace PlanarHalving.Sweep
open Set RankLimits

noncomputable def greedyConfiguration {n k : ℕ} {P : Fin n → Point}
    (hP : Generic P) (hk : k≤n) (a : ℕ) (ha : 0<a) (hn : 0<n)
    (hR : 0<((states P hP hk).greedy 0 a ha).count) : Configuration where
  n := n
  R := ((states P hP hk).greedy 0 a ha).count
  k := k
  a := a
  n_pos := hn
  R_pos := hR
  a_pos := ha
  point := P
  generic := hP
  system := (states P hP hk).greedySystem a ha

noncomputable def greedyConfiguration_embedding {n k : ℕ} {P : Fin n → Point}
    (hP : Generic P) (hk : k≤n) (a : ℕ) (ha : 0<a) (hn : 0<n)
    (hR : 0<((states P hP hk).greedy 0 a ha).count) :
    (greedyConfiguration hP hk a ha hn hR).SweepEmbedding where
  rank_le := hk
  index := ((states P hP hk).greedy 0 a ha).index
  increasing := ((states P hP hk).greedy 0 a ha).increasing
  marks := fun _ => rfl

end PlanarHalving.Sweep

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Greedy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving
open Set

namespace Sweep
variable {n T k : ℕ} {P : Fin n → Point}

lemma States.outside_activity_constant (S : @States n T k P)
    {u v : Fin (T+1)} (huv : u ≤ v) {x : Fin n} (hx : x ∉ S.intervalActivity u v huv)
    {i : Fin (T+1)} (hui : u ≤ i) (hiv : i ≤ v) : x ∈ S.marks i  ↔  x ∈ S.marks u := by
  by_contra H
  apply hx
  rw [S.mem_intervalActivity huv]
  exact ⟨i,hui,hiv,by tauto⟩

lemma States.intervalActivity_self (S : @States n T k P) (u : Fin (T+1)) :
    S.intervalActivity u u le_rfl=∅ := by
  classical
  ext x
  simp only [Finset.notMem_empty,iff_false,S.mem_intervalActivity]
  rintro ⟨i,hi,hj,h⟩
  have he : i=u := le_antisymm hj hi
  subst i
  tauto

lemma States.intervalActivity_step_subset (S : @States n T k P)
    {u : Fin (T+1)} (j : Fin T) (hu : u ≤ j.castSucc) :
    S.intervalActivity u j.succ (hu.trans (Fin.castSucc_le_succ j))⊆
      S.intervalActivity u j.castSucc hu ∪ ((S.marks j.castSucc\S.marks j.succ)∪
        (S.marks j.succ\S.marks j.castSucc)) := by
  classical
  intro x hx
  obtain ⟨i,hui,hij,hi⟩ := (S.mem_intervalActivity _).mp hx
  by_cases hprev : i ≤ j.castSucc
  · exact Finset.mem_union_left _ ((S.mem_intervalActivity hu).mpr ⟨i,hui,hprev,hi⟩)
  · have he : i=j.succ := Fin.ext (by change i.val=j.val+1;change i.val ≤ j.val+1 at hij;change ¬i.val ≤ j.val at hprev;omega)
    subst i
    by_cases hbefore : x ∈ S.intervalActivity u j.castSucc hu
    · exact Finset.mem_union_left _ hbefore
    · have hb := S.outside_activity_constant hu hbefore hu le_rfl
      apply Finset.mem_union_right
      simp only [Finset.mem_union,Finset.mem_sdiff]
      tauto

lemma States.intervalActivity_step_card (S : @States n T k P)
    {u : Fin (T+1)} (j : Fin T) (hu : u ≤ j.castSucc) :
    (S.intervalActivity u j.succ (hu.trans (Fin.castSucc_le_succ j))).card ≤
      (S.intervalActivity u j.castSucc hu).card+2 := by
  have h := Finset.card_le_card (S.intervalActivity_step_subset j hu)
  have h1 := Finset.card_union_le (S.intervalActivity u j.castSucc hu)
    ((S.marks j.castSucc\S.marks j.succ)∪(S.marks j.succ\S.marks j.castSucc))
  have h2 := Finset.card_union_le (S.marks j.castSucc\S.marks j.succ) (S.marks j.succ\S.marks j.castSucc)
  have h3 := S.step j
  have h4 := Finset.card_sdiff_comm ((S.card_marks j.castSucc).trans (S.card_marks j.succ).symm)
  change (S.marks j.castSucc\S.marks j.succ).card ≤ 1 at h3
  omega

end Sweep
end PlanarHalving
namespace PlanarHalving.Sweep
open Set
variable {n T k : ℕ} {P : Fin n → Point}

noncomputable def States.activitySize (S : @States n T k P) (u v : Fin (T+1)) : ℕ :=
  if h : u ≤ v then (S.intervalActivity u v h).card else 0

lemma States.activitySize_eq (S : @States n T k P) {u v : Fin (T+1)} (h : u ≤ v) :
    S.activitySize u v=(S.intervalActivity u v h).card := dite_eq_left h

lemma States.activitySize_self (S : @States n T k P) (u : Fin (T+1)) : S.activitySize u u=0 := by
  rw [S.activitySize_eq le_rfl,S.intervalActivity_self,Finset.card_empty]

noncomputable def States.activityEligible (S : @States n T k P) (s : Fin (T+1)) (b : ℕ) : Finset (Fin (T+1)) :=
  Finset.univ.filter (fun t => s<t ∧ b ≤ S.activitySize s t)

noncomputable def States.activityNext (S : @States n T k P) (s : Fin (T+1)) (b : ℕ)
    (h : (S.activityEligible s b).Nonempty) : Fin (T+1) := (S.activityEligible s b).min' h

lemma States.activityNext_spec (S : @States n T k P) (s : Fin (T+1)) (b : ℕ)
    (h : (S.activityEligible s b).Nonempty) : s<S.activityNext s b h ∧ b ≤ S.activitySize s (S.activityNext s b h) := by
  exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2

lemma States.before_activityNext (S : @States n T k P) (s : Fin (T+1)) {b : ℕ} (hb : 0<b)
    (h : (S.activityEligible s b).Nonempty) {t : Fin (T+1)} (hst : s ≤ t) (ht : t<S.activityNext s b h) :
    S.activitySize s t<b := by
  by_cases he : t=s
  · subst t;simpa only [S.activitySize_self] using hb
  by_contra hh
  have hm : t ∈ S.activityEligible s b := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,lt_of_le_of_ne hst (Ne.symm he),le_of_not_gt hh⟩
  exact not_le_of_gt ht (Finset.min'_le _ _ hm)

lemma States.activityNext_bound (S : @States n T k P) (s : Fin (T+1)) {b : ℕ} (hb : 0<b)
    (h : (S.activityEligible s b).Nonempty) : S.activitySize s (S.activityNext s b h) ≤ b+1 := by
  have hs := (S.activityNext_spec s b h).1
  let j : Fin T := ⟨(S.activityNext s b h).val-1,by have:=(S.activityNext s b h).isLt;omega⟩
  have hj : j.succ=S.activityNext s b h := by apply Fin.ext;dsimp [j];omega
  have hsj : s ≤ j.castSucc := by change s.val ≤ (S.activityNext s b h).val-1;exact Nat.le_sub_one_of_lt hs
  have hprev := S.before_activityNext s hb h hsj (by rw [←hj];exact Fin.castSucc_lt_succ)
  have hstep := S.intervalActivity_step_card j hsj
  rw [←S.activitySize_eq,←S.activitySize_eq,hj] at hstep
  omega

structure States.ActivityGreedy (S : @States n T k P) (s : Fin (T+1)) (b : ℕ) where
  count : ℕ
  index : Fin (count+1) → Fin (T+1)
  first : index 0=s
  increasing : StrictMono index
  lower : ∀ j : Fin count, b ≤ S.activitySize (index j.castSucc) (index j.succ)
  upper : ∀ j : Fin count, S.activitySize (index j.castSucc) (index j.succ) ≤ b+1
  tail : S.activitySize (index (Fin.last count)) (Fin.last T)<b

noncomputable def States.activityGreedy (S : @States n T k P) (s : Fin (T+1)) (b : ℕ) (hb : 0<b) :
    S.ActivityGreedy s b := by
  classical
  by_cases h : (S.activityEligible s b).Nonempty
  · let t := S.activityNext s b h
    have ht : s<t := (S.activityNext_spec s b h).1
    let Q := S.activityGreedy t b hb
    refine ⟨Q.count+1,Fin.cons s Q.index,by simp,?_,?_,?_,?_⟩
    · apply Fin.strictMono_cons.mpr
      refine ⟨?_,Q.increasing⟩
      intro j
      exact ht.trans_le (by simpa only [Q.first] using Q.increasing.monotone (Fin.zero_le j))
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa only [Fin.castSucc_zero,Fin.cons_zero,Fin.cons_succ,Q.first] using (S.activityNext_spec s b h).2
      · simpa only [Fin.castSucc_succ,Fin.cons_succ] using Q.lower j
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa only [Fin.castSucc_zero,Fin.cons_zero,Fin.cons_succ,Q.first] using S.activityNext_bound s hb h
      · simpa only [Fin.castSucc_succ,Fin.cons_succ] using Q.upper j
    · simpa only [Fin.cons_last] using Q.tail
  · refine ⟨0,fun _ => s,rfl,?_,(fun j => Fin.elim0 j),(fun j => Fin.elim0 j),?_⟩
    · intro i j hij
      exact False.elim (by have:=i.isLt;have:=j.isLt;change i.val<j.val at hij;omega)
    ·
      by_cases he : s=Fin.last T
      · subst s;simpa only [S.activitySize_self] using hb
      · by_contra hn
        exact h ⟨Fin.last T,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          lt_of_le_of_ne (Fin.le_last _) he,le_of_not_gt hn⟩⟩
termination_by T-s.val
decreasing_by
  have ht := (S.activityNext_spec s b h).1
  change s.val<(S.activityNext s b h).val at ht
  omega

noncomputable def States.ActivityGreedy.intervals (S : @States n T k P) {s : Fin (T+1)} {b : ℕ}
    (Q : S.ActivityGreedy s b) : Finset (Fin (T+1) × Fin (T+1)) :=
  Finset.univ.image (fun j : Fin Q.count => (Q.index j.castSucc,Q.index j.succ))

end PlanarHalving.Sweep

namespace PlanarHalving.Sweep
open Set

def Refines {n : ℕ} (P : Fin n → Point) (c s : ℝ) : Prop :=
  ∀ i j, projection c (P i)<projection c (P j) → projection s (P i)<projection s (P j)

noncomputable def belowSet {n : ℕ} (P : Fin n → Point) (a b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun l => projection (slope (P a) (P b)) (P l)<projection (slope (P a) (P b)) (P a))

end PlanarHalving.Sweep

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Decomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Sweep
open Set

noncomputable def switchPairs {n : ℕ} (P : Fin n → Point) (k : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2 ∧ 0<k ∧ k<n ∧ belowCount P ij.1 ij.2=k-1)

noncomputable def States.changeSteps {n T k : ℕ} {P : Fin n → Point} (S : @States n T k P) : Finset (Fin T) :=
  Finset.univ.filter (fun i => S.marks i.castSucc≠S.marks i.succ)

end PlanarHalving.Sweep

namespace PlanarHalving.Sweep
open Set

noncomputable def subsetIndex {n : ℕ} (A : Finset (Fin n)) : Fin A.card → Fin n :=
  fun i => (A.orderIsoOfFin rfl i : Fin n)

noncomputable def subsetPoints {n : ℕ} (P : Fin n → Point) (A : Finset (Fin n)) : Fin A.card → Point :=
  P∘subsetIndex A

noncomputable def restrictMarks {n : ℕ} (A M : Finset (Fin n)) : Finset (Fin A.card) :=
  Finset.univ.filter (fun i => subsetIndex A i∈M)

variable {n T k : ℕ} {P : Fin n → Point}

noncomputable def States.blockSteps (S : @States n T k P) (u v : Fin (T+1)) : Finset (Fin T) :=
  S.changeSteps.filter (fun i => u ≤ i.castSucc ∧ i.succ ≤ v)

end PlanarHalving.Sweep

namespace PlanarHalving.Sweep
open Set
variable {n T k : ℕ} {P : Fin n → Point}

noncomputable def States.ActivityGreedy.fullIndex (S : @States n T k P) {s : Fin (T+1)} {b : ℕ}
    (G : S.ActivityGreedy s b) : Fin (G.count+2) → Fin (T+1) :=
  Fin.snoc G.index (Fin.last T)

end PlanarHalving.Sweep

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Perturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Perturbation
open Set

noncomputable def intercept (p q : Point) : ℝ := p.2-slope p q*p.1
noncomputable def intersectionPoint (p q r s : Point) : Point :=
  let x := (intercept r s-intercept p q)/(slope p q-slope r s)
  (x,slope p q*x+intercept p q)

abbrev Edge (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

noncomputable def edgeSlope {n : ℕ} (P : Fin n → Point) (e : Edge n) := slope (P e.val.1) (P e.val.2)
def onLine {n : ℕ} (P : Fin n → Point) (e : Edge n) (z : Point) := orient (P e.val.1) (P e.val.2) z=0

structure Regular {n : ℕ} (P : Fin n → Point) : Prop where
  general : GeneralPosition P
  xdistinct : ∀ i j, i≠j → (P i).1≠(P j).1
  slopes : Function.Injective (edgeSlope P)
  concurrent : ∀ e f g : Edge n, e≠f → g≠e → g≠f → ∀ z : Point,
    onLine P e z → onLine P f z → onLine P g z → ∃ v, P v=z

def newEdge {n : ℕ} (i : Fin n) : Edge (n+1) := ⟨(0,i.succ),Fin.succ_pos i⟩
def oldEdge {n : ℕ} (e : Edge n) : Edge (n+1) := ⟨(e.val.1.succ,e.val.2.succ),Fin.succ_lt_succ_iff.mpr e.property⟩

@[simp] lemma edgeSlope_new {n : ℕ} (P : Fin n → Point) (p : Point) (i : Fin n) :
    edgeSlope (Fin.cons p P) (newEdge i)=slope p (P i) := by simp [edgeSlope,newEdge]
@[simp] lemma edgeSlope_old {n : ℕ} (P : Fin n → Point) (p : Point) (e : Edge n) :
    edgeSlope (Fin.cons p P) (oldEdge e)=edgeSlope P e := by simp [edgeSlope,oldEdge]
@[simp] lemma onLine_new {n : ℕ} (P : Fin n → Point) (p z : Point) (i : Fin n) :
    onLine (Fin.cons p P) (newEdge i) z ↔ orient p (P i) z=0 := by simp [onLine,newEdge]
@[simp] lemma onLine_old {n : ℕ} (P : Fin n → Point) (p z : Point) (e : Edge n) :
    onLine (Fin.cons p P) (oldEdge e) z ↔ onLine P e z := by simp [onLine,oldEdge]

end PlanarHalving.Perturbation
namespace PlanarHalving.Perturbation
open Set

noncomputable def edgeMeet {n : ℕ} (P : Fin n → Point) (e f : Edge n) : Point :=
  intersectionPoint (P e.val.1) (P e.val.2) (P f.val.1) (P f.val.2)

def Fresh {n : ℕ} (P : Fin n → Point) (p : Point) : Prop :=
  (∀ i, p.1≠(P i).1) ∧
  (∀ i j, i≠j → orient (P i) (P j) p≠0) ∧
  (∀ i e, Sweep.projection (edgeSlope P e) p≠Sweep.projection (edgeSlope P e) (P i)) ∧
  (∀ i e f, edgeMeet P e f≠P i → orient (P i) (edgeMeet P e f) p≠0)

end PlanarHalving.Perturbation

end OAI
end


