-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Localization
-- name    : OAI_Analysis_C0Absorption_Localization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T20:59:34.090305+00:00
-- url     : https://prove2.me/theorems/866deef1-c600-42da-83de-9d5b6bd53360
-- title:
--   Localizing operators that flatten functions near a point
-- statement:
--   For a metric space $X$, a centre $q$, a radius $\varepsilon>0$ and a function $u$:
--
--   1. **Ramp.** $\chi(t)=\min(1,\max(0,2t-1))$, a $2$-Lipschitz ramp that is $0$ for $t\le\frac12$ and $1$ for $t\ge1$.
--   2. **Cutoff.** $\mathrm{cutoff}(q,\varepsilon)(x)=1-\chi(d(x,q)/\varepsilon)\in[0,1]$, which vanishes outside the ball of radius $\varepsilon$.
--   3. **Flattening.**
--   $$
--   G_{q,\varepsilon}u(x)=u(q)+\chi\bigl(d(x,q)/\varepsilon\bigr)\bigl(u(x)-u(q)\bigr),
--   $$
--   which equals $u(q)$ near $q$ and $u$ far away. The remainder is $R_{q,\varepsilon}u=G_{q,\varepsilon}u-u=\mathrm{cutoff}(q,\varepsilon)\cdot(u(q)-u)$.
--   4. **Bounds.** If $u$ is $L$-Lipschitz, then $G_{q,\varepsilon}u$ is $4L$-Lipschitz and $R_{q,\varepsilon}u$ is $3L$-Lipschitz. Both operators are linear in $u$.
--   5. **Local-to-global.** On a convex set, a continuous function that is locally $K$-Lipschitz is globally $K$-Lipschitz.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Localization.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Localization.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

open Set Filter Topology

theorem dist_le_of_local_interval {Y : Type*} [PseudoMetricSpace Y]
    {a b K : ℝ} (hab : a ≤ b) {f : ℝ → Y}
    (hf : ContinuousOn f (Icc a b))
    (hloc : ∀ x ∈ Icc a b, ∀ᶠ y in nhdsWithin x (Icc a b),
      dist (f x) (f y) ≤ K * dist x y) :
    dist (f a) (f b) ≤ K * (b-a) := by
  let s : Set ℝ := {x | dist (f a) (f x) ≤ K * (x-a)}
  have hclosed : IsClosed (s ∩ Icc a b) := by
    have hc : ContinuousOn (fun x => (dist (f a) (f x), K * (x-a))) (Icc a b) :=
      (show ContinuousOn (fun x => dist (f a) (f x)) (Icc a b) from
        fun x hx => tendsto_const_nhds.dist (hf x hx)).prodMk (continuousOn_const.mul
        (continuousOn_id.sub continuousOn_const))
    simpa only [s, inter_comm, Set.preimage_ofPred_eq] using hc.preimage_isClosed_of_isClosed isClosed_Icc
      OrderClosedTopology.isClosed_le'
  have ha : a ∈ s := by simp [s]
  have hs := hclosed.Icc_subset_of_forall_exists_gt ha
  apply hs ?_ ⟨hab, le_rfl⟩
  rintro x ⟨hx : dist (f a) (f x) ≤ K * (x-a), hxab⟩ y hxy
  have hh : ∀ᶠ z in nhdsWithin x (Ioi x), dist (f x) (f z) ≤ K * dist x z :=
    nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem hxab) (hloc x ⟨hxab.1, hxab.2.le⟩)
  obtain ⟨z, hz, hxz, hzy⟩ := (hh.and (Ioc_mem_nhdsGT hxy)).exists
  refine ⟨z, ?_, hxz, hzy⟩
  change dist (f a) (f z) ≤ K * (z-a)
  have hdist : dist x z = z-x := by rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxz.le)]; ring
  rw [hdist] at hz
  calc
    dist (f a) (f z) ≤ dist (f a) (f x) + dist (f x) (f z) := dist_triangle _ _ _
    _ ≤ K * (x-a) + K * (z-x) := add_le_add hx hz
    _ = K * (z-a) := by ring

theorem lipschitzOn_convex_of_local {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Y]
    {B : Set E} (hB : Convex ℝ B) {f : E → Y} {K : ℝ≥0}
    (hf : ContinuousOn f B)
    (hloc : ∀ x ∈ B, ∀ᶠ y in nhdsWithin x B, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzOnWith K f B := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let g : ℝ → E := AffineMap.lineMap x y
  have hg : Continuous g := by
    change Continuous (fun t : ℝ => t • (y-x) + x)
    fun_prop
  have hmap : MapsTo g (Icc 0 1) B := fun t ht => hB.lineMap_mem hx hy ht
  have hc : ContinuousOn (f ∘ g) (Icc 0 1) := hf.comp hg.continuousOn hmap
  have hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ u in nhdsWithin t (Icc 0 1),
      dist ((f ∘ g) t) ((f ∘ g) u) ≤ (K * dist x y) * dist t u := by
    intro t ht
    have hgt := (hg.continuousAt (x := t)).continuousWithinAt.tendsto_nhdsWithin hmap
    filter_upwards [hgt (hloc (g t) (hmap ht))] with u hu
    change dist (f (g t)) (f (g u)) ≤ _
    calc
      dist (f (g t)) (f (g u)) ≤ K * dist (g t) (g u) := hu
      _ = (K * dist x y) * dist t u := by
        rw [show dist (g t) (g u) = dist t u * dist x y from dist_lineMap_lineMap x y t u]
        ring
  have h := dist_le_of_local_interval (by norm_num : (0 : ℝ) ≤ 1) hc hh
  simpa [g, Function.comp_def] using h

noncomputable section

def chi (t : ℝ) : ℝ := min 1 (max 0 (2*t-1))

def cutoff {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (x : X) : ℝ :=
  1 - chi (dist x q / ε)

def localG {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (u : X → ℝ) (x : X) : ℝ :=
  u q + chi (dist x q / ε) * (u x-u q)

def localR {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (u : X → ℝ) (x : X) : ℝ :=
  localG q ε u x-u x

theorem cutoff_nonneg {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (x : X) :
    0 ≤ cutoff q ε x := by
  dsimp [cutoff, chi]
  have := min_le_left (1 : ℝ) (max 0 (2 * (dist x q / ε) - 1))
  linarith

theorem cutoff_le_one {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (x : X) :
    cutoff q ε x ≤ 1 := by
  dsimp [cutoff, chi]
  have : 0 ≤ min (1 : ℝ) (max 0 (2 * (dist x q / ε) - 1)) := by positivity
  linarith

theorem localR_eq {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (u : X → ℝ) (x : X) :
    localR q ε u x = cutoff q ε x * (u q-u x) := by
  dsimp [localR, localG, cutoff]
  ring

theorem localG_eq {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (u : X → ℝ) (x : X) :
    localG q ε u x = u x + localR q ε u x := by
  simp [localR]

theorem cutoff_eq_zero {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ} (hε : 0 < ε)
    (x : X) (hx : ε ≤ dist x q) : cutoff q ε x = 0 := by
  have hh : 1 ≤ dist x q / ε := (le_div_iff₀ hε).mpr (by simpa using hx)
  simp [cutoff, chi, max_eq_right (by linarith : 0 ≤ 2*(dist x q/ε)-1),
    min_eq_left (by linarith : (1:ℝ) ≤ 2*(dist x q/ε)-1)]

theorem dist_lt_of_cutoff_ne_zero {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ}
    (hε : 0 < ε) (x : X) (hx : cutoff q ε x ≠ 0) : dist x q < ε := by
  by_contra! hh
  exact hx (cutoff_eq_zero q hε x hh)

theorem chi_lipschitz : LipschitzWith 2 chi := by
  have h : LipschitzWith 2 (fun t : ℝ => 2*t-1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq, show (2*x-1)-(2*y-1)=2*(x-y) by ring, abs_mul]
    norm_num
  change LipschitzWith 2 (fun t : ℝ => min 1 (max 0 (2*t-1)))
  exact (h.const_max 0).const_min 1

theorem cutoff_dist_le {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ}
    (hε : 0 < ε) (x y : X) :
    |cutoff q ε x-cutoff q ε y| ≤ (2 / ε) * dist x y := by
  have h := chi_lipschitz.dist_le_mul (dist x q / ε) (dist y q / ε)
  simp only [Real.dist_eq, NNReal.coe_ofNat] at h
  have heq : |cutoff q ε x-cutoff q ε y| =
      |chi (dist x q/ε)-chi (dist y q/ε)| := by
    rw [cutoff, cutoff, sub_sub_sub_cancel_left, abs_sub_comm]
  rw [heq]
  calc
    |chi (dist x q/ε)-chi (dist y q/ε)| ≤ 2 * |dist x q/ε-dist y q/ε| := h
    _ = (2/ε)*|dist x q-dist y q| := by rw [← sub_div, abs_div, abs_of_pos hε]; ring
    _ ≤ (2/ε)*dist x y := mul_le_mul_of_nonneg_left
      (abs_dist_sub_le x y q) (by positivity)

theorem localR_lipschitz {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ}
    (hε : 0 < ε) (u : X → ℝ) {L : ℝ≥0} (hu : LipschitzWith L u) :
    LipschitzWith (3*L) (localR q ε u) := by
  have hb (x y : X) (hy : cutoff q ε y ≠ 0) :
      |localR q ε u x-localR q ε u y| ≤ (3*L : ℝ≥0)*dist x y := by
    have hd := (dist_lt_of_cutoff_ne_zero q hε y hy).le
    have huq : |u q-u y| ≤ ε*L := by
      calc
        |u q-u y| ≤ L*dist q y := hu.dist_le_mul q y
        _ ≤ L*ε := mul_le_mul_of_nonneg_left (by rwa [dist_comm]) L.coe_nonneg
        _ = ε*L := mul_comm _ _
    have heq : localR q ε u x-localR q ε u y =
        cutoff q ε x*(u y-u x)+(cutoff q ε x-cutoff q ε y)*(u q-u y) := by
      simp only [localR_eq]; ring
    rw [heq]
    calc
      |cutoff q ε x*(u y-u x)+(cutoff q ε x-cutoff q ε y)*(u q-u y)|
          ≤ |cutoff q ε x*(u y-u x)| + |(cutoff q ε x-cutoff q ε y)*(u q-u y)| := abs_add_le _ _
      _ = cutoff q ε x*|u y-u x| + |cutoff q ε x-cutoff q ε y| * |u q-u y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (cutoff_nonneg _ _ _)]
      _ ≤ 1 * (L*dist x y) + ((2/ε)*dist x y)*(ε*L) := by
        apply add_le_add
        · apply mul_le_mul (cutoff_le_one q ε x)
          · have hd := hu.dist_le_mul y x
            rw [dist_comm y x] at hd
            exact hd
          · exact abs_nonneg _
          · norm_num
        · exact mul_le_mul (cutoff_dist_le q hε x y) huq (abs_nonneg _) (by positivity)
      _ = (3*L : ℝ≥0)*dist x y := by
        push_cast
        field_simp
        ; ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  by_cases hy : cutoff q ε y = 0
  · by_cases hx : cutoff q ε x = 0
    · simp [localR_eq, hx, hy]; positivity
    · simpa only [abs_sub_comm, dist_comm] using hb y x hx
  · exact hb x y hy

theorem localG_lipschitz {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ}
    (hε : 0 < ε) (u : X → ℝ) {L : ℝ≥0} (hu : LipschitzWith L u) :
    LipschitzWith (4*L) (localG q ε u) := by
  have heq : localG q ε u = fun x => u x+localR q ε u x := funext (localG_eq q ε u)
  rw [heq]
  have hc : L+3*L=4*L := by ring
  rw [← hc]
  exact hu.add (localR_lipschitz q hε u hu)

def localGLinear {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) :
    (X → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun := localG q ε
  map_add' u v := by ext x; simp only [localG, Pi.add_apply]; ring
  map_smul' c u := by ext x; simp only [localG, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def localRLinear {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) :
    (X → ℝ) →ₗ[ℝ] (X → ℝ) := localGLinear q ε - LinearMap.id

@[simp] theorem localRLinear_apply {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ)
    (u : X → ℝ) : localRLinear q ε u = localR q ε u := rfl

def localOp {X : Type*} [PseudoMetricSpace X] (isG : Bool) (q : X) (ε : ℝ) :
    (X → ℝ) →ₗ[ℝ] (X → ℝ) := if isG then localGLinear q ε else localRLinear q ε

end

end
end C0Absorption

end OAI


