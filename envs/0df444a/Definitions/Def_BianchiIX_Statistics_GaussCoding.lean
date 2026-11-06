-- Prove2me | Definitions.Def_BianchiIX_Statistics_GaussCoding
-- name    : BianchiIX_Statistics_GaussCoding
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T14:41:14.753099+00:00
-- url     : https://prove2.me/theorems/bee55eca-54b9-477d-8e9e-fdb293ca9b25
-- title:
--   Continued-fraction coding of positive digit sequences
-- statement:
--   Let $A=\{1,2,3,\ldots\}$, and let $a=(a_0,a_1,\ldots)\in A^{\mathbb N}$.
--   For $b\in A$, write $g_b(x)=1/(b+x)$. For a finite word $w=(b_0,\ldots,b_{n-1})$,
--   set $G_w=g_{b_0}\circ\cdots\circ g_{b_{n-1}}$, with $G_{\varnothing}$ the identity.
--   Define
--   $$q_n(a)=G_{(a_0,\ldots,a_{n-1})}(0),\qquad
--   \pi(a)=\lim_{n\to\infty}q_n(a),\qquad (\sigma^m a)_j=a_{m+j}.$$
--   The limit exists by the uniform contraction of inverse words. Write
--   $T(x)=1/x-\lfloor1/x\rfloor$ for $x\ne0$ and $T(0)=0$.
--
--   The digit space carries the product sigma algebra of the discrete sigma algebra
--   on $A$. Finite prefixes, digit shifts, and the approximants $q_n$ supply the
--   coding construction. The convergence proof used to define $\pi$ is included
--   with these definitions.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussCoding.lean

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat

section
open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.gaussInv_pos {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) : 0 < gaussInv a x := by
  unfold gaussInv
  exact one_div_pos.mpr (by linarith)

end
end

section
open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.gaussInv_le_one {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) : gaussInv a x ≤ 1 := by
  unfold gaussInv
  exact (div_le_one (by linarith : 0 < a + x)).mpr (by linarith)

end
end

section
open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.gaussInv_pair_eq {a b x : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hx : 0 ≤ x) :
    gaussInv a (gaussInv b x) = (b + x) / (a * (b + x) + 1) := by
  have hbpos : 0 < b + x := by linarith
  have hapos : 0 < a + 1 / (b + x) := by positivity
  have hprod : 0 < a * (b + x) + 1 := by positivity
  unfold gaussInv
  field_simp

end
end

section
open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.gaussInv_lipschitz {a x y : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |gaussInv a x - gaussInv a y| ≤ |x - y| := by
  have hax : 0 < a + x := by linarith
  have hay : 0 < a + y := by linarith
  have hden : 1 ≤ (a + x) * (a + y) := by
    nlinarith [mul_nonneg (show 0 ≤ a + x - 1 by linarith)
      (show 0 ≤ a + y - 1 by linarith)]
  have hid : gaussInv a x - gaussInv a y = (y - x) / ((a + x) * (a + y)) := by
    unfold gaussInv
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos (mul_pos hax hay), abs_sub_comm y x]
  exact div_le_self (abs_nonneg _) hden

end
end

section
open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.gaussInv_pair_lipschitz
    {a b x y : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |gaussInv a (gaussInv b x) - gaussInv a (gaussInv b y)| ≤ (1 / 4) * |x - y| := by
  have hdx : 2 ≤ a * (b + x) + 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ b + x by linarith)]
  have hdy : 2 ≤ a * (b + y) + 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ b + y by linarith)]
  have hdxpos : 0 < a * (b + x) + 1 := by linarith
  have hdypos : 0 < a * (b + y) + 1 := by linarith
  have hden : 4 ≤ (a * (b + x) + 1) * (a * (b + y) + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdx) (sub_nonneg.mpr hdy)]
  rw [gaussInv_pair_eq ha hb hx, gaussInv_pair_eq ha hb hy]
  have hid : (b + x) / (a * (b + x) + 1) - (b + y) / (a * (b + y) + 1) =
      (x - y) / ((a * (b + x) + 1) * (a * (b + y) + 1)) := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos (mul_pos hdxpos hdypos)]
  calc
    _ ≤ |x - y| / 4 := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hden
    _ = (1 / 4) * |x - y| := by ring

end
end

section
open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.gaussWord_nonneg (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ gaussWord w x := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast hw a (by simp)
    exact (gaussInv_pos ha (ih (fun b hb => hw b (by simp [hb])))).le

end
end

section
open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.gaussWord_lipschitz (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |gaussWord w x - gaussWord w y| ≤ (1 / 4 : ℝ) ^ (w.length / 2) * |x - y| := by
  induction w using List.twoStepInduction with
  | nil => simp [gaussWord]
  | singleton a =>
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast hw a (by simp)
    simpa [gaussWord] using gaussInv_lipschitz ha hx hy
  | cons_cons a b w ih _ =>
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast hw a (by simp)
    have hb : (1 : ℝ) ≤ b := by exact_mod_cast hw b (by simp)
    have htail : ∀ c ∈ w, 1 ≤ c := fun c hc => hw c (by simp [hc])
    have hlen : (a :: b :: w).length / 2 = w.length / 2 + 1 := by
      simp [Nat.add_assoc, Nat.add_div_right]
    calc
      _ ≤ (1 / 4) * |gaussWord w x - gaussWord w y| :=
        gaussInv_pair_lipschitz ha hb (gaussWord_nonneg w htail hx) (gaussWord_nonneg w htail hy)
      _ ≤ (1 / 4) * ((1 / 4) ^ (w.length / 2) * |x - y|) :=
        mul_le_mul_of_nonneg_left (ih htail) (by norm_num)
      _ = _ := by rw [hlen, pow_succ]; ring

end
end

section
open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.gaussWord_diameter (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a)
    {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |gaussWord w x - gaussWord w y| ≤ (1 / 4 : ℝ) ^ (w.length / 2) := by
  have hxy : |x - y| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hy.1, hx.2]⟩
  calc
    _ ≤ (1 / 4 : ℝ) ^ (w.length / 2) * |x - y| := gaussWord_lipschitz w hw hx.1 hy.1
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hxy (by positivity :
      0 ≤ (1 / 4 : ℝ) ^ (w.length / 2))

end
end


/-! Infinite positive digit strings, their real values, and measurable coding. -/

namespace BianchiIX

noncomputable section

open Filter Set
open scoped Topology

instance _root_.BianchiIX.instMeasurableSpacePNat_bianchiIX : MeasurableSpace ℕ+ := inferInstanceAs (MeasurableSpace {n : ℕ // 0 < n})
instance _root_.BianchiIX.instMeasurableSingletonClassPNat_bianchiIX : MeasurableSingletonClass ℕ+ :=
  inferInstanceAs (MeasurableSingletonClass {n : ℕ // 0 < n})

def shiftDigits (a : ℕ → ℕ+) (k : ℕ) : ℕ → ℕ+ := fun i => a (k + i)



def digitPrefix (a : ℕ → ℕ+) (n : ℕ) : List ℕ :=
  (List.range n).map (fun i => (a i : ℕ))

def gaussApprox (a : ℕ → ℕ+) (n : ℕ) : ℝ := gaussWord (digitPrefix a n) 0



theorem digitPrefix_positive (a : ℕ → ℕ+) (n : ℕ) :
    ∀ k ∈ digitPrefix a n, 1 ≤ k := by
  intro k hk
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hk
  exact Nat.succ_le_of_lt (a i).pos

theorem digitPrefix_length (a : ℕ → ℕ+) (n : ℕ) : (digitPrefix a n).length = n := by
  simp [digitPrefix]

theorem digitPrefix_add (a : ℕ → ℕ+) (n k : ℕ) :
    digitPrefix a (n + k) = digitPrefix a n ++ digitPrefix (shiftDigits a n) k := by
  simp [digitPrefix, List.range_add, List.map_map, Function.comp_def, shiftDigits]



theorem gaussWord_append (w v : List ℕ) (x : ℝ) :
    gaussWord (w ++ v) x = gaussWord w (gaussWord v x) := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa only [List.cons_append, gaussWord] using congrArg (gaussInv a) ih

theorem gaussWord_mem_unit (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : gaussWord w x ∈ Icc (0 : ℝ) 1 := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast hw a (by simp)
    have ht := ih (fun b hb => hw b (by simp [hb]))
    exact ⟨(gaussInv_pos ha ht.1).le, gaussInv_le_one ha ht.1⟩

theorem gaussApprox_mem_unit (a : ℕ → ℕ+) (n : ℕ) : gaussApprox a n ∈ Icc (0 : ℝ) 1 :=
  gaussWord_mem_unit _ (digitPrefix_positive a n) ⟨le_rfl, zero_le_one⟩

theorem gaussApprox_add (a : ℕ → ℕ+) (n k : ℕ) :
    gaussApprox a (n + k) = gaussWord (digitPrefix a n) (gaussApprox (shiftDigits a n) k) := by
  simp only [gaussApprox, digitPrefix_add, gaussWord_append]



theorem gaussApprox_distance (a : ℕ → ℕ+) {n k : ℕ} (hnk : n ≤ k) :
    |gaussApprox a n - gaussApprox a k| ≤ (1 / 4 : ℝ) ^ (n / 2) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnk
  rw [gaussApprox_add]
  simpa only [gaussApprox, digitPrefix_length] using
    gaussWord_diameter (digitPrefix a n) (digitPrefix_positive a n)
      (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩) (gaussApprox_mem_unit (shiftDigits a n) j)

theorem gauss_diameter_tendsto_zero :
    Tendsto (fun n : ℕ => (1 / 4 : ℝ) ^ (n / 2)) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun n : ℕ => n / 2) atTop atTop := by
    refine tendsto_atTop.mpr fun k => eventually_atTop.mpr ⟨2 * k, ?_⟩
    intro n hn
    omega
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hdiv

theorem gaussApprox_cauchy (a : ℕ → ℕ+) : CauchySeq (gaussApprox a) := by
  apply cauchySeq_of_le_tendsto_0' (fun n => (1 / 4 : ℝ) ^ (n / 2))
  · intro n k hnk
    simpa only [Real.dist_eq] using gaussApprox_distance a hnk
  · exact gauss_diameter_tendsto_zero

def gaussCode (a : ℕ → ℕ+) : ℝ :=
  (cauchySeq_tendsto_of_complete (gaussApprox_cauchy a)).choose















def gaussMap (x : ℝ) : ℝ := Int.fract (1 / x)































end

end BianchiIX


