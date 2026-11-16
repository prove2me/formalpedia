-- Prove2me | Definitions.Def_LowRandomnessDP_KNorm_Supplement_Rounding
-- name    : LowRandomnessDP_KNorm_Supplement_Rounding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:28:03.900352+00:00
-- url     : https://prove2.me/theorems/145f95a0-a55e-4429-991b-1f1375d1f8a1
-- title:
--   Algorithm 1 — smallest-shift rounding and its fibre partition
-- statement:
--   For every positive integer $d$, write $\mathbb R^d$ for real coordinate vectors and $\{u\}=u-\lfloor u\rfloor$ for the fractional part, including for negative $u$. For $a\in\{0,\ldots,d-1\}$, define
--
--   $$\Phi_a(x)=\sum_{i=1}^d\{x_i-a/d\},\qquad A(x)=\min\operatorname*{argmin}_{0\le a<d}\Phi_a(x),\qquad R(x)_i=A(x)/d+\lfloor x_i-A(x)/d\rfloor.$$
--
--   The partition consists of the nonempty fibres $\{x:R(x)=y\}$, indexed by outputs $y$ in the range of $R$. The representative of this fibre is $y$ itself. The construction proves $R(R(x))=R(x)$ and the partition axioms, and the finite-minimum API certifies both minimization and the smallest-shift tie-break. These structural facts are used only to construct the objects; none of the five numbered estimates is supplied by the definitions.
--
--   Also define $K_\infty=\{x:\forall i,\ |x_i|\le1\}$ and $B_\infty(x;r)=\{z:\forall i,\ |z_i-x_i|\le r\}$. This is the shared object layer for the explicit partition results of Section 3.2.
--
--   **Formalization Note.** Coordinates and shifts use `Fin d`; dimensions require an explicit proof of positivity. The published `CellPartition`, `IsMSSP` and gauge interfaces are reused. The closed-ball convention is the reading used in the paper's counting proof.
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), Algorithm 1 and Section 3.2, PDF p. 11 / printed p. 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf; SHA-256 1562e70c55d785f992aaa32a161f0b06ac058da62f8f71fb07610037a20bc37b; Section 3.2.2, PDF p. 13 / printed p. 11; Section 2.1, PDF p. 6 / printed p. 4

import Definitions.Def_LowRandomnessDP_KNorm_Geometry

set_option autoImplicit false

noncomputable section

namespace LowRandomnessDP.KNorm.Supplement

/-- Algorithm 1, PDF 11 (printed 9): the sum of fractional parts at shift a/d. -/
def phi {d : ℕ} (x : Vec d) (a : Fin d) : ℝ :=
  ∑ i, Int.fract (x i - (a.val : ℝ) / d)

/-- All minimizing shifts. The order on `Fin d` implements the source's tie-break. -/
def minimizingShifts {d : ℕ} (x : Vec d) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter (fun a => ∀ b, phi x a ≤ phi x b)

private theorem minimizingShifts_nonempty {d : ℕ} (hd : 0 < d) (x : Vec d) :
    (minimizingShifts x).Nonempty := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin d))
    (phi x) ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun b => ha b (Finset.mem_univ _)⟩⟩

/-- The SMALLEST minimizing shift, exactly as in Algorithm 1. -/
def A {d : ℕ} (hd : 0 < d) (x : Vec d) : Fin d :=
  (minimizingShifts x).min' (minimizingShifts_nonempty hd x)

/-- Immediate specification of the finite minimum used in the constructor. -/
theorem A_minimizes {d : ℕ} (hd : 0 < d) (x : Vec d) (b : Fin d) :
    phi x (A hd x) ≤ phi x b := by
  classical
  exact (Finset.mem_filter.mp (Finset.min'_mem _ (minimizingShifts_nonempty hd x))).2 b

/-- The tie-break is by the shift value, not by an arbitrary choice of a minimizer. -/
theorem A_le_of_minimizes {d : ℕ} (hd : 0 < d) (x : Vec d) (a : Fin d)
    (ha : ∀ b, phi x a ≤ phi x b) : A hd x ≤ a := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)

/-- Algorithm 1; integer floor, also for negative coordinates. -/
def R {d : ℕ} (hd : 0 < d) (x : Vec d) : Vec d :=
  fun i => ((A hd x).val : ℝ) / d +
    (Int.floor (x i - ((A hd x).val : ℝ) / d) : ℝ)

/-- The unit body of the coordinate sup norm. -/
def infinityBody (d : ℕ) : Set (Vec d) := {x | ∀ i, |x i| ≤ 1}

/-- Closed coordinate sup-norm ball, including its boundary. -/
def infinityBall {d : ℕ} (x : Vec d) (r : ℝ) : Set (Vec d) :=
  {z | ∀ i, |z i - x i| ≤ r}

/-- Structural constructor obligation: an output of Algorithm 1 represents its own fibre.
The proof uses only the zero fractional parts of a rounded vector and the finite minimum;
no estimate from Lemmas 3.3--3.6 is assumed. -/
private theorem R_idempotent {d : ℕ} (hd : 0 < d) (x : Vec d) :
    R hd (R hd x) = R hd x := by
  have hz : phi (R hd x) (A hd x) = 0 := by
    simp [phi, R, add_sub_cancel_left]
  have hs : phi (R hd x) (A hd (R hd x)) = 0 := by
    apply le_antisymm
    · exact (A_minimizes hd (R hd x) (A hd x)).trans hz.le
    · exact Finset.sum_nonneg (fun i _ => Int.fract_nonneg _)
  funext i
  have hi : Int.fract (R hd x i - ((A hd (R hd x)).val : ℝ) / d) = 0 := by
    have hle := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) =>
        Int.fract_nonneg (R hd x j - ((A hd (R hd x)).val : ℝ) / d))
      (Finset.mem_univ i)
    change Int.fract (R hd x i - ((A hd (R hd x)).val : ℝ) / d) ≤
      phi (R hd x) (A hd (R hd x)) at hle
    exact le_antisymm (hs ▸ hle) (Int.fract_nonneg _)
  change ((A hd (R hd x)).val : ℝ) / d +
    (Int.floor (R hd x i - ((A hd (R hd x)).val : ℝ) / d) : ℝ) = R hd x i
  rw [Int.fract] at hi
  linarith

/-- Nonempty fibres of Algorithm 1, with the rounded output itself as representative.
The representatives are not chosen arbitrarily from the fibre. -/
def inducedPartition {d : ℕ} (hd : 0 < d) : CellPartition d where
  cells := {c | ∃ y ∈ Set.range (R hd), c = {x | R hd x = y}}
  nonempty := by
    rintro c ⟨y, ⟨x, hx⟩, rfl⟩
    exact ⟨x, hx⟩
  covers_uniquely := by
    intro x
    refine ⟨{z | R hd z = R hd x}, ⟨⟨R hd x, ⟨x, rfl⟩, rfl⟩, rfl⟩, ?_⟩
    rintro c ⟨⟨y, _, rfl⟩, hxy⟩
    change R hd x = y at hxy
    rw [hxy]
  representative := fun c => Classical.choose c.property
  representative_mem := by
    intro c
    obtain ⟨⟨x, hx⟩, hc⟩ := Classical.choose_spec c.property
    apply Eq.mpr (congrArg (fun s : Set (Vec d) => Classical.choose c.property ∈ s) hc)
    change R hd (Classical.choose c.property) = Classical.choose c.property
    rw [← hx]
    exact R_idempotent hd x

end LowRandomnessDP.KNorm.Supplement


