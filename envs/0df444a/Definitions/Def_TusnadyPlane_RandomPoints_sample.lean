-- Prove2me | Definitions.Def_TusnadyPlane_RandomPoints_sample
-- name    : TusnadyPlane_RandomPoints_sample
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:11.641782+00:00
-- url     : https://prove2.me/theorems/c8c7d919-6555-4f53-a473-87003018680e
-- title:
--   Continuous sample law and anchored signed discrepancy
-- statement:
--   A sample consists of $n$ labeled points $P_i=(U_i,V_i)$ in the real plane. A coloring chooses one of the signs $-1,+1$ at every label. The square law is the product of Lebesgue measure restricted to $[0,1]$ in each coordinate, and the sample law is its $n$-fold product. The square has area one, so no additional normalization is needed.
--   $$F_\chi(x,y)=\sum_{i=1}^n\chi_i\mathbf1\{P_i\in[0,x]\times[0,y]\},\qquad D(P,\chi)=\sup_{x,y\in[0,1]}|F_\chi(x,y)|.$$
--   The endpoint average is $a^{[\ell,u]}(y)=(F_\chi(\ell,y)+F_\chi(u,y))/2$. The supremum is over the entire square; its image is nonempty, finite, and bounded by $n$, even with repeated points. These definitions retain the continuous sampling model and all colorings for the goal. Boolean values encode the two signs, and labels are indexed by $\mathrm{Fin}\,n$.
-- source:
--   Zhewei Wei, Tight Bounds for Tusnády’s Problem in the Plane, STOC 2027 submission #313 (October 2026), printed p. 1, 4 (PDF p. 2, 5), §1 main result; §2.1, (2)

import Mathlib

noncomputable section

namespace TusnadyPlane.RandomPoints

abbrev Sample (n : ℕ) := Fin n → ℝ × ℝ
abbrev Coloring (n : ℕ) := Fin n → Bool

def sign (c : Bool) : ℝ := if c then 1 else -1

/-- The area-one square law and its n-fold independent product. §1. -/
def squareLaw : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)).prod
    (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))

instance squareLaw_isProbabilityMeasure : MeasureTheory.IsProbabilityMeasure squareLaw := ⟨by
  rw [squareLaw, ← Set.univ_prod_univ, MeasureTheory.Measure.prod_prod]
  simp⟩

def sampleLaw (n : ℕ) : MeasureTheory.Measure (Sample n) :=
  MeasureTheory.Measure.pi (fun _ : Fin n => squareLaw)

instance sampleLaw_isProbabilityMeasure (n : ℕ) : MeasureTheory.IsProbabilityMeasure (sampleLaw n) := by
  unfold sampleLaw
  infer_instance

/-- Closed anchored rectangle signed count, with labels retained. §1. -/
def signedCount {n : ℕ} (P : Sample n) (χ : Coloring n) (x y : ℝ) : ℝ :=
  ∑ i : Fin n, if (P i).1 ∈ Set.Icc 0 x ∧ (P i).2 ∈ Set.Icc 0 y then sign (χ i) else 0

/-- Full continuum supremum; its nonempty finite range is bounded by n. §1. -/
def discrepancy {n : ℕ} (P : Sample n) (χ : Coloring n) : ℝ :=
  sSup {v : ℝ | ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1,
    v = |signedCount P χ x y|}

/-- Endpoint average (2); exact closed counts even at boundaries. -/
def endpointAverage {n : ℕ} (P : Sample n) (χ : Coloring n) (lo hi y : ℝ) : ℝ :=
  (signedCount P χ lo y + signedCount P χ hi y) / 2

end TusnadyPlane.RandomPoints


