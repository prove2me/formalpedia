-- Prove2me | Definitions.Def_MetricTesting_Characterization_Supplement_bit_size
-- name    : MetricTesting_Characterization_Supplement_bit_size
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:19:36.640792+00:00
-- url     : https://prove2.me/theorems/33668d0d-ebfb-46d6-ab93-5cf54153f860
-- title:
--   Rational bit size and designated robust metric faces
-- statement:
--   For a reduced rational number $x$, let its binary size be the larger of the bit lengths of its numerator magnitude and positive denominator; zero uses one bit. An array has bit bound $B$ at order $n$ when every entry is rational and
--
--   $$\operatorname{bits}(x)\le B\bigl(1+\lceil\log_2 n\rceil\bigr).$$
--
--   A robust face consists of a metric array in $[1,C_0]$, an edge-disjoint family of three-element label sets and one designated long edge for each selected triangle. The designated inequalities are exactly its tight inequalities. Every other triangle slack and every entry's distance from either endpoint is at least $n^{-3}$. A slack is the sum of the two short distances minus the designated long distance.
--
--   These predicates express the numerical and geometric conclusions required of a robust-face witness. They impose no testing or obstruction conclusion and do not restrict the real-valued upper-bound input model.
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), Lemma 4.10, printed pp. 16–17 (PDF pp. 17–18); §6.2–6.5, printed pp. 27–31 (PDF pp. 28–32)

import Mathlib
import Definitions.Def_MetricTesting_Characterization_Supplement_geometry

set_option autoImplicit false
noncomputable section

namespace MetricTesting.Characterization.Supplement

/-- Binary lengths of the reduced numerator and denominator, with one bit for zero. -/
def rationalBits (x : ℚ) : ℕ :=
  max (Nat.log2 x.num.natAbs + 1) (Nat.log2 x.den + 1)

def logSize (n : ℕ) : ℕ := 1 + ⌈Real.log (n : ℝ) / Real.log 2⌉₊

def SmallRational {Λ : Set NNReal} {n : ℕ} (B : ℕ) (D : Array Λ n) : Prop :=
  ∀ e, ∃ x : ℚ, (x : ℝ) = (D e : NNReal) ∧ rationalBits x ≤ B * logSize n

/-- A tight inequality is indexed by its long unordered edge and its third vertex. -/
def triangleSlack {Λ : Set NNReal} {n : ℕ} (D : Array Λ n)
    (e : Edge n) (v : Fin n) : ℝ :=
  (∑ i ∈ e.1, entry D i v) - ((D e : NNReal) : ℝ)

/-- A designated family has exactly one long edge for each of its triangles. -/
def RobustFace {n : ℕ} (C₀ : ℚ) (D : Array (BoundedValues (C₀ : ℝ)) n)
    (H : Finset (Finset (Fin n))) : Prop :=
  Triangle D ∧ EdgeDisjoint H ∧ (∀ S ∈ H, S.card = 3) ∧
  ∃ long : (S : Finset (Fin n)) → Edge n,
    (∀ S ∈ H, (long S).1 ⊆ S) ∧
    (∀ (e : Edge n) (v : Fin n), v ∉ e.1 →
      (triangleSlack D e v = 0 ↔ ∃ S ∈ H, S = insert v e.1 ∧ long S = e)) ∧
    (∀ (e : Edge n) (v : Fin n), v ∉ e.1 →
      triangleSlack D e v ≠ 0 → (n : ℝ)⁻¹^3 ≤ triangleSlack D e v) ∧
    ∀ e, (n : ℝ)⁻¹^3 ≤ ((D e : NNReal) : ℝ) - 1 ∧
      (n : ℝ)⁻¹^3 ≤ (C₀ : ℝ) - ((D e : NNReal) : ℝ)

end MetricTesting.Characterization.Supplement


