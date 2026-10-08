-- Prove2me | Definitions.Def_KarpPapadimitriou_Generator_Hyperplanes
-- name    : KarpPapadimitriou_Generator_Hyperplanes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:28:14.404931+00:00
-- url     : https://prove2.me/theorems/3dbb8ada-1cc2-4f78-a541-8ea9c7e93128
-- title:
--   The parameter t, small hyperplanes, and Euclidean distance
-- statement:
--   Fix $n\in\mathbb N$, a coefficient-bound exponent $P$, an integer objective $c\in\mathbb Z^n$, and a threshold $k\in\mathbb Z$. The report's bit-length parameter is
--   $$t=(n+1)^2(P+1)+\sum_{i=1}^n\bigl(\lceil\log_2|c_i|\rceil+1\bigr)+\bigl(\lceil\log_2|k|\rceil+1\bigr).$$
--
--   A **small hyperplane** $H=\{x:f\cdot x=g\}$ has nonzero integer normal $f$, and $|f_i|,|g|\le 2^P$. Its point distance is $|f\cdot x-g|/\|f\|_2$. A finite family of hyperplanes is called **affinely independent** here when its normal vectors are linearly independent over $\mathbb R$; its flat is their common solution set.
--
--   These objects make the quantitative separation and projection lemmas on pp. 12–13 precise.
--
--   **Formalization Note** For a zero coefficient, $\lceil\log_2|0|\rceil$ is read as zero; negative coefficients use absolute values. Lean uses $\operatorname{clog}_2$ on natural absolute values. Rational points are cast into $\mathrm{EuclideanSpace}\,\mathbb R\,(\mathrm{Fin}\ n)$ for distance, and distance to a flat uses the Euclidean metric infimum distance. The nonzero normal excludes division by zero.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), pp. 10–13, t, Lemma 4, Corollary, Lemma 5

import Mathlib
import Definitions.Def_KarpPapadimitriou_Generator_COP

namespace KarpPapadimitriou.Generator

/-- The paper's `t` for fixed dimension, smallness exponent value, objective and threshold.
At zero and negative coefficients, the ceiling logarithm is read as that of the absolute value,
with `clog 2 0 = 0`. -/
def tParam (n P : ℕ) (c : Fin n → ℤ) (k : ℤ) : ℕ :=
  (n + 1) ^ 2 * (P + 1) +
    (∑ i : Fin n, (Nat.clog 2 (c i).natAbs + 1)) +
    (Nat.clog 2 k.natAbs + 1)

/-- An integer hyperplane with nonzero normal and coefficients bounded by `2^P`. -/
def SmallHyperplane {n : ℕ} (P : ℕ) (f : Fin n → ℤ) (g : ℤ) : Prop :=
  f ≠ 0 ∧ (∀ i, (f i).natAbs ≤ 2 ^ P) ∧ g.natAbs ≤ 2 ^ P

/-- The real Euclidean normal length of an integer hyperplane. -/
noncomputable def normalLength {n : ℕ} (f : Fin n → ℤ) : ℝ :=
  Real.sqrt (∑ i : Fin n, ((f i : ℝ) ^ 2))

/-- The real dot product with an integer normal. -/
def dotR {n : ℕ} (f : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, (f i : ℝ) * x i

/-- The real Euclidean hyperplane with integer normal and constant. -/
def hyperplane {n : ℕ} (f : Fin n → ℤ) (g : ℤ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | dotR f x = (g : ℝ)}

/-- Distance to a nondegenerate hyperplane, expressed by the standard quotient formula. -/
noncomputable def hyperplaneDistance {n : ℕ} (f : Fin n → ℤ) (g : ℤ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  |dotR f x - (g : ℝ)| / normalLength f

/-- A rational point viewed in real Euclidean space. -/
def realPoint {n : ℕ} (x : Fin n → ℚ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => (x i : ℝ))

/-- A finite family of hyperplanes is affinely independent when its normal vectors are linearly
independent over the reals. -/
def IndependentNormals {n m : ℕ} (H : Fin m → (Fin n → ℤ) × ℤ) : Prop :=
  LinearIndependent ℝ (fun i : Fin m => (fun j : Fin n => ((H i).1 j : ℝ)))

/-- The simultaneous solution set of a family of real hyperplane equations. -/
def flat {n m : ℕ} (H : Fin m → (Fin n → ℤ) × ℤ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, x ∈ hyperplane (H i).1 (H i).2}

end KarpPapadimitriou.Generator


