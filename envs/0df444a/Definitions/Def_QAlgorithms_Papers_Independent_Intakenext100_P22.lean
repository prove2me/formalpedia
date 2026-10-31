-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P22
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P22
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T04:47:37.674773+00:00
-- url     : https://prove2.me/theorems/9dfbed5a-c98e-463a-bd41-e2a937b16b3b
-- title:
--   Definitions for Entanglement entropy of two disjoint intervals in conformal field theory II
-- statement:
--   The objects the formalized statements of *Entanglement entropy of two disjoint intervals in conformal field theory II* (arXiv:1011.5482) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `bilinear`: Bilinear dot product without conjugation, PDF pp. 3–4, (8),(12).
--   - `thetaSummand`: The actual characteristic-theta summand, PDF p. 4, (12).
--   - `characteristicTheta`: Riemann–Siegel theta with complex characteristics, PDF p. 4, (12). On the Siegel domain absolute convergence is part of theta_inversion. The accepted Support21.P18.theta is a qubit antiunitary, a different object.
--   - `Siegel`: Symmetry and positive definite imaginary part, PDF pp. 12–13, (53).
--   - `gaussianFactor`: Holomorphic Gaussian factor det(-iT)^(-1/2), PDF p. 12, (53). The integral fixes the branch continuously from T=iY, Y positive definite, rather than taking the principal scalar square root of the determinant.
--   - `betaRatio`: Hypergeometric ratio, PDF p. 3, (7), on 0<y,x<1.
--   - `periodMatrix`: Computed period data (6)–(7), PDF pp. 2–3; not a physical moment.
--   - `thetaDenominator`: Theta denominator in (68)–(70), PDF pp. 15–16. For this pure imaginary period matrix the theta value is positive real.
--   - `replicaWeight`: Geometric exponent for c=1, PDF p. 16, (71).
--   - `cosineMatrix`: Cosine matrix with source indices shifted to Fin, PDF p. 14, (61).
--   - `cosineQuadratic`: v^t C v in (59)–(64), PDF pp. 14–15.
--   - `exponentA`: Exponent a_v defined independently by the Fourier sum (59), PDF p. 14.
--   - `digammaCombination`: Digamma combination f_y in §5.1, PDF p. 14.
--   - `exponentB`: Amplitude b_v defined independently by (60), PDF p. 14.
--   - `chainValue`: Zero extension m_0=m_n=0 in (62), PDF p. 14.
--   - `chainEnergy`: Domain-wall energy including both endpoints at n=2, PDF p. 14, (62).
--   - `intervalBlock`: Block (a,b] of height h in source coordinates, PDF pp. 15–16, (63),(75). The accepted operator/channel definitions named block are different objects.
--   - `secondPattern`: Explicit second-sector patterns m_0,m_1,m_2 in (85), PDF p. 18.
--   - `halfShift`: Canonical m+ε with ε_i in {0,1/2}, PDF p. 16, (74).
--   - `sheetSine`: Sine of a sheet difference, PDF pp. 18–19, (91)–(93). Subtraction is in ℝ, never truncated in ℕ.
--   - `qFactor`: Q_0,Q_1,Q_2 defined by (91)–(93), PDF pp. 18–19.
--   - `rectangleSum`: Direct finite rectangle sum, PDF p. 18, (86).
--   - `reducedQSum`: Reduced ordered sum with j_1=0, PDF p. 19, (97).
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory II, arXiv:1011.5482v1, https://arxiv.org/abs/1011.5482v1

import Mathlib

/-! Statements from Calabrese–Cardy–Tonni, arXiv:1011.5482v1.
Physical CFT moments are not defined by their proposed answers; see HARD.md.
All new definitions below belong only to this paper. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P22

open scoped BigOperators Topology
open Filter MeasureTheory

/-- Bilinear dot product without conjugation, PDF pp. 3–4, (8),(12). -/
def bilinear {g : ℕ} (v w : Fin g → ℂ) : ℂ := ∑ i, v i * w i

/-- The actual characteristic-theta summand, PDF p. 4, (12). -/
noncomputable def thetaSummand {g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ)
    (a b z : Fin g → ℂ) (m : Fin g → ℤ) : ℂ :=
  Complex.exp (Complex.I * Real.pi *
    bilinear (fun i => (m i : ℂ) + a i) (T.mulVec (fun i => (m i : ℂ) + a i)) +
    2 * Real.pi * Complex.I * bilinear (fun i => (m i : ℂ) + a i) (z + b))

/-- Riemann–Siegel theta with complex characteristics, PDF p. 4, (12).
On the Siegel domain absolute convergence is part of theta_inversion.
The accepted Support21.P18.theta is a qubit antiunitary, a different object. -/
noncomputable def characteristicTheta {g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ)
    (a b z : Fin g → ℂ) : ℂ := ∑' m : Fin g → ℤ, thetaSummand T a b z m

/-- Symmetry and positive definite imaginary part, PDF pp. 12–13, (53). -/
def Siegel {g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ) : Prop :=
  T.transpose = T ∧ Matrix.PosDef (fun i j : Fin g => (T i j).im)

/-- Holomorphic Gaussian factor det(-iT)^(-1/2), PDF p. 12, (53).
The integral fixes the branch continuously from T=iY, Y positive definite,
rather than taking the principal scalar square root of the determinant. -/
noncomputable def gaussianFactor {g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ) : ℂ :=
  ∫ y : Fin g → ℝ, Complex.exp (Complex.I * Real.pi *
    bilinear (fun i => (y i : ℂ)) (T.mulVec (fun i => (y i : ℂ))))

example : bilinear (fun _ : Fin 1 => (2 : ℂ)) (fun _ => 3) = 6 := by
  norm_num [bilinear]

example : thetaSummand (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 0 0 = 1 := by
  simp [thetaSummand, bilinear]

example : gaussianFactor (0 : Matrix (Fin 0) (Fin 0) ℂ) = 1 := by
  have hvolume : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
    simpa using (volume_pi_pi (fun _ : Fin 0 => (Set.univ : Set ℝ)))
  simp [gaussianFactor, bilinear, Measure.real, hvolume]

example : characteristicTheta (0 : Matrix (Fin 0) (Fin 0) ℂ) 0 0 0 = 1 := by
  simp [characteristicTheta, thetaSummand, bilinear]

/-- Hypergeometric ratio, PDF p. 3, (7), on 0<y,x<1. -/
noncomputable def betaRatio (y x : ℝ) : ℝ :=
  ordinaryHypergeometric y (1 - y) (1 : ℝ) (1 - x) /
    ordinaryHypergeometric y (1 - y) (1 : ℝ) x

/-- Computed period data (6)–(7), PDF pp. 2–3; not a physical moment. -/
noncomputable def periodMatrix (n : ℕ) (x : ℝ) :
    Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ :=
  fun r s => 2 * Complex.I / (n : ℂ) *
    ∑ k ∈ Finset.Ico 1 n,
      ((Real.sin (Real.pi * (k : ℝ) / n) * betaRatio ((k : ℝ) / n) x *
        Real.cos (2 * Real.pi * (k : ℝ) / n * ((r.val : ℝ) - s.val)) : ℝ) : ℂ)

/-- Theta denominator in (68)–(70), PDF pp. 15–16.
For this pure imaginary period matrix the theta value is positive real. -/
noncomputable def thetaDenominator (n : ℕ) (x : ℝ) : ℝ :=
  ‖characteristicTheta (periodMatrix n x) 0 0 0‖

/-- Geometric exponent for c=1, PDF p. 16, (71). -/
def replicaWeight (n : ℕ) : ℝ := ((n : ℝ) - 1 / n) / 6

example : periodMatrix 1 (1 / 2) = (0 : Matrix (Fin 0) (Fin 0) ℂ) := by
  ext i
  exact Fin.elim0 i

example : replicaWeight 2 = 1 / 4 := by norm_num [replicaWeight]

example (y : ℝ)
    (h : ordinaryHypergeometric y (1 - y) (1 : ℝ) (1 / 2 : ℝ) ≠ 0) :
    betaRatio y (1 / 2) = 1 := by
  norm_num [betaRatio, h]

/-- Cosine matrix with source indices shifted to Fin, PDF p. 14, (61). -/
noncomputable def cosineMatrix (n k : ℕ) : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ :=
  fun i j => Real.cos (2 * Real.pi * (k : ℝ) / n * ((i.val : ℝ) - j.val))

/-- v^t C v in (59)–(64), PDF pp. 14–15. -/
noncomputable def cosineQuadratic (n k : ℕ) (v : Fin (n - 1) → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * cosineMatrix n k i j * v j

/-- Exponent a_v defined independently by the Fourier sum (59), PDF p. 14. -/
noncomputable def exponentA (n : ℕ) (v : Fin (n - 1) → ℝ) : ℝ :=
  2 / (n : ℝ) * ∑ k ∈ Finset.Ico 1 n,
    Real.sin (Real.pi * (k : ℝ) / n) ^ 2 * cosineQuadratic n k v

/-- Digamma combination f_y in §5.1, PDF p. 14. -/
noncomputable def digammaCombination (y : ℝ) : ℝ :=
  2 * Real.eulerMascheroniConstant +
    (Complex.digamma (y : ℂ)).re + (Complex.digamma ((1 - y : ℝ) : ℂ)).re

/-- Amplitude b_v defined independently by (60), PDF p. 14. -/
noncomputable def exponentB (n : ℕ) (v : Fin (n - 1) → ℝ) : ℝ :=
  2 / (n : ℝ) * ∑ k ∈ Finset.Ico 1 n,
    Real.sin (Real.pi * (k : ℝ) / n) ^ 2 * digammaCombination ((k : ℝ) / n) *
      cosineQuadratic n k v

/-- Zero extension m_0=m_n=0 in (62), PDF p. 14. -/
def chainValue (n : ℕ) (v : Fin (n - 1) → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else if h : j - 1 < n - 1 then v ⟨j - 1, h⟩ else 0

/-- Domain-wall energy including both endpoints at n=2, PDF p. 14, (62). -/
def chainEnergy (n : ℕ) (v : Fin (n - 1) → ℝ) : ℝ :=
  (∑ j ∈ Finset.range n, (chainValue n v (j + 1) - chainValue n v j) ^ 2) / 2

/-- Block (a,b] of height h in source coordinates, PDF pp. 15–16, (63),(75).
The accepted operator/channel definitions named block are different objects. -/
def intervalBlock (n a b : ℕ) (h : ℝ) : Fin (n - 1) → ℝ :=
  fun i => if a < i.val + 1 ∧ i.val + 1 ≤ b then h else 0

/-- Explicit second-sector patterns m_0,m_1,m_2 in (85), PDF p. 18. -/
def secondPattern (n a b c d : ℕ) (s : ℝ) (r : Fin 3) : Fin (n - 1) → ℝ :=
  if r.val = 0 then intervalBlock n a b s + intervalBlock n c d s
  else if r.val = 1 then intervalBlock n a b s - intervalBlock n c d s
  else intervalBlock n a d s + intervalBlock n b c s

/-- Canonical m+ε with ε_i in {0,1/2}, PDF p. 16, (74). -/
def halfShift (n : ℕ) (e : Fin (n - 1) → Bool)
    (m : Fin (n - 1) → ℤ) : Fin (n - 1) → ℝ :=
  fun i => (m i : ℝ) + if e i then (1 / 2 : ℝ) else 0

/-- Sine of a sheet difference, PDF pp. 18–19, (91)–(93).
Subtraction is in ℝ, never truncated in ℕ. -/
noncomputable def sheetSine (n a b : ℕ) : ℝ :=
  Real.sin (Real.pi * ((b : ℝ) - a) / n)

/-- Q_0,Q_1,Q_2 defined by (91)–(93), PDF pp. 18–19. -/
noncomputable def qFactor (n a b c d : ℕ) (r : Fin 3) : ℝ :=
  if r.val = 0 then
    sheetSine n b d * sheetSine n a c /
      (sheetSine n a b * sheetSine n c d * sheetSine n a d * sheetSine n b c)
  else if r.val = 1 then
    sheetSine n a d * sheetSine n b c /
      (sheetSine n a b * sheetSine n c d * sheetSine n b d * sheetSine n a c)
  else
    sheetSine n a b * sheetSine n c d /
      (sheetSine n b d * sheetSine n a c * sheetSine n a d * sheetSine n b c)

example : intervalBlock 2 0 1 (1 : ℝ) = fun _ => 1 := by
  ext i
  simp [intervalBlock, Fin.eq_zero i]

example : chainEnergy 2 (fun _ => (1 : ℝ)) = 1 := by
  norm_num [chainEnergy, chainValue, Finset.sum_range_succ]

example : halfShift 2 (fun _ => true) (fun _ => (0 : ℤ)) = intervalBlock 2 0 1 (1 / 2) := by
  ext i
  simp [halfShift, intervalBlock, Fin.eq_zero i]

example : exponentA 2 (fun _ => (0 : ℝ)) = 0 ∧
    exponentB 2 (fun _ => (0 : ℝ)) = 0 := by
  simp [exponentA, exponentB, cosineQuadratic]

example : secondPattern 4 0 1 2 3 1 0 = intervalBlock 4 0 1 1 + intervalBlock 4 2 3 1 := rfl

example : sheetSine 2 0 1 = 1 := by norm_num [sheetSine]

example : qFactor 4 0 0 1 2 0 = 0 := by simp [qFactor, sheetSine]

/-- Direct finite rectangle sum, PDF p. 18, (86). -/
noncomputable def rectangleSum (n k p lr q lc : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico (p + 1) (p + lr + 1),
    ∑ j ∈ Finset.Ico (q + 1) (q + lc + 1),
      Real.cos (2 * Real.pi * (k : ℝ) / n * ((i : ℝ) - j))

example : rectangleSum 4 1 0 0 0 1 = 0 := by simp [rectangleSum]

example : rectangleSum 4 1 0 1 0 1 = 1 := by norm_num [rectangleSum]

/-- Reduced ordered sum with j_1=0, PDF p. 19, (97). -/
noncomputable def reducedQSum (n : ℕ) (alpha : ℝ) (r : Fin 3) : ℝ :=
  ∑ b ∈ Finset.Ico 1 n, ∑ c ∈ Finset.Ico (b + 1) n,
    ∑ d ∈ Finset.Ico (c + 1) n, Real.rpow (qFactor n 0 b c d r) (2 * alpha)

example : reducedQSum 3 1 1 = 0 := by
  unfold reducedQSum
  apply Finset.sum_eq_zero
  intro b hb
  apply Finset.sum_eq_zero
  intro c hc
  apply Finset.sum_eq_zero
  intro d hd
  have hb_lower := (Finset.mem_Ico.mp hb).1
  have hc_lower := (Finset.mem_Ico.mp hc).1
  have hd_lower := (Finset.mem_Ico.mp hd).1
  have hd_upper := (Finset.mem_Ico.mp hd).2
  omega

end QAlgorithms.Papers.Independent.Intakenext100.P22


