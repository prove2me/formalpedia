-- Prove2me | Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Model
-- name    : PrivateAgnosticHalfspace_Gaussian_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T11:22:23.776566+00:00
-- url     : https://prove2.me/theorems/e86cba22-8102-46fa-a51d-90aff3757938
-- title:
--   Gaussian labeled examples, Hermite features and Algorithm 1
-- statement:
--   An example is a vector $x\in\mathbb R^d$ and a label $y\in\{-1,1\}$. Coordinates have their Euclidean norm and Borel sigma algebra. A halfspace is $x\mapsto\operatorname{sign}(\langle w,x\rangle+t)$, allowing $w=0$ and every real $t$. The sign at zero is $+1$. For a probability law $P$, write $\operatorname{err}_P(h)=P[h(X)\ne Y]$ and $\mathrm{OPT}=\inf_{w,t}\operatorname{err}_P(h_{w,t})$.
--
--   The tensor Hermite polynomial is $h_\kappa(x)=\prod_i h_{\kappa_i}(x_i)$, using the referenced normalized univariate Hermites. The cutoff includes each multi-index of degree at most $p$ exactly once. With $D_p=\binom{d+p}{p}$ and $T=2\sqrt{D_p}$, set
--   $$
--   \psi_p(x)=(h_\kappa(x))_{|\kappa|\le p},\qquad
--   \bar\psi_p(x)=\frac{T}{\max\{T,\|\psi_p(x)\|_2\}}\psi_p(x).
--   $$
--   The coefficient domain is the closed unit ball. Population and empirical objectives are absolute losses. Equations (14a)–(14c) define the public degree, training repetitions, grid size, least admissible training-block size and validation size. The sample law is the actual product of the training output laws, followed by exponential weights on the ordered validation block. Each candidate pair retains its multiplicity, and the output stores its coefficient vector and threshold index.
--
--   These definitions specify the learner without giving it a population distribution. Probability normalization and measurability of its output law are theorem conclusions, rather than an unchecked interpretation of a total measure operation.
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, STOC 2027 submission #1006 (October 2026), p. 3–5, 21–22, 25–26, notation, Algorithm 1, Definition B.2, Lemma B.8, Eqs. (4), (14a)–(14c); canonical PDF sha256 f0122a33e29daa624b530bdd0b071998d8e44197b30449b0cb3213289645cec7

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_AMPLowDeg_RankOne_Cumulant

open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian

/-- Euclidean coordinates, with their Euclidean norm and Borel sigma algebra. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Example (d : ℕ) := Vec d × Bool

def label (y : Bool) : ℝ := if y then 1 else -1
noncomputable def sign (z : ℝ) : Bool := decide (0 ≤ z)
noncomputable def affine (d : ℕ) (w : Vec d) (t : ℝ) (x : Vec d) : Bool :=
  sign (inner ℝ w x + t)
noncomputable def gaussian (d : ℕ) : Measure (Vec d) := stdGaussian (Vec d)

noncomputable def error {X : Type*} [MeasurableSpace X]
    (P : Measure (X × Bool)) (h : X → Bool) : ℝ := P.real {z | h z.1 ≠ z.2}
noncomputable def opt (d : ℕ) (P : Measure (Example d)) : ℝ :=
  sInf (Set.range fun wt : Vec d × ℝ => error P (affine d wt.1 wt.2))
noncomputable def empiricalError {X : Type*} {n : ℕ}
    (S : Fin n → X × Bool) (h : X → Bool) : ℝ :=
  (∑ i, if h (S i).1 = (S i).2 then (0 : ℝ) else 1) / n

/-- All natural multi-indices, and their normalized tensor Hermite polynomials. -/
noncomputable def hermite (d : ℕ) (κ : Fin d → ℕ) (x : Vec d) : ℝ :=
  ∏ i, AMPLowDeg.RankOne.hermNorm (κ i) (x i)
def degree {d : ℕ} (κ : Fin d → ℕ) : ℕ := ∑ i, κ i

/-- A finite enumeration without duplicates, including the constant polynomial. -/
abbrev Index (d p : ℕ) := {κ : Fin d → Fin (p + 1) // ∑ i, (κ i).val ≤ p}
abbrev Coeff (d p : ℕ) := EuclideanSpace ℝ (Index d p)
abbrev UnitBall (d p : ℕ) := {v : Coeff d p // ‖v‖ ≤ 1}

def featureDimension (d p : ℕ) : ℕ := (d + p).choose p
noncomputable def features (d p : ℕ) (x : Vec d) : Coeff d p :=
  WithLp.toLp 2 (fun κ => hermite d (fun i => (κ.val i).val) x)
noncomputable def radius (d p : ℕ) : ℝ := 2 * Real.sqrt (featureDimension d p)
noncomputable def clipScale (d p : ℕ) (x : Vec d) : ℝ :=
  radius d p / max (radius d p) ‖features d p x‖
noncomputable def clipped (d p : ℕ) (x : Vec d) : Coeff d p :=
  clipScale d p x • features d p x
noncomputable def score (d p : ℕ) (v : Coeff d p) (x : Vec d) : ℝ :=
  inner ℝ v (clipped d p x)
noncomputable def candidate (d p : ℕ) (M : ℕ) (v : Coeff d p) (l : Fin M)
    (x : Vec d) : Bool := sign (score d p v x - (-1 + (2 * (l.val : ℝ) + 1) / M))
noncomputable def populationLoss (d p : ℕ) (P : Measure (Example d)) (v : Coeff d p) : ℝ :=
  ∫ z, |score d p v z.1 - label z.2| ∂P
noncomputable def empiricalLoss (d p : ℕ) {n : ℕ} (S : Fin n → Example d)
    (v : Coeff d p) : ℝ := (∑ i, |score d p v (S i).1 - label (S i).2|) / n
noncomputable def minimumLoss (d p : ℕ) (P : Measure (Example d)) : ℝ :=
  sInf (populationLoss d p P '' Metric.closedBall 0 1)

/-- Public parameter schedule (14a)--(14c). The minimization is over integers at least two;
`Nat.find` is used only when the defining set is nonempty. The goal asserts its existence. -/
noncomputable def scheduledDegree (C α : ℝ) : ℕ := ⌈C / α ^ 2⌉₊
noncomputable def repetitions (β : ℝ) : ℕ := ⌈Real.log (2 / β) / Real.log 2⌉₊
noncomputable def thresholds (C α : ℝ) : ℕ := ⌈C / α⌉₊
noncomputable def blockCondition (C c α ε δ : ℝ) (d p n : ℕ) : Prop :=
  2 ≤ n ∧ C * (radius d p * Real.sqrt ((featureDimension d p : ℝ) * Real.log (1 / δ)) /
    (ε * n) + Real.sqrt ((featureDimension d p : ℝ) / n)) ≤ c * α
noncomputable def trainingSize (C c α ε δ : ℝ) (d p : ℕ) : ℕ :=
  by
    classical
    exact if h : ∃ n, blockCondition C c α ε δ d p n then Nat.find h else 0
noncomputable def validationSize (C α β ε : ℝ) (k M : ℕ) : ℕ :=
  ⌈C * (α⁻¹ ^ 2 + (ε * α)⁻¹) * Real.log ((k : ℝ) * M / β)⌉₊

/-- Finite exponential weights preserve the indexed list, including duplicates. -/
noncomputable def validationLaw {X : Type*} {K m : ℕ}
    (h : Fin K → X → Bool) (ε : ℝ) (S : Fin m → X × Bool) : Measure (Fin K) :=
  let w := fun j => Real.exp (-ε * m * empiricalError S (h j) / 2)
  ∑ j, ENNReal.ofReal (w j / ∑ i, w i) • Measure.dirac j

/-- An optimizer is sample-only; no population or success predicate occurs in this type. -/
abbrev Optimizer := ∀ d p n : ℕ, ℝ → ℝ → (Fin n → Example d) → ProbabilityMeasure (UnitBall d p)

/-- Algorithm 1 output is a selected coefficient vector and threshold index. -/
abbrev Output (d p M : ℕ) := UnitBall d p × Fin M
noncomputable def decode (d p M : ℕ) (o : Output d p M) : Vec d → Bool :=
  candidate d p M o.1.val o.2

/-- The exact sample-only law of Algorithm 1 with disjoint public blocks and independent coins.
The theorem requires this measure to equal a probability mechanism for every deterministic input. -/
noncomputable def algorithmLaw (O : Optimizer) (d p k M n₀ m : ℕ) (ε δ : ℝ)
    (S : Fin (k * n₀ + m) → Example d) : Measure (Output d p M) :=
  let blocks : Fin k → Fin n₀ → Example d := fun j i =>
    S ⟨j.val * n₀ + i.val, by
      have hj := Nat.mul_le_mul_right n₀ (Nat.succ_le_of_lt j.isLt)
      have hi := i.isLt
      nlinarith⟩
  let val : Fin m → Example d := fun i => S ⟨k * n₀ + i.val, by omega⟩
  let train := Measure.pi (fun j : Fin k => (O d p n₀ ε δ (blocks j) : Measure (UnitBall d p)))
  train.bind fun v =>
    let w := fun jl : Fin k × Fin M =>
      Real.exp (-ε * m * empiricalError val (candidate d p M (v jl.1).val jl.2) / 2)
    ∑ jl : Fin k × Fin M,
      ENNReal.ofReal (w jl / ∑ il : Fin k × Fin M, w il) • Measure.dirac (v jl.1, jl.2)

end PrivateAgnosticHalfspace.Gaussian


