-- Prove2me | Definitions.Def_SkutellaCQP_MaxSNP_Supplement_Hyperplane
-- name    : SkutellaCQP_MaxSNP_Supplement_Hyperplane
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:46:56.039342+00:00
-- url     : https://prove2.me/theorems/51365466-4e0c-41ee-be67-d8ddc81af975
-- title:
--   §5 — actual hyperplane rounding, f₂, Conjecture 5.3 and precision
-- statement:
--   A normal is drawn from the published uniform probability measure on the sphere of $\mathbb R^{n+1}$. A job goes to machine 0 when its vector and the machine-0 vector have the same sign of inner product with the normal, and otherwise to machine $-1$. All jobs use the same normal, so the resulting joint law retains their correlations. A fixed tie convention only affects null events.
--
--   For $\theta\in[0,\pi]$, define
--   $$\xi(\theta)=\min\{\pi,\max\{0,\pi/2+1.3662(\theta-\pi/2)\}\},\qquad f_2(\theta)=\frac\pi2(1-\cos\xi(\theta)).$$
--   Only job vectors are modified. Their polar angle to $v_0$ becomes $f_2(\theta)$, preserving the normalized transverse direction; the two collinear endpoints stay fixed. Conjecture 5.3 is the precise proposition that this constructed law satisfies (34)–(35) for every feasible SDP solution, with $\rho_1=1.1847$ and $\rho_2=1.3388$. It is defined without being asserted.
--
--   The module also constructs independent rounding and the choice of the two computable upper bounds. Sufficient tolerances are $\delta_{54}=3(\rho_2-\rho_1)L/(8\rho_2)$ and $\delta_{55}=(1.2752-q)L/(2q)$, where $q=31399/24623$. They specify the paper's “almost optimal” without replacing it by exact optimality. Both are zero for zero-weight instances, where a zero SDP objective is feasible and every schedule has value zero.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), DOI 10.1145/375827.375840, pp. 25–29, RANDOM HYPERPLANE, f₂, Conjecture 5.3 and Theorems 5.4–5.5

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Supplement_SDP
import Definitions.Def_RegretBandits_Nonlinear_Smoothing

namespace SkutellaCQP.MaxSNP.Supplement

open MeasureTheory Finset
open scoped RealInnerProductSpace

/-- The clipped angle of p. 28; 1.3662 is an exact rational. -/
noncomputable def xi (θ : ℝ) : ℝ :=
  min Real.pi (max 0 (Real.pi / 2 + (6831 / 5000 : ℝ) * (θ - Real.pi / 2)))

/-- The modification `f₂ = f₁ ∘ ξ`, pp. 27–28. -/
noncomputable def f₂ (θ : ℝ) : ℝ := Real.pi * (1 - Real.cos (xi θ)) / 2

/-- Modify a job in its plane with the machine-0 vector, preserving the normalized
transverse direction. The collinear endpoints stay fixed, avoiding division by zero. -/
noncomputable def modifiedJob {n : ℕ} (v : Vectors n) (j : Fin n) : Vec n :=
  let c := ⟪v.machine 0, v.job j⟫
  let transverse := v.job j - c • v.machine 0
  let θ := Real.arccos c
  if ‖transverse‖ = 0 then v.job j
  else Real.cos (f₂ θ) • v.machine 0 +
    (Real.sin (f₂ θ) / ‖transverse‖) • transverse

/-- Only job vectors are modified; the two antipodal machine vectors are unchanged. -/
noncomputable def modified {n : ℕ} (v : Vectors n) : Vectors n :=
  ⟨v.machine, modifiedJob v⟩

/-- RANDOM HYPERPLANE, p. 25: same sign as machine 0 means machine 0.
The deterministic tie convention affects a null set for feasible vectors. -/
noncomputable def hyperplaneAssignment {n : ℕ} (v : Vectors n) (r : Vec n) : Fin n → Two :=
  fun j => if (0 ≤ ⟪v.job j, r⟫ ↔ 0 ≤ ⟪v.machine 0, r⟫) then 0 else 1

/-- The actual joint assignment law induced by one uniform sphere normal, not independently
specified marginal or pairwise probabilities. Events are Borel sign regions. -/
noncomputable def hyperplaneLaw {n : ℕ} (v : Vectors n) (σ : Fin n → Two) : ℝ :=
  ((RegretBandits.Nonlinear.uniformSphere (n + 1))
    {r | hyperplaneAssignment v r = σ}).toReal

/-- The `f₂`-modified hyperplane law. -/
noncomputable def modifiedLaw {n : ℕ} (v : Vectors n) : (Fin n → Two) → ℝ :=
  hyperplaneLaw (modified v)

/-- Independent rounding, a particular implementation of the paper's pairwise-independent
algorithm. All assignment probabilities are constructed from (30). -/
noncomputable def independentLaw {n : ℕ} (v : Vectors n) (σ : Fin n → Two) : ℝ :=
  ∏ j, assignment v (σ j) j

/-- Conjecture 5.3 as a concrete assertion about `f₂` and its actual hyperplane law.
This is a premise of Theorems 5.4 and 5.5, never an axiom or an asserted theorem. -/
def Conjecture53 : Prop :=
  ∀ (n : ℕ) (p : Two → Fin n → ℝ) (w : Fin n → ℝ),
    (∀ i j, 0 < p i j) → (∀ j, 0 ≤ w j) →
    ∀ (v : Vectors n) (Z : ℝ), SDPFeasible p w v Z →
    ProbabilityBounds v (modifiedLaw v) (11847 / 10000) (3347 / 2500)

/-- A sufficient additive SDP tolerance for Theorem 5.4; zero weights require no optimization. -/
noncomputable def tolerance54 {n : ℕ} (p : Two → Fin n → ℝ) (w : Fin n → ℝ) : ℝ :=
  (3 / 8 : ℝ) * ((3347 / 2500 : ℝ) - (11847 / 10000 : ℝ)) * lowerBound p w /
    (3347 / 2500 : ℝ)

/-- Crossing value of the two affine performance bounds on p. 29. -/
noncomputable def crossingValue : ℝ := 31399 / 24623

/-- A sufficient additive tolerance absorbing the strict slack below 1.2752. -/
noncomputable def tolerance55 {n : ℕ} (p : Two → Fin n → ℝ) (w : Fin n → ℝ) : ℝ :=
  ((797 / 625 : ℝ) - crossingValue) * lowerBound p w / (2 * crossingValue)

/-- Compare the two computable upper bounds, avoiding the quotient `cᵀa/Z` at `Z=0`. -/
noncomputable def chooseIndependent {n : ℕ} (p : Two → Fin n → ℝ) (w : Fin n → ℝ)
    (v : Vectors n) (Z : ℝ) : Prop :=
  Z + linearValue p w v / 2 ≤
    (11847 / 10000 : ℝ) * (3 * linearValue p w v / 4) +
    (3347 / 2500 : ℝ) * (Z - 3 * linearValue p w v / 4)

/-- The p. 29 choice uses only the two upper bounds, not the true optimum. -/
noncomputable def selectedLaw {n : ℕ} (p : Two → Fin n → ℝ) (w : Fin n → ℝ)
    (v : Vectors n) (Z : ℝ) : (Fin n → Two) → ℝ :=
  by
    classical
    exact if chooseIndependent p w v Z then independentLaw v else modifiedLaw v

end SkutellaCQP.MaxSNP.Supplement


