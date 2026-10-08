-- Prove2me | Definitions.Def_BernoulliNonflatInSeven
-- name    : BernoulliNonflatInSeven
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:01.532433+00:00
-- url     : https://prove2.me/theorems/3c1fdd3f-beb1-409f-b6bd-ff8ef9dcb056
-- statement:
--   For each nonnegative integer d, Space(d) is real Euclidean d-space, with Lebesgue measure. A test function on a set D is a globally smooth real function with compact support contained in D. A vector field G is a weak gradient of u on D if, for every such test function φ and every constant vector h, ∫_D u(x)Dφ(x)[h] dx = −∫_D ⟨G(x),h⟩φ(x) dx. The condition H¹(D;u,G) additionally requires u and G to be square-integrable. The condition H¹₀(D;u,G) requires H¹ membership and approximation by test functions whose L² errors in both function value and gradient are smaller than every prescribed positive ε. Local H¹ membership requires H¹ membership on every positive-radius open ball whose closed ball lies in D. The Bernoulli energy is E_D(u,G)=∫_D (‖G(x)‖²+1_{u(x)>0}) dx. A local minimizer is a function on an open set D admitting a locally H¹ weak gradient G, nonnegative almost everywhere on D, such that E_B(u,G)≤E_B(v,V) on every such ball B whenever v is nonnegative almost everywhere, (v,V) belongs to H¹(B), and (v−u,V−G) belongs to H¹₀(B). Competitors may be arbitrary Sobolev representatives. A global minimizer satisfies this condition on the whole space. One-homogeneity means that, for every r>0, u(rx)=ru(x) for almost every x; nonzero means u is not almost everywhere zero. Flatness means that some unit vector e satisfies u(x)=max(⟨x,e⟩,0) almost everywhere. These are definitions; no existence assertion is included.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BernoulliNonflatInSeven.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BernoulliNonflatInSeven.lean; bytes 16..3300
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace Bernoulli
open scoped _root_.Bernoulli

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Compactly supported smooth real tests in the open set. -/
def Test {d : ℕ} (D : Set (Space d)) (φ : Space d → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ D

/-- Distributional gradient, tested in every constant direction. -/
def WeakGradient {d : ℕ} (D : Set (Space d))
    (u : Space d → ℝ) (G : Space d → Space d) : Prop :=
  ∀ φ, Test D φ → ∀ h : Space d,
    (∫ x in D, u x * (fderiv ℝ φ x) h) =
      -(∫ x in D, inner ℝ (G x) h * φ x)

/-- H¹(D), with its weak gradient. -/
def H1 {d : ℕ} (D : Set (Space d))
    (u : Space d → ℝ) (G : Space d → Space d) : Prop :=
  MemLp u 2 (volume.restrict D) ∧
  MemLp G 2 (volume.restrict D) ∧ WeakGradient D u G

/-- H¹₀(D) is H¹-closure of C∞ compactly supported functions.
Both L² errors tend to zero. This does not restrict competitors to smooth ones. -/
def H10 {d : ℕ} (D : Set (Space d))
    (u : Space d → ℝ) (G : Space d → Space d) : Prop :=
  H1 D u G ∧ ∀ ε : ℝ, 0 < ε → ∃ φ : Space d → ℝ,
    Test D φ ∧
    eLpNorm (fun x => u x - φ x) 2 (volume.restrict D) < ENNReal.ofReal ε ∧
    eLpNorm (fun x => G x - gradient φ x) 2 (volume.restrict D) < ENNReal.ofReal ε

/-- Ballwise H¹_loc, on an open set (balls have compact closure inside D). -/
def H1Loc {d : ℕ} (D : Set (Space d))
    (u : Space d → ℝ) (G : Space d → Space d) : Prop :=
  ∀ c : Space d, ∀ r : ℝ, 0 < r → Metric.closedBall c r ⊆ D →
    H1 (Metric.ball c r) u G

/-- The exact volume-one Bernoulli energy, not just Dirichlet energy. -/
def energy {d : ℕ} (D : Set (Space d))
    (u : Space d → ℝ) (G : Space d → Space d) : ℝ :=
  ∫ x in D, ‖G x‖ ^ 2 + if 0 < u x then (1 : ℝ) else 0

/-- Full ballwise local comparison. Competitor and gradient are arbitrary
Sobolev representatives on the ball, with zero-trace difference. -/
def LocalMinimizer {d : ℕ} (D : Set (Space d)) (u : Space d → ℝ) : Prop :=
  IsOpen D ∧ ∃ G : Space d → Space d,
    H1Loc D u G ∧ (∀ᵐ x ∂volume.restrict D, 0 ≤ u x) ∧
    ∀ c : Space d, ∀ r : ℝ, 0 < r → Metric.closedBall c r ⊆ D →
      ∀ (v : Space d → ℝ) (V : Space d → Space d),
        H1 (Metric.ball c r) v V →
        (∀ᵐ x ∂volume.restrict (Metric.ball c r), 0 ≤ v x) →
        H10 (Metric.ball c r) (fun x => v x - u x) (fun x => V x - G x) →
        energy (Metric.ball c r) u G ≤ energy (Metric.ball c r) v V

/-- Nonnegative global minimizer, with all centers and all positive radii. -/
def GlobalMinimizer {d : ℕ} (u : Space d → ℝ) : Prop :=
  LocalMinimizer Set.univ u

def OneHomogeneous {d : ℕ} (u : Space d → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ᵐ x ∂volume, u (r • x) = r * u x

def Nonzero {d : ℕ} (u : Space d → ℝ) : Prop :=
  ¬ (u =ᵐ[volume] fun _ => 0)

/-- Flatness is a.e. equality of H¹ representatives. -/
def Flat {d : ℕ} (u : Space d → ℝ) : Prop :=
  ∃ e : Space d, ‖e‖ = 1 ∧ ∀ᵐ x ∂volume, u x = max (inner ℝ x e) 0



end Bernoulli
end
end OAI


