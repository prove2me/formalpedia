-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_LoosenessRigidity
-- name    : KSATSingleFlip_Connect_LoosenessRigidity
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T07:16:52.111632+00:00
-- url     : https://prove2.me/theorems/b2b3559d-72fd-4e13-8ccc-0e66f7e70a30
-- title:
--   Random k-SAT looseness and rigidity geometry
-- statement:
--   These predicates formalize the geometric conclusions of Theorem 1.3. On the low-density side, a common set of solutions of mass at least $1-1/n$ has a logarithmic satisfying flip path reversing every requested variable and a linear-length satisfying path to every solution in a linear-radius Hamming ball. On the high-density side, all but an exponentially small fraction of solutions have at least $(1-\delta)n$ variables whose reversal requires a solution at linear Hamming distance. The definitions do not encode algorithmic constructibility or runtime.
-- source:
--   Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, Theorem 1.3 and density bounds (1.5), printed p. 4 (PDF p. 6), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_Model

noncomputable section
open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- The two density endpoints (1.5), with signed correction ±8(log log k)^2/(log k)^2. -/
def geometryDensity (k : ℕ) (upper : Bool) : ℝ :=
  ((2 : ℝ)^k / k) *
    (Real.log k + Real.log (Real.log k) + 1 +
      (Real.log (Real.log k) + 1/2) / Real.log k +
      (if upper then 8 else -8) * (Real.log (Real.log k))^2 / (Real.log k)^2)

/-- Geometric parts of Theorem 1.3(a,b), with common good solutions.
This predicate does not encode the theorem's algorithmic time guarantees. -/
def HasLooseLocalGeometry {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (radius pathConstant : ℝ) : Prop :=
  0 < numSols Φ ∧
  ∃ S ⊆ sols Φ,
    (1 - 1 / (n : ℝ)) * numSols Φ ≤ (S.card : ℝ) ∧
    ∀ x ∈ S,
      (∀ v : Fin n, ∃ y p, IsSatPath Φ p x y ∧ y v ≠ x v ∧
        (pathLength p : ℝ) ≤ 32 * (Real.log k)^5 * Real.log n) ∧
      (∀ y ∈ sols Φ, (hamming x y : ℝ) ≤ radius * n →
        ∃ p, IsSatPath Φ p x y ∧ (pathLength p : ℝ) ≤ pathConstant * n)

/-- Geometric part of Theorem 1.3(c): on all but an exponentially small
fraction of solutions, at least a (1−δ) fraction of variables are linearly rigid. -/
def HasRigidGeometry {n : ℕ} (Φ : GFormula (Fin n))
    (δ radius rate : ℝ) : Prop :=
  0 < numSols Φ ∧
  ∃ S ⊆ sols Φ,
    (1 - Real.exp (-rate * n)) * numSols Φ ≤ (S.card : ℝ) ∧
    ∀ x ∈ S, ∃ R : Finset (Fin n),
      (1 - δ) * n ≤ (R.card : ℝ) ∧
      ∀ v ∈ R, ∀ y ∈ sols Φ, y v ≠ x v → radius * n ≤ (hamming x y : ℝ)

end KSATSingleFlip.Connect


