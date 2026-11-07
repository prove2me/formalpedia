-- Prove2me | Definitions.Def_RegevRecon_Law
-- name    : RegevRecon_Law
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:53.870204+00:00
-- url     : https://prove2.me/theorems/f39ee820-25f2-4093-ba23-f01083c4b6a8
-- title:
--   Finitely supported laws: point masses, bind, independent draws, expectation
-- statement:
--   A **finitely supported law** on a set $\alpha$ assigns a real mass to finitely many points. The operations are the point mass $\delta_a$; the bind, which draws $a\sim P$ and then samples from $f(a)$; the push-forward; the law $\sum_i w_i\delta_{f(i)}$ of a finite weighted family; the uniform law; the joint law of independent draws; and the expectation $E_P[f]=\sum_a P(a)f(a)$.
--
--   All random vectors of the paper take finitely many values, so two random vectors are equal in distribution, $X\overset d=Y$, exactly when their laws agree as functions. This is a joint statement about whole vectors.
--
--   **Formalization Note** Because expectations are finite sums, no integrability or measurability condition can change a value. A probability law is the separate predicate `Law.IsProb`; the verification file shows the laws of the mission are probability laws on the simplex.
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), §§5, 7, 8, pp.13–14, 18–24

import Mathlib

namespace RegevRecon

/-- **A finitely supported law on `α`**: the mass of each point. All random vectors of Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…),
§§5, 7, 8 (pp.13–14, 18–24) take finitely many values, and this type records their laws exactly.

**Formalization Note** The paper's `=d` between random vectors is equality of `Law`s: the two
vectors have the same mass at every point, jointly in all coordinates, since a point of
`ZMod p → ℝ` is a whole vector. Expectations are finite sums, so no integrability or
measurability side condition can silently change a value. Being a probability law is the separate
predicate `Law.IsProb`; the laws of this mission are probability laws (verification file). -/
abbrev Law (α : Type*) := α →₀ ℝ

namespace Law

variable {α β ι : Type*}

/-- The point mass at `a`. -/
noncomputable def dirac (a : α) : Law α := Finsupp.single a 1

/-- Draw `a ∼ P`, then a sample of `f a`. -/
noncomputable def bind (P : Law α) (f : α → Law β) : Law β := P.sum fun a w => w • f a

/-- The law of `f X` for `X ∼ P`. -/
noncomputable def map (f : α → β) (P : Law α) : Law β := P.bind fun a => dirac (f a)

/-- The law that gives `f i` the mass `w i`, for `i` in a finite index type; a branch of weight
zero contributes nothing, so `f i` is never read there. -/
noncomputable def ofWeights [Fintype ι] (w : ι → ℝ) (f : ι → α) : Law α :=
  ∑ i, Finsupp.single (f i) (w i)

/-- The uniform law on a finite type. -/
noncomputable def uniform (ι : Type*) [Fintype ι] : Law ι :=
  ofWeights (fun _ => ((Fintype.card ι : ℝ))⁻¹) id

/-- The joint law of independent draws from `P 0, …, P (n-1)`. -/
noncomputable def indep : (n : ℕ) → (Fin n → Law α) → Law (Fin n → α)
  | 0, _ => dirac Fin.elim0
  | n + 1, P => (P 0).bind fun a =>
      (indep n fun i => P i.succ).bind fun r => dirac (Fin.cons a r : Fin (n + 1) → α)

/-- The joint law of `n` independent copies of `X ∼ P`. -/
noncomputable def iid (n : ℕ) (P : Law α) : Law (Fin n → α) := indep n fun _ => P

/-- The expectation `E[f X]`, `X ∼ P`. -/
noncomputable def expect (P : Law α) (f : α → ℝ) : ℝ := P.sum fun a w => w * f a

/-- `P` is a probability law: nonnegative masses of total mass `1`. -/
def IsProb (P : Law α) : Prop := (∀ a, 0 ≤ P a) ∧ (P.sum fun _ w => w) = 1

end Law

end RegevRecon


