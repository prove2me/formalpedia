-- Prove2me | Definitions.Def_RandomDimReduction_Channel_Supplement_SubalgebraCP
-- name    : RandomDimReduction_Channel_Supplement_SubalgebraCP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:39:57.206575+00:00
-- url     : https://prove2.me/theorems/9f5b39b7-03ab-4ca2-bef6-18436b76770d
-- title:
--   Inherited matrix positivity on a subalgebra of bounded operators
-- statement:
--   Let $H$ be any complex Hilbert space and $S$ a complex subalgebra of the bounded operators on $H$. A finite operator block matrix $[X_{ij}]$ is positive when $X_{ij}^\dagger=X_{ji}$ and
--   $$\operatorname{Re}\sum_{i,j}\langle v_i,X_{ij}v_j\rangle\ge0\quad\text{for every }(v_i)\in H^r.$$
--   A complex-linear map $f:S\to L(H)$ is completely positive for the inherited matrix order when entrywise application of $f$ preserves this cone for every finite size $r$. Left multiplication is the actual complex-linear map $X\mapsto AX$; its definition assumes neither positivity of $A$ nor commutation with $S$.
--
--   This is the full amplification condition needed in Lemma 3.2. It allows infinite-dimensional $H$ and does not require $S$ to be commutative, norm closed or star closed, or require $A$ to belong to $S$.
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf, Lemma 3.2, p.9

import Mathlib

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace

namespace RandomDimReduction.Channel.Supplement

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The inherited positive cone of finite operator block matrices on the Hilbert direct sum H^r.
Self-adjointness and nonnegative quadratic form are imposed in the ambient bounded operators. -/
def PositiveOperatorBlock {r : ℕ} (X : Matrix (Fin r) (Fin r) (H →L[ℂ] H)) : Prop :=
  (∀ i j, (X i j).adjoint = X j i) ∧
    ∀ v : Fin r → H, 0 ≤ (∑ i, ∑ j, inner ℂ (v i) (X i j (v j))).re

/-- Complete positivity on an arbitrary (not necessarily star-closed) complex subalgebra,
with the inherited matrix order, at every finite amplification. -/
def CompletelyPositiveOn (S : NonUnitalSubalgebra ℂ (H →L[ℂ] H))
    (f : S →ₗ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∀ (r : ℕ) (X : Matrix (Fin r) (Fin r) S),
    PositiveOperatorBlock (fun i j => (X i j : H →L[ℂ] H)) →
      PositiveOperatorBlock (fun i j => f (X i j))

/-- Literal left multiplication; A need not belong to S. -/
def leftMultiplication (S : NonUnitalSubalgebra ℂ (H →L[ℂ] H)) (A : H →L[ℂ] H) :
    S →ₗ[ℂ] (H →L[ℂ] H) where
  toFun X := A * (X : H →L[ℂ] H)
  map_add' X Y := by simp [mul_add]
  map_smul' c X := by simp

end RandomDimReduction.Channel.Supplement


