-- Prove2me | Definitions.Def_ParityBarrier563_Trilinear_Supplement_FiniteAverages
-- name    : ParityBarrier563_Trilinear_Supplement_FiniteAverages
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:38:56.388201+00:00
-- url     : https://prove2.me/theorems/f5d5f90d-91f5-423e-b089-23c7b9f883e8
-- title:
--   Finite averages and agreement
-- statement:
--   For a finite nonempty sample space A, the uniform mean and probability are
--   $$\mathbb E_A H=|A|^{-1}\sum_{a\in A}H(a),\qquad \Pr_A(E)=\mathbb E_A1_E.$$
--   Agreement is uniform probability of equal Boolean outputs; fixedCount counts fixed coordinates directly; bounded tests have absolute value at most one. The average-case exponent is $n\log_2\log_2 s/(\log_2 s)^{d-1}$ for $n,s\ge2$. These utilities keep all input blocks in the uniform sample space. Means below are used only on nonempty Boolean cubes; the total extension on the empty sample space is zero.
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), §2, printed pp.9–10 / PDF 11–12; Theorems 1.3, 6.4

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Cube
import Definitions.Def_ParityBarrier563_Trilinear_Restriction

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Uniform mean on a finite nonempty sample space; used only on Boolean cubes below. -/
noncomputable def mean {A : Type} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card A

/-- Uniform probability on the same finite sample space. -/
noncomputable def probability {A : Type} [Fintype A] (P : A → Prop) : ℝ :=
  mean (fun a => if P a then 1 else 0)

/-- Agreement under uniform inputs, including all blocks of a multiblock input. -/
noncomputable def agreement {V : Type} [Fintype V] (F G : BoolFn V) : ℝ :=
  probability (fun x => F x = G x)

/-- Number of fixed coordinates (no natural subtraction). -/
def fixedCount {V : Type} [Fintype V] (τ : Restriction V) : ℕ :=
  (Finset.univ.filter fun v => (τ v).isSome).card

/-- A bounded real test function. -/
def BoundedTest {V : Type} (J : RealFn V) : Prop := ∀ x, |J x| ≤ 1

/-- Correlation exponent, with every logarithm base two. Used for n,s ≥ 2. -/
noncomputable def averageExponent (d n : ℕ) (s : ℝ) : ℝ :=
  n * Real.logb 2 (Real.logb 2 s) / (Real.logb 2 s) ^ (d - 1)

end ParityBarrier563.Trilinear.Supplement


