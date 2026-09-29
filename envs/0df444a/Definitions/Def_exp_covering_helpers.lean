-- Prove2me | Definitions.Def_exp_covering_helpers
-- name    : exp_covering_helpers
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-28T08:23:32.245987+00:00
-- url     : https://prove2.me/theorems/5b87e3e8-48d7-4f96-ae99-7ee332999a3a
-- title:
--   Helpers for the exponential covering of the punctured complex plane
-- statement:
--   Auxiliary constants for the universal cover $z \mapsto e^z$ of the punctured complex plane $\mathbb{C}\setminus\{0\}$: the point $0$ of the fibre over the basepoint $1$ (used as the basepoint of the covering space), the basepoint $1$ itself, and the loop $t \mapsto e^{2\pi i t}$, which traces the unit circle once counterclockwise.
-- source:
--   Standard model of the universal covering $\exp : \mathbb{C} \to \mathbb{C}\setminus\{0\}$.

import Mathlib

namespace BraidsLinksMCG

/-- The point `0` of the fibre of `Complex.exp` over the basepoint `1` of
`{z : ℂ // z ≠ 0}`, since `Complex.exp 0 = 1`. -/
def expFibreBase :
    (fun z : ℂ ↦ (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ⁻¹'
      {(⟨1, by norm_num⟩ : {z : ℂ // z ≠ 0})} :=
  ⟨(0 : ℂ), by simp [Complex.exp_zero]⟩

/-- The basepoint `1` in the punctured complex plane `{z : ℂ // z ≠ 0}`. -/
def expBase : {z : ℂ // z ≠ 0} := ⟨1, by norm_num⟩

/-- The counterclockwise circle of radius `1` about the origin, traced once, based
at `1`; it is the image under `Complex.exp` of the straight segment from `0` to
`2 * Real.pi * Complex.I`. -/
noncomputable def expWindingLoop : Path expBase expBase :=
  ⟨⟨fun t => (⟨Complex.exp (2 * Real.pi * (t : ℝ) * Complex.I),
      Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}), by fun_prop⟩,
    by simp [expBase], by
    simp [expBase, Complex.exp_two_pi_mul_I]⟩

end BraidsLinksMCG


