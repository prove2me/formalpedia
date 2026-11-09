-- Prove2me | Definitions.Def_DetComplexityPowerSum_Quadratic_KernelNormalizers
-- name    : DetComplexityPowerSum_Quadratic_KernelNormalizers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:28:08.629674+00:00
-- url     : https://prove2.me/theorems/52fe64ed-7074-43e4-aeb4-e8756bcd1e3f
-- title:
--   Claim 3.6 setting — the pencil value $M(a)$, the kernel unions $U,V$ and admissible $g,h$
-- statement:
--   For $M_0,M_1,\dots,M_n\in\mathbb C^{m\times m}$ and $a\in\mathbb C^n$, write $M(a)=M_0+\sum_{i=1}^n a_iM_i$. With $S$ the polar slice of Definition 2.2, put
--   $$U=\bigcup_{a\in S}\{u\in\mathbb C^m: u\ne 0,\ u^TM(a)=0\},\qquad V=\bigcup_{a\in S}\{v\in\mathbb C^m: v\ne 0,\ M(a)v=0\}.$$
--   A pair $g,h\in\mathbb C^m$ **normalizes the kernels** if $g^Tu\ne 0$ for every $u\in U$ and $h^Tv\ne 0$ for every $v\in V$.
--
--   These are the vectors that fix the scale of the left and right kernel vectors in the proxy system. That such a pair exists is Claim 3.6; it is not part of the definition.
--
--   **Formalization Note** Transposes are ordinary bilinear ones, written with `⬝ᵥ`, `ᵥ*` and `*ᵥ`; no complex conjugation occurs.
-- source:
--   Mrinal Kumar, Ben Lee Volk, STOC 2027 submission #131 (October 2026), p. 7, Claim 3.6

import Mathlib
import Definitions.Def_DetComplexityPowerSum_Quadratic_PolarSlice

namespace DetComplexityPowerSum.Quadratic

open Matrix

/-- The value `M(a) = M₀ + ∑ᵢ aᵢ Mᵢ` of the affine matrix pencil at a point `a ∈ ℂⁿ`. -/
noncomputable def pencil {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) (a : Fin n → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  M₀ + ∑ i : Fin n, a i • M i

/-- The set `U = ⋃_{a ∈ S} {u : u ≠ 0, uᵀ M(a) = 0}` of Claim 3.6. -/
def leftKernelUnion {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) : Set (Fin m → ℂ) :=
  {u | ∃ a ∈ polarSlice n, u ≠ 0 ∧ u ᵥ* pencil M₀ M a = 0}

/-- The set `V = ⋃_{a ∈ S} {v : v ≠ 0, M(a) v = 0}` of Claim 3.6. -/
def rightKernelUnion {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) : Set (Fin m → ℂ) :=
  {v | ∃ a ∈ polarSlice n, v ≠ 0 ∧ pencil M₀ M a *ᵥ v = 0}

/-- The property of the vectors `g, h` picked in Claim 3.6: `gᵀu ≠ 0` for every `u ∈ U` and
`hᵀv ≠ 0` for every `v ∈ V`. Transposes are ordinary bilinear ones, without conjugation. -/
def NormalizesKernels {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) (g h : Fin m → ℂ) : Prop :=
  (∀ u ∈ leftKernelUnion M₀ M, g ⬝ᵥ u ≠ 0) ∧ (∀ v ∈ rightKernelUnion M₀ M, h ⬝ᵥ v ≠ 0)

end DetComplexityPowerSum.Quadratic


