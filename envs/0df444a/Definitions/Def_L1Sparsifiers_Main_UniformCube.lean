-- Prove2me | Definitions.Def_L1Sparsifiers_Main_UniformCube
-- name    : L1Sparsifiers_Main_UniformCube
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:20.961202+00:00
-- url     : https://prove2.me/theorems/a5bcc1d9-9fae-41c3-a661-8311bfba4cbf
-- title:
--   The cube $[-1,1]^m$, the continuous uniform probability on it, and cube vertices
-- statement:
--   The **cube** is $[-1,1]^m\subseteq\mathbb R^m$. For an event $E\subseteq\mathbb R^m$, the probability of $E$ when $x$ is drawn uniformly from the solid cube is
--   $$\mathbb P_{x\sim[-1,1]^m}[x\in E]=\frac{\mathrm{Vol}_m(E\cap[-1,1]^m)}{2^m},$$
--   normalized Lebesgue measure on the cube, equivalently $m$ independent coordinates each uniform on $[-1,1]$. For $m=0$ the cube is the single point of $\mathbb R^0$ and has probability $1$.
--
--   A **vertex** of the cube is a sign vector $\sigma\in\{-1,1\}^m$, viewed as a point of $\mathbb R^m$. The uniform distribution on the $2^m$ vertices is a different distribution from the uniform distribution on the solid cube; both appear in the paper.
--
--   **Formalization Note** `volume` is Lebesgue measure on `Fin m → ℝ`; on a non-measurable set it is the outer measure. The events to which `cubeProb` is applied in this mission are measurable or null-measurable, where both agree. Sign vectors are the published `PSDPolyApprox.Cube m = Fin m → ℤˣ`, and `vertex σ` casts each unit $\pm1$ to a real number.
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), notation $x\sim[-1,1]^m$, pp.6, 9–12; $x\sim\{-1,1\}^m$, pp.6, 10

import Mathlib
import Definitions.Def_PSDPolyApprox_Cube

namespace L1Sparsifiers.Main

open MeasureTheory

/-- The solid cube `[-1,1]^m ⊆ ℝ^m`. -/
def cube (m : ℕ) : Set (Fin m → ℝ) := Set.Icc (-1) 1

/-- **Probability under the continuous uniform distribution on `[-1,1]^m`.**
Reis–Rothvoss, STOC 2027 submission #162, notation `P_{x∼[-1,1]^m}` (pp.6, 9–12): for an event
`E ⊆ ℝ^m`, `P_{x∼[-1,1]^m}[x ∈ E] = Vol_m(E ∩ [-1,1]^m) / 2^m`, normalized Lebesgue measure on
the cube (equivalently, independent uniform coordinates on `[-1,1]`). For `m = 0` the cube is the
single point of `ℝ^0` and has probability `1`.

**Formalization Note.** `volume` is the Lebesgue measure on `Fin m → ℝ`; on a set that is not
measurable it is the outer measure. -/
noncomputable def cubeProb (m : ℕ) (E : Set (Fin m → ℝ)) : ℝ :=
  (volume (E ∩ cube m)).toReal / 2 ^ m

/-- The vertex `σ ∈ {-1,1}^m` of the cube as a point of `ℝ^m`; the published `PSDPolyApprox.Cube m`
is `Fin m → ℤˣ`, whose values are exactly `±1`. -/
def vertex {m : ℕ} (σ : PSDPolyApprox.Cube m) : Fin m → ℝ := fun i => ((σ i : ℤ) : ℝ)

end L1Sparsifiers.Main


