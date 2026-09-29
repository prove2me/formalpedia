-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2KernelCasimir
-- name    : LanglandsTunnell_CubicInduction_SlabL2KernelCasimir
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/832b1998-ddf2-58fa-9462-332f4753f99f
-- title:
--   Left-invariant derivatives and Casimir operators on kernel charts
-- statement:
--   This module sets up differential operators acting on functions of a real $3\times 3$ array of entries, to be used as the archimedean chart of functions on $\mathrm{GL}_3$ of the adeles of $\mathbb{Q}$.
--
--   `kernelEnt` sends $h \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q},\infty})$ to the array $(a,b) \mapsto$ [`AutomorphicForm.StandardKernel.realCoord`](../def/AutomorphicForm_SmoothingKernel.html#L766) of the $(a,b)$ entry of $h$, i.e. the real matrix obtained by reading each entry through the ring homomorphism from the infinite adele ring of $\mathbb{Q}$ to $\mathbb{R}$ given by evaluation at the unique infinite place followed by the identification of its completion with $\mathbb{R}$.
--
--   For indices $i,j \in \{0,1,2\}$ and $\beta : (\mathrm{Fin}\,3 \to \mathrm{Fin}\,3 \to \mathbb{R}) \to \mathbb{C}$, `kernelLeftDeriv i j β` is the function $m \mapsto -\,(D\beta)_m\bigl(a,b \mapsto [a = i]\,m_{jb}\bigr)$: minus the Fréchet derivative of $\beta$ at $m$, with $\mathbb{R}$ as base field, evaluated on the tangent vector $E_{ij}m$, the array whose $i$-th row is the $j$-th row of $m$ and whose other rows vanish. The lemma `kernelLeftDeriv_apply` records this equation. Since Mathlib's `fderiv` is $0$ where $\beta$ fails to be differentiable, the operator is defined on all functions, with no smoothness hypothesis.
--
--   From these, three operators are formed by composition and summation over all indices: `kernelCasimir1` $= \sum_i L_{ii}$, `kernelCasimir2` $= \sum_{i,j} L_{ij}L_{ji}$, `kernelCasimir3` $= \sum_{i,j,k} L_{ij}L_{jk}L_{ki}$, and in addition `kernelCasimir3T` $= \sum_{i,j,k} L_{ki}L_{jk}L_{ij}$, the cubic expression with the three factors applied in the opposite order.
--
--   Finally, `archChart F x` is, for $F$ a complex function on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ and $x$ a point of that group, the function $m \mapsto F(x \cdot \mathrm{archRealLift3}\,m)$, where [`WhittakerBlock.archRealLift3 m`](../def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L18) is the adelic matrix with archimedean part $m$ and trivial finite part when that matrix is invertible, and $1$ otherwise; `archChart_apply` records this. Nothing is asserted about these objects beyond the two definitional identities.
--
--   **Relation to Mathlib.** The differential operators are the project's own; they are built from Mathlib's `fderiv` over $\mathbb{R}$ and are therefore total, taking the value $0$ at points of non-differentiability.
--
--   **Where it is used.** These operators are the kernel-side counterparts of the right-translation derivatives `archDeriv` and the operators `casimir1`, `casimir2`, `casimir3` used to define finiteness under the centre of the enveloping algebra for automorphic functions on $\mathrm{GL}_3$ over $\mathbb{Q}$. They provide the vocabulary in which differentiating an archimedean convolution is transferred to the smoothing kernel, within the $\mathrm{GL}_3$ input to the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_SlabL2KernelCasimir.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Mathlib.Analysis.Calculus.FDeriv.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm

namespace LanglandsTunnell.CubicInduction.SlabL2

def kernelEnt (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Fin 3 → Fin 3 → ℝ :=
  fun a b => AutomorphicForm.StandardKernel.realCoord ((h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) a b)

def kernelLeftDeriv (i j : Fin 3) (β : (Fin 3 → Fin 3 → ℝ) → ℂ) : (Fin 3 → Fin 3 → ℝ) → ℂ :=
  fun m => -(fderiv ℝ β m (fun a b => if a = i then m j b else 0))

def kernelCasimir1 (β : (Fin 3 → Fin 3 → ℝ) → ℂ) : (Fin 3 → Fin 3 → ℝ) → ℂ :=
  fun m => ∑ i : Fin 3, kernelLeftDeriv i i β m

def kernelCasimir2 (β : (Fin 3 → Fin 3 → ℝ) → ℂ) : (Fin 3 → Fin 3 → ℝ) → ℂ :=
  fun m => ∑ i : Fin 3, ∑ j : Fin 3, kernelLeftDeriv i j (kernelLeftDeriv j i β) m

def kernelCasimir3 (β : (Fin 3 → Fin 3 → ℝ) → ℂ) : (Fin 3 → Fin 3 → ℝ) → ℂ :=
  fun m => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, kernelLeftDeriv i j (kernelLeftDeriv j k (kernelLeftDeriv k i β)) m

def kernelCasimir3T (β : (Fin 3 → Fin 3 → ℝ) → ℂ) : (Fin 3 → Fin 3 → ℝ) → ℂ :=
  fun m => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, kernelLeftDeriv k i (kernelLeftDeriv j k (kernelLeftDeriv i j β)) m

def archChart (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) : (Fin 3 → Fin 3 → ℝ) → ℂ :=
  fun m => F (x * WhittakerBlock.archRealLift3 m)

theorem kernelLeftDeriv_apply (i j : Fin 3) (β : (Fin 3 → Fin 3 → ℝ) → ℂ) (m : Fin 3 → Fin 3 → ℝ) :
    kernelLeftDeriv i j β m = -(fderiv ℝ β m (fun a b => if a = i then m j b else 0)) := rfl

theorem archChart_apply (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) (m : Fin 3 → Fin 3 → ℝ) :
    archChart F x m = F (x * WhittakerBlock.archRealLift3 m) := rfl

end LanglandsTunnell.CubicInduction.SlabL2

end


