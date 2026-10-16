-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
-- name    : OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T00:58:57.159745+00:00
-- url     : https://prove2.me/theorems/41b81032-9332-424b-a2ca-9cce54a7e23c
-- title:
--   $C^1$ functions on the torus $\mathbb{R}^3/(10\mathbb{Z})^3$ and the kinetic energy density
-- statement:
--   Points of $\mathbb{R}^3$ are $x=(x_0,x_1,x_2)$ with standard basis $e_0,e_1,e_2$.
--
--   1. **Periodic $C^1$ functions.** Let $E$ be a real normed space. A function $g:\mathbb{R}^3\to E$ is called *torus-$C^1$* if
--      - $g$ is Fréchet differentiable at every point of $\mathbb{R}^3$;
--      - for each $j\in\{0,1,2\}$ the partial derivative $x\mapsto\partial_jg(x)=Dg(x)[e_j]$ is continuous on $\mathbb{R}^3$;
--      - $g(x+10k)=g(x)$ for all $x\in\mathbb{R}^3$ and all $k\in\mathbb{Z}^3$.
--
--      In other words, $g$ is a $C^1$ function that is periodic with respect to the lattice $10\mathbb{Z}^3$, i.e. a $C^1$ function on the torus $\mathbb{R}^3/(10\mathbb{Z})^3$.
--   2. **Kinetic energy density.** For $a=(a_0,a_1,a_2)\in\mathbb{R}^3$,
--   $$
--   \kappa(a)=\sum_{i=0}^{2}\frac{a_i\,a_i}{2}=\frac{|a|^2}{2}.
--   $$
--
--   Torus-$C^1$ is the regularity class in which integration-by-parts identities on the periodic cell $[0,10)^3$ are established, for instance that the cell integral of a divergence $\sum_j\partial_jg_j$ vanishes, and that $\int_{[0,10)^3}Dq(x)[v(x)]\,dx=0$ for a divergence-free field $v$. These identities and the density $\kappa$ enter the energy method showing that classical solutions of the forced Navier–Stokes equations with given forcing and zero initial data are unique.
--
--   **Formalization Note** `TorusC1 g` is a structure (a proposition) with fields `differentiable`, `continuous_partial` and `periodic`, where the lattice translation $10k$ is written `deck k`; the density is `kineticDensity`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/ClassicalRegularity.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/ClassicalRegularity.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SolenoidalSheetPrograms mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce

namespace OAI

/-! SheetFlows classical regularity. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

structure TorusC1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Space → E) : Prop where
  differentiable : Differentiable ℝ g
  continuous_partial : ∀ j, Continuous (fun x => fderiv ℝ g x (basis j))
  periodic : ∀ x k, g (x + deck k) = g x

def kineticDensity (a : Space) : ℝ := ∑ i : Fin 3, a i * a i / 2

end Solenoidal
end

end OAI


