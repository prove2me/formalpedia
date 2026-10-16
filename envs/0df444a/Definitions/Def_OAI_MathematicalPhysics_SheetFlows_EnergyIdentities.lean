-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
-- name    : OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T00:59:39.845846+00:00
-- url     : https://prove2.me/theorems/c2ede12e-d99e-4e9f-9e0b-5ffa5045db67
-- title:
--   Euclidean dot product and the relative kinetic energy of two velocity fields
-- statement:
--   1. **Dot product.** For $a,b\in\mathbb{R}^3$, $\langle a,b\rangle=\sum_{i=0}^{2}a_ib_i$. It is linear in its second argument: for $a,b,c\in\mathbb{R}^3$ and $\lambda\in\mathbb{R}$,
--   $$
--   \langle a,b+c\rangle=\langle a,b\rangle+\langle a,c\rangle,\quad \langle a,b-c\rangle=\langle a,b\rangle-\langle a,c\rangle,\quad \langle a,-b\rangle=-\langle a,b\rangle,\quad \langle a,\lambda b\rangle=\lambda\langle a,b\rangle .
--   $$
--   2. **Relative energy.** For vector fields $u,v:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ and $t\in\mathbb{R}$,
--   $$
--   \mathcal E_{u,v}(t)=\int_{[0,10)^3}\kappa\bigl(v(t,x)-u(t,x)\bigr)\,dx=\frac12\int_{[0,10)^3}\bigl|v(t,x)-u(t,x)\bigr|^2\,dx,
--   $$
--   where $\kappa(a)=\sum_{i=0}^{2}a_i^2/2$ is the kinetic energy density and $[0,10)^3$ is the fundamental cell of the lattice $10\mathbb{Z}^3$.
--
--   $\mathcal E_{u,v}(t)$ is half the squared $L^2$ distance between $u(t,\cdot)$ and $v(t,\cdot)$ on one period cell. It is the quantity behind the uniqueness of classical solutions of the forced Navier–Stokes equations: for two solutions with the same forcing, its time derivative is $\int\langle v-u,\partial_tv-\partial_tu\rangle$, which is bounded by a multiple of $\mathcal E_{u,v}$ itself, while $\mathcal E_{u,v}(0)=0$, and a Gronwall-type argument then forces $\mathcal E_{u,v}\equiv0$.
--
--   **Formalization Note** The objects are `euclidDot` (with simp lemmas `euclidDot_add`, `euclidDot_sub`, `euclidDot_neg`, `euclidDot_smul`) and `relativeEnergy`, a Bochner integral over `fundamentalCell` of `kineticDensity`; as usual in Lean, the integral of a non-integrable function is $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/EnergyIdentities.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/EnergyIdentities.lean by skeleton subtraction
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
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity

namespace OAI

/-! SheetFlows energy identities. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

def euclidDot (a b : Space) : ℝ := ∑ i : Fin 3, a i * b i

@[simp] theorem euclidDot_add (a b c : Space) :
    euclidDot a (b + c) = euclidDot a b + euclidDot a c := by
  simp [euclidDot, mul_add, Finset.sum_add_distrib]

@[simp] theorem euclidDot_sub (a b c : Space) :
    euclidDot a (b - c) = euclidDot a b - euclidDot a c := by
  simp [euclidDot, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem euclidDot_neg (a b : Space) : euclidDot a (-b) = -euclidDot a b := by
  simp [euclidDot, Finset.sum_neg_distrib]

@[simp] theorem euclidDot_smul (a b : Space) (c : ℝ) :
    euclidDot a (c • b) = c * euclidDot a b := by
  simp [euclidDot, ← Finset.mul_sum, mul_left_comm]

def relativeEnergy (u v : Field) (t : ℝ) : ℝ :=
  ∫ x in fundamentalCell, kineticDensity (v t x - u t x)

end Solenoidal
end

end OAI


