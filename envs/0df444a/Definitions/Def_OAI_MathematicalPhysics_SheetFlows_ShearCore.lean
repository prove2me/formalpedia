-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ShearCore
-- name    : OAI_MathematicalPhysics_SheetFlows_ShearCore
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:08:52.074909+00:00
-- url     : https://prove2.me/theorems/d678e69d-f82b-4547-8d3c-282dcb299633
-- title:
--   Shear-core programs that rescale offsets around the point $(5,6)$ in the layer $x_2=5$
-- statement:
--   **Notation.** Let $\psi$ be the standard smooth transition function ($C^\infty$, equal to $0$ on $(-\infty,0]$ and to $1$ on $[1,\infty)$), $\beta_{h,d}(s)=\psi\bigl(2(s+h+d)/d\bigr)\,\psi\bigl(2(h+d-s)/d\bigr)$ the plateau (for $d>0$ equal to $1$ when $|s|\le h+d/2$ and to $0$ when $|s|\ge h+d$), $\lambda_{h,d}(s)=s\,\beta_{h,d}(s)$, and
--   $$
--   C_{h,d,c}(s)=\sum_{k\in\mathbb{Z}}\beta_{h,d}(s-c-10k),\qquad D_{h,d,c}(s)=\sum_{k\in\mathbb{Z}}\lambda_{h,d}(s-c-10k)
--   $$
--   the smooth $10$-periodic bump and linear profiles centred at $c$. A *stationary pulse* is a $C^\infty$ vector field $w:\mathbb{R}^3\to\mathbb{R}^3$ that is invariant under translations by $10\mathbb{Z}^3$, has zero mean over the cell $[0,10)^3$, is divergence free, satisfies $Dw(x)[w(x)]=0$ and is straight invariant, $w(x+\tau\,w(x))=w(x)$ for all $x\in\mathbb{R}^3$ and $\tau\in\mathbb{R}$; it acts on points by the displacement $a\mapsto a+w(a)$, and a program (a finite list of pulses) acts by applying its pulses in order. Points of $\mathbb{R}^3$ are $x=(x_0,x_1,x_2)$ with standard basis $e_0,e_1,e_2$. Fix a collar width $d$ with $0<d\le\frac1{10}$.
--
--   1. **Core lifts.** The stationary pulses
--   $$
--   K_0(x)=D_{1/2,d,5}(x_0)\,C_{1/2,d,6}(x_1)\,e_2,\qquad K_1(x)=C_{1/2,d,5}(x_0)\,D_{1/2,d,6}(x_1)\,e_2 .
--   $$
--   2. **Core shears.** For $j\in\{0,1\}$, the stationary pulse $S_j(x)=D_{1/2,d,5}(x_2)\,e_j$.
--   3. **Triple programs.** For $l\in\mathbb{R}$,
--   $$
--   T_0(l)=\bigl[K_0,\ (l-1)S_0,\ -\tfrac1l K_0\bigr],\qquad T_1(l)=\bigl[K_1,\ (l-1)S_1,\ -\tfrac1l K_1\bigr].
--   $$
--   4. **Processing program.** For $l,m\in\mathbb{R}$, $\mathrm{Proc}(l,m)$ is the program $T_0(l)$ followed by $T_1(m)$.
--
--   Each $K_i$ and $S_j$ is a tensor-product pulse whose factor in the direction of motion is identically $1$, and its mean over $[0,10)^3$ vanishes because one factor is a $D$-profile, which has zero integral over a period.
--
--   Near the point $(5,6,5)$ these pulses are linear: for $|r|,|s|\le\frac12$ one has $K_0(5+r,6+s,z)=r\,e_2$, $K_1(5+r,6+s,z)=s\,e_2$ and $S_j(x_0,x_1,5+r)=r\,e_j$. Thus $T_0(l)$ lifts the point $(5+r,6+s,5)$ to height $5+r$, shears it horizontally by $(l-1)r$, and lowers it again by $\frac1l\cdot lr=r$, ending at $(5+lr,6+s,5)$ when $l\ne0$ and $|lr|\le\frac12$; likewise $T_1(m)$ rescales the second offset, so $\mathrm{Proc}(l,m)$ maps $(5+r,6+s,5)$ to $(5+lr,6+ms,5)$. Points with $x_1\in[2,3]$ and $x_2=2$ are left untouched. This is how a diagonal rescaling of offsets is realized by divergence-free shear flows with vanishing advection term.
--
--   **Formalization Note** The objects are `coreLift0`, `coreLift1`, `coreHorizontal`, `tripleProgram0`, `tripleProgram1` and `processingProgram`, all built with `StationaryPulse.tensor` from `Cprofile (1/2) d.size c` and `Dprofile (1/2) d.size c`. The last pulse of a triple uses the scale factor $-1/l$, which Lean evaluates to $0$ when $l=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/ShearCore.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/ShearCore.lean by skeleton subtraction
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
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Pulses
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Localization

namespace OAI

/-! SheetFlows shear core. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

variable (d : Collar)

def coreLift0 : StationaryPulse :=
  StationaryPulse.tensor 2 ![Dprofile (1/2) d.size 5, Cprofile (1/2) d.size 6, fun _ => 1]
    (by intro k; fin_cases k
        · exact Dprofile_contDiff _ _ d.positive
        · exact Cprofile_contDiff _ _ d.positive
        · exact contDiff_const)
    (by intro k; fin_cases k
        · exact Dprofile_periodic _ _ _
        · exact Cprofile_periodic _ _ _
        · exact fun _ => rfl)
    (fun _ => rfl) 0
    (by apply Dprofile_integral_zero d.positive <;> linarith [d.small])

def coreLift1 : StationaryPulse :=
  StationaryPulse.tensor 2 ![Cprofile (1/2) d.size 5, Dprofile (1/2) d.size 6, fun _ => 1]
    (by intro k; fin_cases k
        · exact Cprofile_contDiff _ _ d.positive
        · exact Dprofile_contDiff _ _ d.positive
        · exact contDiff_const)
    (by intro k; fin_cases k
        · exact Cprofile_periodic _ _ _
        · exact Dprofile_periodic _ _ _
        · exact fun _ => rfl)
    (fun _ => rfl) 1
    (by apply Dprofile_integral_zero d.positive <;> linarith [d.small])

def coreHorizontal (j : Fin 2) : StationaryPulse :=
  StationaryPulse.tensor j.castSucc ![fun _ => 1, fun _ => 1, Dprofile (1/2) d.size 5]
    (by intro k; fin_cases k
        · exact contDiff_const
        · exact contDiff_const
        · exact Dprofile_contDiff _ _ d.positive)
    (by intro k; fin_cases k
        · exact fun _ => rfl
        · exact fun _ => rfl
        · exact Dprofile_periodic _ _ _)
    (by intro s; fin_cases j <;> rfl) 2
    (by apply Dprofile_integral_zero d.positive <;> linarith [d.small])

def tripleProgram0 (l : ℝ) : List StationaryPulse :=
  [coreLift0 d, (coreHorizontal d 0).scale (l-1), (coreLift0 d).scale (-1/l)]

def tripleProgram1 (l : ℝ) : List StationaryPulse :=
  [coreLift1 d, (coreHorizontal d 1).scale (l-1), (coreLift1 d).scale (-1/l)]

def processingProgram (l m : ℝ) : List StationaryPulse :=
  tripleProgram0 d l ++ tripleProgram1 d m

end Solenoidal
end
end

end OAI


