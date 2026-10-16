-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Routing
-- name    : OAI_MathematicalPhysics_SheetFlows_Routing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:09:34.275499+00:00
-- url     : https://prove2.me/theorems/7a01c66e-161a-4a74-a93e-b099cdaaa504
-- title:
--   Routing programs that carry each source rectangle of the sheet affinely onto its target rectangle
-- statement:
--   **Notation.** A rectangle $R$ has rational corners $\ell_j<u_j$ ($j=0,1$), carrier $\{y\in\mathbb{R}^2:\ell_j\le y_j\le u_j\}$, centre $c(R)=\bigl((\ell_0+u_0)/2,(\ell_1+u_1)/2\bigr)$ and half-widths $w_j(R)=(u_j-\ell_j)/2$; it lies in the coding square if its carrier is contained in $[2,3]^2$. A *stationary pulse* is a $C^\infty$ vector field $w:\mathbb{R}^3\to\mathbb{R}^3$ that is invariant under translations by $10\mathbb{Z}^3$, has zero mean over the cell $[0,10)^3$, is divergence free, satisfies $Dw(x)[w(x)]=0$ and is straight invariant, $w(x+\tau\,w(x))=w(x)$ for all $x\in\mathbb{R}^3$ and $\tau\in\mathbb{R}$; it acts on points by the displacement $a\mapsto a+w(a)$, and a program (a finite list of pulses) acts by applying its pulses in order. Points of $\mathbb{R}^3$ are $x=(x_0,x_1,x_2)$ with standard basis $e_0,e_1,e_2$. Fix a collar width $d$ with $0<d\le\frac1{10}$, and let $C_{h,d,c}(s)=\sum_{k\in\mathbb{Z}}\beta_{h,d}(s-c-10k)$ be the smooth $10$-periodic bump built from the plateau $\beta_{h,d}(s)=\psi\bigl(2(s+h+d)/d\bigr)\,\psi\bigl(2(h+d-s)/d\bigr)$, where $\psi$ is the standard smooth transition function ($0$ on $(-\infty,0]$, $1$ on $[1,\infty)$); for the small parameters used here it equals $1$ within distance $h+d/2$ of $c+10\mathbb{Z}$ and $0$ at distance at least $h+d$. The following pulses and programs are used:
--   - the vertical pulse $V_{R,s}(x)=C_{w_0,d,c_0+s}(x_0)\bigl(C_{w_1,d,c_1}(x_1)-C_{w_1,d,c_1+4}(x_1)\bigr)e_2$ of a rectangle $R$ in the coding square, with $c=c(R)$, $w=w(R)$ and shift $s\in\mathbb{R}$;
--   - the travel program $\mathrm{Tr}(\delta)$, $\delta\in\mathbb{R}^2$, consisting of the two pulses $\delta_j\bigl(C_{0,d,5}(x_2)-C_{0,d,8}(x_2)\bigr)e_j$ for $j=0,1$;
--   - the shear-core processing program $\mathrm{Proc}(l,m)$, made of two lift–shear–lower triples of pulses around the point $(5,6,5)$.
--
--   A *sheet datum* of size $N$ consists of source rectangles $S_0,\dots,S_{N-1}$ and target rectangles $T_0,\dots,T_{N-1}$ in the coding square (the sources pairwise separated by positive distances, and likewise the targets) and positive rational ratios $r_i=(r_{i,0},r_{i,1})$ such that the diagonal map
--   $$
--   \phi_i(y)=\bigl(c_0(T_i)+r_{i,0}\,(y_0-c_0(S_i)),\ c_1(T_i)+r_{i,1}\,(y_1-c_1(S_i))\bigr)
--   $$
--   maps the carrier of $S_i$ onto that of $T_i$. This file defines:
--
--   1. **Evacuation program** of a rectangle $R$ in the coding square: the pulse $3V_{R,0}$, then $\mathrm{Tr}(4,0)$, then the pulse $-3V_{R,4}$.
--   2. **Instruction program** for the $i$-th pair of a sheet datum: the pulse $3V_{S_i,4}$, then
--   $$
--   \mathrm{Tr}\bigl(1-c_0(S_i),\,6-c_1(S_i)\bigr),\quad \mathrm{Proc}(r_{i,0},r_{i,1}),\quad \mathrm{Tr}\bigl(c_0(T_i)-5,\,c_1(T_i)-6\bigr),
--   $$
--   in this order, and finally the pulse $-3V_{T_i,0}$.
--   3. **Sheet program** of a sheet datum: the evacuation programs of $S_0,\dots,S_{N-1}$, followed by the instruction programs for $i=0,\dots,N-1$.
--
--   Write $\mathrm{sh}(y)=(y_0,y_1,2)$ for the points of the sheet. The evacuation of $S_i$ lifts $\mathrm{sh}(y)$, $y\in S_i$, to height $5$, moves it by $4$ in the $x_0$-direction and lowers it back, ending at $(y_0+4,y_1,2)$. The instruction for $i$ lifts this evacuated copy to height $5$, translates it so that the centre of the copy of $S_i$ goes to $(5,6)$, rescales the offsets by $r_{i,0}$ and $r_{i,1}$, translates the centre to that of $T_i$, and lowers the result onto the sheet at $\mathrm{sh}(\phi_i(y))$. When the sources, and also the targets, are $d$-collar separated, every other evacuation and instruction leaves these points fixed, so the whole sheet program maps $\mathrm{sh}(y)$ to $\mathrm{sh}(\phi_i(y))$ for $y\in S_i$; the scheduled velocity built from this program then has the prescribed time-one flow on the sheet.
--
--   **Formalization Note** The programs are `evacuateProgram`, `instructionProgram` and `sheetProgram`; the sheet program is the concatenation of `List.flatMap` over `List.finRange N` of the evacuations with that of the instructions. The simp lemmas `StationaryPulse.apply_of_field_zero` and `StationaryPulse.scale_apply_of_field_zero` say that a pulse, or any rescaling of it, fixes every point where its field vanishes. The separation and image conditions contained in `SheetData N` are not used by the definitions themselves.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/Routing.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Routing.lean by skeleton subtraction
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
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ShearCore

namespace OAI

/-! SheetFlows routing. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

@[simp] theorem StationaryPulse.apply_of_field_zero (p : StationaryPulse) {x : Space}
    (h : p.field x = 0) : p.apply x = x := by
  rw [StationaryPulse.apply, h, add_zero]

@[simp] theorem StationaryPulse.scale_apply_of_field_zero (p : StationaryPulse) (c : ℝ)
    {x : Space} (h : p.field x = 0) : (p.scale c).apply x = x := by
  apply StationaryPulse.apply_of_field_zero
  rw [StationaryPulse.scale_field, h, smul_zero]

def evacuateProgram (d : Collar) (R : Rectangle) (hR : R.inCodingSquare) :
    List StationaryPulse :=
  [(verticalPulse d R hR 0).scale 3] ++ travelProgram d ![4,0] ++
    [(verticalPulse d R hR 4).scale (-3)]

def instructionProgram {N : ℕ} (d : Collar) (D : SheetData N) (i : Fin N) :
    List StationaryPulse :=
  [(verticalPulse d (D.source i) (D.source_inside i) 4).scale 3] ++
  travelProgram d ![1-(D.source i).center 0,6-(D.source i).center 1] ++
  processingProgram d (D.ratio i 0) (D.ratio i 1) ++
  travelProgram d ![(D.target i).center 0-5,(D.target i).center 1-6] ++
  [(verticalPulse d (D.target i) (D.target_inside i) 0).scale (-3)]

def sheetProgram {N : ℕ} (d : Collar) (D : SheetData N) : List StationaryPulse :=
  (List.finRange N).flatMap (fun i => evacuateProgram d (D.source i) (D.source_inside i)) ++
  (List.finRange N).flatMap (instructionProgram d D)

end Solenoidal
end

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

end Solenoidal
end

end OAI


