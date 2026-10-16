-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Localization
-- name    : OAI_MathematicalPhysics_SheetFlows_Localization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:06:07.994277+00:00
-- url     : https://prove2.me/theorems/83160a81-438b-4493-940e-50b162c1b80f
-- title:
--   Collars, lifted sheet points, and vertical and horizontal transport pulses
-- statement:
--   **Notation.** Let $\psi$ be the standard smooth transition function ($C^\infty$, equal to $0$ on $(-\infty,0]$ and to $1$ on $[1,\infty)$). For $h,c\in\mathbb{R}$ and $d>0$, the plateau $\beta_{h,d}(s)=\psi\bigl(2(s+h+d)/d\bigr)\,\psi\bigl(2(h+d-s)/d\bigr)$ equals $1$ for $|s|\le h+d/2$ and vanishes for $|s|\ge h+d$, and $C_{h,d,c}(s)=\sum_{k\in\mathbb{Z}}\beta_{h,d}(s-c-10k)$ is its smooth $10$-periodic translate centred at $c$. A *rectangle* $R$ has rational corners $\ell_j<u_j$ ($j=0,1$), carrier $\{y\in\mathbb{R}^2:\ell_j\le y_j\le u_j\}$, centre $c_j(R)=(\ell_j+u_j)/2$ and half-widths $w_j(R)=(u_j-\ell_j)/2$; it lies in the coding square if $2\le\ell_j$ and $u_j\le3$ for $j=0,1$. A *stationary pulse* is a $C^\infty$ vector field $w:\mathbb{R}^3\to\mathbb{R}^3$ that is invariant under translations by $10\mathbb{Z}^3$, has zero mean over the cell $[0,10)^3$, is divergence free, satisfies $Dw(x)[w(x)]=0$ and is straight invariant, $w(x+\tau\,w(x))=w(x)$ for all $x\in\mathbb{R}^3$ and $\tau\in\mathbb{R}$; it acts on points by the displacement $a\mapsto a+w(a)$, and a program (a finite list of pulses) acts by applying its pulses in order. Points of $\mathbb{R}^3$ are $x=(x_0,x_1,x_2)$ with standard basis $e_0,e_1,e_2$.
--
--   1. **Collar separation.** A family $R_0,\dots,R_{N-1}$ of rectangles is $d$-collar separated ($d\in\mathbb{R}$) if for all $i\ne j$ and every $y$ in the carrier of $R_j$ there is a coordinate $k\in\{0,1\}$ with
--   $$
--   |y_k-c_k(R_i)|\ge w_k(R_i)+d ,
--   $$
--   i.e. every point of $R_j$ has $\ell^\infty$-distance at least $d$ from $R_i$.
--   2. **Centres.** If $R$ lies in the coding square, then $2\le c_j(R)\le3$ for $j=0,1$.
--   3. **Collar.** A collar is a real number $d$ with $0<d\le\frac1{10}$.
--   4. **Lifted points.** For $s,z\in\mathbb{R}$ and $y\in\mathbb{R}^2$, $L_{s,z}(y)=(y_0+s,\ y_1,\ z)\in\mathbb{R}^3$.
--   5. **Vertical pulse.** For a collar $d$, a rectangle $R$ in the coding square with $c=c(R)$ and $w=w(R)$, and a shift $s\in\mathbb{R}$, the stationary pulse
--   $$
--   V_{R,s}(x)=C_{w_0,d,c_0+s}(x_0)\,\bigl(C_{w_1,d,c_1}(x_1)-C_{w_1,d,c_1+4}(x_1)\bigr)\,e_2 .
--   $$
--   6. **Horizontal pulses.** For a collar $d$ and $j\in\{0,1\}$, the stationary pulse
--   $$
--   H_j(x)=\bigl(C_{0,d,5}(x_2)-C_{0,d,8}(x_2)\bigr)\,e_j .
--   $$
--   7. **Travel program.** For $\delta=(\delta_0,\delta_1)\in\mathbb{R}^2$, the two-pulse program $\mathrm{Tr}(\delta)=[\delta_0H_0,\ \delta_1H_1]$.
--
--   Both $V_{R,s}$ and $H_j$ are tensor-product pulses $g_0(x_0)g_1(x_1)g_2(x_2)\,e_i$ whose factor in the direction of motion is identically $1$; their mean vanishes because one factor is a difference of two translated bumps with equal integrals over a period.
--
--   These are the transport primitives of an explicit Navier–Stokes flow that moves pieces of the sheet $\{x_2=2\}$. For $s\in[0,4]$ the vertical pulse $V_{R,s}$ equals $e_2$ at every lifted point $L_{s,z}(y)$ with $y\in R$ and vanishes at the lifted points of rectangles collar separated from $R$, so $3V_{R,s}$ lifts exactly one rectangle from height $2$ to height $5$. The horizontal pulses equal $e_j$ near the layer $x_2=5$ and vanish at height $2$, so the travel program translates the layer $\{x_2=5\}$ by $(\delta_0,\delta_1,0)$ and leaves the sheet $\{x_2=2\}$ fixed.
--
--   **Formalization Note** The objects are `Rectangle.CollarSeparated`, `Rectangle.center_bounds`, `Collar` (a structure with `size`, `positive`, `small`), `lifted`, `verticalPulse d R hR s`, `horizontalPulse` and `travelProgram`; both pulses are built with `StationaryPulse.tensor`, and in `horizontalPulse` the direction is `j.castSucc`, i.e. $e_0$ or $e_1$. The proof `hR` that $R$ lies in the coding square is used only to certify the zero mean. `StationaryPulse.scale_field` is the simp lemma $(c\,w)(x)=c\,w(x)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/Localization.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Localization.lean by skeleton subtraction
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

namespace OAI

/-! SheetFlows localization. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

def Rectangle.CollarSeparated {N : ℕ} (R : Fin N → Rectangle) (d : ℝ) : Prop :=
  ∀ i j, i ≠ j → ∀ y ∈ (R j).carrier,
    ∃ k, (R i).halfWidth k + d ≤ |y k - (R i).center k|

theorem Rectangle.center_bounds (R : Rectangle) (hR : R.inCodingSquare) (j : Fin 2) :
    2 ≤ R.center j ∧ R.center j ≤ 3 := by
  have hl : (2:ℝ) ≤ R.lower j := by exact_mod_cast (hR j).1
  have hu : (R.upper j:ℝ) ≤ 3 := by exact_mod_cast (hR j).2
  have hw : (R.lower j:ℝ) ≤ R.upper j := by exact_mod_cast (R.positive j).le
  dsimp [Rectangle.center]
  constructor <;> linarith

structure Collar where
  size : ℝ
  positive : 0 < size
  small : size ≤ 1/10

variable (d : Collar)

def lifted (s z : ℝ) (y : Plane) : Space := ![y 0 + s, y 1, z]

def verticalPulse (R : Rectangle) (hR : R.inCodingSquare) (s : ℝ) : StationaryPulse :=
  StationaryPulse.tensor 2
    ![Cprofile (R.halfWidth 0) d.size (R.center 0+s),
      fun x => Cprofile (R.halfWidth 1) d.size (R.center 1) x -
        Cprofile (R.halfWidth 1) d.size (R.center 1+4) x, fun _ => 1]
    (by intro j; fin_cases j
        · exact Cprofile_contDiff _ _ d.positive
        · exact (Cprofile_contDiff _ _ d.positive).sub (Cprofile_contDiff _ _ d.positive)
        · exact contDiff_const)
    (by intro j; fin_cases j
        · exact Cprofile_periodic _ _ _
        · exact (Cprofile_periodic _ _ _).sub (Cprofile_periodic _ _ _)
        · exact fun _ => rfl)
    (fun _ => rfl) 1
    (by
      apply Cprofile_corrected_integral_zero d.positive <;>
        have hw := R.halfWidth_le_half hR 1 <;>
        have hc := R.center_bounds hR 1 <;>
        linarith [d.small])

def horizontalPulse (j : Fin 2) : StationaryPulse :=
  StationaryPulse.tensor j.castSucc
    ![fun _ => 1, fun _ => 1, fun z => Cprofile 0 d.size 5 z - Cprofile 0 d.size 8 z]
    (by intro k; fin_cases k
        · exact contDiff_const
        · exact contDiff_const
        · exact (Cprofile_contDiff _ _ d.positive).sub (Cprofile_contDiff _ _ d.positive))
    (by intro k; fin_cases k
        · exact fun _ => rfl
        · exact fun _ => rfl
        · exact (Cprofile_periodic _ _ _).sub (Cprofile_periodic _ _ _))
    (by intro s; fin_cases j <;> rfl) 2
    (by apply Cprofile_corrected_integral_zero d.positive <;> linarith [d.small])

@[simp] theorem StationaryPulse.scale_field (c : ℝ) (p : StationaryPulse) (x : Space) :
    (p.scale c).field x = c • p.field x := rfl

def travelProgram (δ : Plane) : List StationaryPulse :=
  [(horizontalPulse d 0).scale (δ 0), (horizontalPulse d 1).scale (δ 1)]

end Solenoidal
end
end

end OAI


