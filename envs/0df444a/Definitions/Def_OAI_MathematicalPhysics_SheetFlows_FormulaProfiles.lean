-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_FormulaProfiles
-- name    : OAI_MathematicalPhysics_SheetFlows_FormulaProfiles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:20:20.049532+00:00
-- url     : https://prove2.me/theorems/e48c5b54-d2d6-4a4c-945c-765c28fca99e
-- title:
--   Rational parameters, differences of periodic jet certificates, and rational formulas for stationary pulses
-- statement:
--   This short file adds three notions used to show that the building blocks of a sheet flow are given by explicit formulas with rational data. Throughout, $\psi(s)=e^{-1/s}$ for $s>0$ and $\psi(s)=0$ for $s\le0$. A *jet expression* is a formal one-variable expression built from rational constants, the identity, sums, products, rational affine substitutions $s\mapsto e(as+b)$, flat functions $p(1/s)\psi(s)$ with $p\in\mathbb{Q}[X]$, and $R(s)=1/(\psi(s)+\psi(1-s))$; a *box expression* is a formal expression in the space-time coordinates $z_0=t,z_1=x_0,z_2=x_1,z_3=x_2$ built from rational constants, jet expressions applied to a single coordinate, sums and products.
--
--   1. **Rational parameter.** A real number $x$ is a rational parameter if $x=q$ for some $q\in\mathbb{Q}$.
--   2. **Difference of periodic jet certificates.** Fix $T\in\mathbb{Q}$. A period-$T$ jet certificate for $f:\mathbb{R}\to\mathbb{R}$ records that $T>0$, that $f$ is $C^\infty$ and $T$-periodic, and supplies a jet expression $e_f$ whose value agrees with $f$ on $[0,T]$. From certificates for $f$ and $g$ one obtains a certificate for $f-g$ with expression
--   $$e_{f-g}=e_f+(-1)\cdot e_g .$$
--   3. **Rational formula of a stationary pulse.** A *stationary pulse* is a vector field $w:\mathbb{R}^3\to\mathbb{R}^3$ that is $C^\infty$, satisfies $w(x+10k)=w(x)$ for all $k\in\mathbb{Z}^3$, has $\int_{[0,10)^3}w(x)\,dx=0$, is divergence free, satisfies $Dw(x)[w(x)]=0$ for all $x$, and is straight invariant: $w(x+s\,w(x))=w(x)$ for all $x\in\mathbb{R}^3$ and $s\in\mathbb{R}$. Such a pulse *has a rational formula* if the time-independent field $(t,x)\mapsto w(x)$ coincides on $[0,1]\times[0,10]^3$ with $\bigl(E_0(t,x),E_1(t,x),E_2(t,x)\bigr)$ for some box expressions $E_0,E_1,E_2$.
--
--   Rational parameters are the hypothesis under which the centers, widths and collar sizes of the cutoff profiles can be written with rational coefficients; closure of jet certificates under subtraction covers profiles that are differences of shifted cutoffs; and the rational-formula property of stationary pulses is what is established for every pulse of the routing programs, so that the scheduled sheet velocity has an explicit formula on one space-time period.
--
--   **Formalization Note** The definitions are `RationalParameter`, `PeriodicJet.sub` (a data-valued definition built from `PeriodicJet.add`, `PeriodicJet.mul` and `PeriodicJet.const T _ (-1)`), and `StationaryPulse.RationalFormula p := HasRationalFormula (fun _ => p.field)`. The file also declares a section variable `d : Collar` with the hypothesis that its size is a rational parameter, but defines nothing further with it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/FormulaProfiles.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/FormulaProfiles.lean by skeleton subtraction
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
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Routing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetCalculus
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_BoxJets
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalFormula

namespace OAI

/-! SheetFlows formula profiles. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

def RationalParameter (x : ℝ) : Prop := ∃ q : ℚ, (q:ℝ) = x

namespace RationalParameter

end RationalParameter

def PeriodicJet.sub {T : ℚ} {f g : ℝ → ℝ} (p : PeriodicJet T f) (q : PeriodicJet T g) :
    PeriodicJet T (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg,neg_one_mul,Rat.cast_neg,Rat.cast_one] using
    p.add ((PeriodicJet.const T p.positive (-1)).mul q)

namespace StationaryPulse

def RationalFormula (p : StationaryPulse) : Prop := HasRationalFormula (fun _ => p.field)

end StationaryPulse

variable (d : Collar) (hd : RationalParameter d.size)
include hd

end Solenoidal
end

end OAI


