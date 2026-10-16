-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalFormula
-- name    : OAI_MathematicalPhysics_SheetFlows_RationalFormula
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:17:25.730264+00:00
-- url     : https://prove2.me/theorems/46594a2f-8df7-4b77-9376-f3ddc9379bc3
-- title:
--   Fields given by a box-expression formula on one period, and rational pulse slots
-- statement:
--   This file connects symbolic formulas to vector fields and to the time pulses that schedule a flow. Space-time points are $z=(t,x)\in\mathbb{R}\times\mathbb{R}^3$, with coordinates $z_0=t$ and $z_{i+1}=x_i$ for $i=0,1,2$. Write $\psi(s)=e^{-1/s}$ for $s>0$ and $\psi(s)=0$ for $s\le 0$. A *jet expression* is a formal one-variable expression built from rational constants, the identity, sums, products, rational affine substitutions $s\mapsto e(as+b)$, flat functions $p(1/s)\psi(s)$ with $p\in\mathbb{Q}[X]$, and $R(s)=1/(\psi(s)+\psi(1-s))$. A *box expression* is a formal expression built from rational constants, terms $e[z_j]$ in which a jet expression $e$ is applied to one coordinate $z_j$, sums and products; it evaluates to a real function on space-time.
--
--   1. **Finite sums of box expressions.** For a list $(E_1,\dots,E_k)$, $\mathrm{suml}(E_1,\dots,E_k)=E_1+(E_2+\cdots+(E_k+0))$, and for a family $(E_i)_{i\in I}$ over a finite index type, $\sum_{i\in I}E_i$ is the sum of the list of its members. They evaluate to $\sum_{m}E_m(z)$ and $\sum_{i\in I}E_i(z)$ respectively.
--   2. **Rational formula.** A time-dependent vector field $u:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ *has a rational formula* if there are box expressions $E_0,E_1,E_2$ with
--   $$u(t,x)=\bigl(E_0(t,x),E_1(t,x),E_2(t,x)\bigr)\qquad\text{for all }(t,x)\in[0,1]\times[0,10]^3 .$$
--   3. **Spatial coordinate terms.** For $i\in\{0,1,2\}$ and a jet expression $e$, the box expression $e[x_i]=e[z_{i+1}]$, which evaluates to $e(x_i)$ at $(t,x)$.
--   4. **Rational slot endpoints.** For $m\ge 1$ and $0\le i<m$, the rationals
--   $$a_{m,i}=\frac14+\frac{i}{2m},\qquad b_{m,i}=a_{m,i}+\frac{1}{4m};$$
--   their images in $\mathbb{R}$ are the real slot endpoints used to schedule pulses.
--   5. **Jet certificate of a scheduled pulse.** Let $S(s)=\psi(s)/(\psi(s)+\psi(1-s))$ be the standard smooth transition from $0$ (for $s\le0$) to $1$ (for $s\ge1$), let $\ell_{a,b}(t)=\frac{d}{dt}S\bigl(\frac{t-a}{b-a}\bigr)$, and let $\phi_{m,i}(t)=\sum_{k\in\mathbb{Z}}\ell_{a_{m,i},b_{m,i}}(t-k)$ be the scheduled pulse, a $1$-periodic smooth bump that is nonzero only while $t$ modulo $1$ lies in the slot $(a_{m,i},b_{m,i})$. For $T\in\mathbb{Q}$, a period-$T$ jet certificate for $f:\mathbb{R}\to\mathbb{R}$ consists of the facts $T>0$, $f\in C^\infty$ and $f(s+T)=f(s)$ for all $s$, together with a jet expression $e$ such that $f=e$ on $[0,T]$. The file constructs such a certificate with $T=1$ for every $\phi_{m,i}$; its expression is the formal derivative of the jet expression $s\mapsto S\bigl(\frac{s-a_{m,i}}{b_{m,i}-a_{m,i}}\bigr)$.
--
--   The rational-formula property is the bridge between finite symbolic descriptions and the analytic fields of the construction: a smooth field that is periodic in time and space and has a rational formula on one period is determined by finitely many symbols, and so are all its derivatives. The rational slot endpoints and the certificate for $\phi_{m,i}$ make the time profiles of scheduled flows expressible in this language.
--
--   **Formalization Note** The objects are `BoxExpr.suml` and `BoxExpr.sum` (with simp lemmas `eval_suml`, `eval_sum`), `HasRationalFormula` (stated with `Set.EqOn` on `closedPeriodCell`), `spatialCoordinate` (with `spatialCoordinate_eval`), `slotLeftRat` and `slotRightRat` (with cast lemmas to the real `slotLeft`, `slotRight`), and the data-valued definition `scheduledPulse_jet : PeriodicJet 1 (scheduledPulse m i)`, obtained from `periodicPulse_jet` and the slot bounds $\frac14\le a_{m,i}<b_{m,i}\le\frac34$. Since `Fin m` is empty for $m=0$, the slot definitions only concern $m\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/RationalFormula.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/RationalFormula.lean by skeleton subtraction
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

namespace OAI

/-! SheetFlows rational formula. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

namespace BoxExpr

def suml : List BoxExpr → BoxExpr
  | [] => .const 0
  | e :: l => .add e (suml l)

@[simp] theorem eval_suml (l : List BoxExpr) (z : SpaceTime) :
    (suml l).eval z = (l.map (fun e => e.eval z)).sum := by
  induction l with
  | nil => simp [suml,eval]
  | cons e l ih => simp [suml,eval,ih]

def sum {ι : Type*} [Fintype ι] (f : ι → BoxExpr) : BoxExpr :=
  suml (Finset.univ.toList.map f)

@[simp] theorem eval_sum {ι : Type*} [Fintype ι] (f : ι → BoxExpr) (z : SpaceTime) :
    (sum f).eval z = ∑ i, (f i).eval z := by
  simp [sum, List.map_map, Function.comp_def]

end BoxExpr

def HasRationalFormula (u : Field) : Prop :=
  ∃ e : Fin 3 → BoxExpr,
    Set.EqOn (fun z => u z.1 z.2) (fun z => expressionField e z.1 z.2) closedPeriodCell

namespace HasRationalFormula

end HasRationalFormula

def spatialCoordinate (i : Fin 3) (e : JetExpr) : BoxExpr := .coord i.succ e

@[simp] theorem spatialCoordinate_eval (i : Fin 3) (e : JetExpr) (t : ℝ) (x : Space) :
    (spatialCoordinate i e).eval (t,x) = e.eval (x i) := by
  fin_cases i <;> rfl

def slotLeftRat (m : ℕ) (i : Fin m) : ℚ := 1/4 + (i:ℕ) / (2*m)
def slotRightRat (m : ℕ) (i : Fin m) : ℚ := slotLeftRat m i + 1/(4*m)

@[simp] theorem slotLeftRat_cast (m : ℕ) (i : Fin m) :
    (slotLeftRat m i : ℝ) = slotLeft m i := by
  simp [slotLeftRat,slotLeft]

@[simp] theorem slotRightRat_cast (m : ℕ) (i : Fin m) :
    (slotRightRat m i : ℝ) = slotRight m i := by
  simp [slotRightRat,slotRight]

def scheduledPulse_jet {m : ℕ} (i : Fin m) : PeriodicJet 1 (scheduledPulse m i) := by
  have hl : slotLeftRat m i < slotRightRat m i := by
    have hh : (slotLeftRat m i : ℝ) < slotRightRat m i := by
      simpa only [slotLeftRat_cast,slotRightRat_cast] using (slot_bounds i).2.1
    exact_mod_cast hh
  have ha : 0 ≤ slotLeftRat m i := by
    have := (slot_bounds i).1
    have : (0:ℝ) ≤ slotLeftRat m i := by rw [slotLeftRat_cast]; linarith
    exact_mod_cast this
  have hb : slotRightRat m i ≤ 1 := by
    have := (slot_bounds i).2.2
    have : (slotRightRat m i:ℝ) ≤ 1 := by rw [slotRightRat_cast]; linarith
    exact_mod_cast this
  simpa only [slotLeftRat_cast,slotRightRat_cast,scheduledPulse] using
    periodicPulse_jet (slotLeftRat m i) (slotRightRat m i) hl ha hb

end Solenoidal
end

end OAI


