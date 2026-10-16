-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalBalls
-- name    : OAI_MathematicalPhysics_SheetFlows_RationalBalls
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:22:38.583587+00:00
-- url     : https://prove2.me/theorems/93009fb7-5fc5-438c-bd8e-dc97201ce8cf
-- title:
--   Rational ball arithmetic with enclosures of exponentials and flat functions
-- statement:
--   This file sets up exact interval ("ball") arithmetic over $\mathbb{Q}$, used to evaluate certain smooth functions to any prescribed accuracy with rational computations only. A *rational ball* is a pair $a=(c,r)\in\mathbb{Q}\times\mathbb{Q}$ with center $c$ and radius $r$. Write $\psi(s)=e^{-1/s}$ for $s>0$ and $\psi(s)=0$ for $s\le0$, and $F_m(s)=s^{-m}\psi(s)$ for $s>0$, $F_m(s)=0$ for $s\le 0$.
--
--   1. **Containment.** $a=(c,r)$ contains $x\in\mathbb{R}$ if $|c-x|\le r$.
--   2. **Operations.** $\mathrm{point}(q)=(q,0)$, which contains $q$; $(c_1,r_1)+(c_2,r_2)=(c_1+c_2,\ r_1+r_2)$;
--   $$(c_1,r_1)\otimes(c_2,r_2)=\bigl(c_1c_2,\ |c_1|\,r_2+|c_2|\,r_1+r_1r_2\bigr);$$
--   and powers $a^{0}=\mathrm{point}(1)$, $a^{n+1}=a^{n}\otimes a$.
--   3. **Approximating sequences.** A sequence of balls $(A_n)_{n\in\mathbb{N}}$ approximates $x\in\mathbb{R}$ if every $A_n$ contains $x$ and the radii of $A_n$ tend to $0$ as $n\to\infty$.
--   4. **Exponential.** $\mathrm{taylor}(q,n)=\sum_{m=0}^{n-1}q^m/m!$; $\mathrm{smallExp}(q,n)=\bigl(\mathrm{taylor}(q,n+1),\ 2\cdot 2^{-(n+1)}\bigr)$, a ball for $e^{q}$ intended for $|q|\le\frac12$; $K(q)=2\bigl(|\mathrm{num}(q)|+1\bigr)$, where $\mathrm{num}(q)$ is the numerator of $q$ in lowest terms; and
--   $$\mathrm{expApprox}(q,n)=\mathrm{smallExp}\bigl(q/K(q),\,n\bigr)^{K(q)},$$
--   which encloses $e^{q}=\bigl(e^{q/K(q)}\bigr)^{K(q)}$ using that $|q/K(q)|\le\frac12$.
--   5. **Clamped reciprocal.** $\mathrm{clampInv}(c,r)=\bigl(1/\max(\tfrac1{32},c),\ 512\,r\bigr)$, a ball for $1/x$ intended for arguments $x$ bounded below.
--   6. **Flat functions.** For $m\in\mathbb{N}$, $\mathrm{flatApprox}(m,q,n)=\mathrm{point}(0)$ if $q\le0$, and $\mathrm{flatApprox}(m,q,n)=\mathrm{point}(q^{-m})\otimes\mathrm{expApprox}(-1/q,\,n)$ if $q>0$; a ball for $F_m(q)$.
--   7. **Transition reciprocal.** $\mathrm{reciprocalApprox}(q,n)=\mathrm{clampInv}\bigl(\mathrm{flatApprox}(0,q,n)+\mathrm{flatApprox}(0,1-q,n)\bigr)$, a ball for $1/\bigl(\psi(q)+\psi(1-q)\bigr)$.
--
--   Ball addition and multiplication are the rational counterparts of real addition and multiplication: if $a$ contains $x$ and $b$ contains $y$, then $a+b$ contains $x+y$ and $a\otimes b$ contains $xy$. Together with the enclosures of $e^{q}$, of the flat functions $F_m$ and of $1/(\psi(s)+\psi(1-s))$, they allow the atoms of the arithmetic circuits that describe the forcing field to be evaluated at rational points with rigorous error bars that shrink with the precision parameter $n$.
--
--   **Formalization Note** `QBall` is the abbreviation `ℚ × ℚ`, and the definitions `Contains`, `point`, `add`, `mul`, `pow`, `Approximates` (a structure with fields `contains` and `radius`, the latter a `Tendsto` statement), `taylor`, `smallExp`, `expScale` (this is $K$), `expApprox`, `clampInv`, `flatApprox`, `reciprocalApprox` live in the namespace `QBall`. The only lemma in the file is `point_contains`. The type does not force radii to be nonnegative; containment of some real number does.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/RationalBalls.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/RationalBalls.lean by skeleton subtraction
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
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_FormulaProfiles

namespace OAI

/-! SheetFlows rational balls. -/

section
open Set Filter
open scoped Topology BigOperators
namespace Solenoidal

abbrev QBall := ℚ × ℚ

namespace QBall

def Contains (a : QBall) (x : ℝ) : Prop := |(a.1:ℝ)-x| ≤ (a.2:ℝ)

def point (q : ℚ) : QBall := (q,0)
def add (a b : QBall) : QBall := (a.1+b.1,a.2+b.2)
def mul (a b : QBall) : QBall :=
  (a.1*b.1, |a.1| *b.2 + |b.1| *a.2 + a.2*b.2)
def pow (a : QBall) : ℕ → QBall
  | 0 => point 1
  | n+1 => mul (pow a n) a

@[simp] theorem point_contains (q : ℚ) : (point q).Contains (q:ℝ) := by
  simp [Contains,point]

structure Approximates (A : ℕ → QBall) (x : ℝ) : Prop where
  contains : ∀ n, (A n).Contains x
  radius : Tendsto (fun n => ((A n).2:ℝ)) atTop (𝓝 0)

def taylor (q : ℚ) (n : ℕ) : ℚ := ∑ m ∈ Finset.range n, q^m / (m.factorial:ℚ)

def smallExp (q : ℚ) (n : ℕ) : QBall :=
  (taylor q (n+1), 2*(1/2:ℚ)^(n+1))

def expScale (q : ℚ) : ℕ := 2 * (q.num.natAbs+1)
def expApprox (q : ℚ) (n : ℕ) : QBall :=
  pow (smallExp (q / (expScale q:ℚ)) n) (expScale q)

def clampInv (a : QBall) : QBall := ((max (1/32) a.1)⁻¹,512*a.2)

def flatApprox (m : ℕ) (q : ℚ) (n : ℕ) : QBall :=
  if q ≤ 0 then point 0 else
    mul (point (q⁻¹^m)) (expApprox (-q⁻¹) n)

def reciprocalApprox (q : ℚ) (n : ℕ) : QBall :=
  clampInv (add (flatApprox 0 q n) (flatApprox 0 (1-q) n))

end QBall
end Solenoidal
end

end OAI


