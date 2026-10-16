-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EffectiveForcing
-- name    : OAI_MathematicalPhysics_SheetFlows_EffectiveForcing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:30:49.837798+00:00
-- url     : https://prove2.me/theorems/b0e29e90-049c-4914-9763-6c1a69a584cb
-- title:
--   Ball oracles and precision search for evaluating derivatives of a field to rational accuracy
-- statement:
--   This file defines the algorithmic components of a procedure that approximates the mixed derivatives of a time-dependent vector field to any requested rational accuracy. Space-time points $z=(t,x)\in\mathbb{R}\times\mathbb{R}^3$ have coordinates $z_0=t$, $z_{i+1}=x_i$; for a field $u:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ and a list $\alpha=(j_1,\dots,j_k)$ of coordinate indices, $D^{\alpha}u=\partial_{j_1}\cdots\partial_{j_k}u$ denotes the mixed partial derivative (the last index acting first). A rational ball $(c,r)\in\mathbb{Q}^2$ contains $x\in\mathbb{R}$ if $|c-x|\le r$; balls are added componentwise and multiplied by $(c_1,r_1)\otimes(c_2,r_2)=(c_1c_2,\,|c_1|r_2+|c_2|r_1+r_1r_2)$. Programs are codes $c$ of partial recursive functions on $\mathbb{N}$, and a program *names* a real number (or a point) if its $n$-th output is a rational approximation within $2^{-n}$.
--
--   1. **Reading a program.** $\mathrm{read}_c(n)$ runs $c$ on input $n$ and decodes the output as an element of the required type (a default value if the output is not a valid code); it is undefined if $c$ does not halt.
--   2. **Precision search.** For $L,\varepsilon\in\mathbb{Q}$, $\mathrm{precision}(L,\varepsilon)$ is the least $n\in\mathbb{N}$ with $L\cdot2^{-n}<\varepsilon/2$, and is undefined if there is none.
--   3. **Ball vectors and oracles.** A ball vector is a triple $b=(b_0,b_1,b_2)$ of rational balls $b_j=(c_j,r_j)$; a rational point is $q\in\mathbb{Q}^4$; a jet request is a triple $(\alpha,q,n)$ consisting of a derivative list, a rational point and a precision; and a ball oracle is a partial function $A$ from jet requests to ball vectors. For a ball vector $b$, $\mathrm{radiusSum}(b)=r_0+r_1+r_2$, $\mathrm{centers}(b)=(c_0,c_1,c_2)\in\mathbb{Q}^3$, and the test $\mathrm{ballTest}_\varepsilon(b)$ holds iff $\mathrm{radiusSum}(b)<\varepsilon/2$.
--   4. **Improvement.** $\mathrm{improve}_A(\alpha,q,\varepsilon)$ searches for the least $n$ such that $A(\alpha,q,n)$ is defined and passes $\mathrm{ballTest}_\varepsilon$ while $A(\alpha,q,m)$ is defined and fails the test for every $m<n$, and returns $\mathrm{centers}\bigl(A(\alpha,q,n)\bigr)$.
--   5. **Jet evaluation.** Given rational derivative bounds $B$ (one rational number for each list $\alpha$), an oracle $A$, and a request $(\alpha,c,\varepsilon)$ in which the program $c$ names a space-time point, $\mathrm{evalJets}$ computes $n=\mathrm{precision}(L,\varepsilon)$ with $L=\sum_{j=0}^{3}B\bigl((j,\alpha)\bigr)$, reads the rational point $q=\mathrm{read}_c(n)$, and returns $\mathrm{improve}_A(\alpha,q,\varepsilon)$.
--   6. **Oracle correctness.** $A$ is correct for $u$ if for every $\alpha$ and every $q\in\mathbb{Q}^4$ there are ball vectors $b(n)\in A(\alpha,q,n)$, $n\in\mathbb{N}$, such that for each $j\in\{0,1,2\}$ every ball $b(n)_j$ contains the $j$-th component of $D^{\alpha}u(\hat q)$ and the radii of $b(n)_j$ tend to $0$; here $\hat q=(q_0,(q_1,q_2,q_3))$ is the space-time point with coordinates $q$.
--   7. **Linear combinations.** $\mathrm{realBall}_c(n)=\bigl(\mathrm{read}_c(n),\,2^{-n}\bigr)$ is the $n$-th ball of a program naming a real number; $\mathrm{linearBalls}(r,a,b)_j=a_j+r\otimes b_j$; $\mathrm{linearOracle}(c,A,B)$ answers a request $p=(\alpha,q,n)$ with $\mathrm{linearBalls}\bigl(\mathrm{realBall}_c(n),A(p),B(p)\bigr)$; and $\mathrm{linearBound}(M,B,C)(\alpha)=B(\alpha)+M\,C(\alpha)$.
--
--   The design is the standard one of computable analysis. If $|D^{(j,\alpha)}u|\le B((j,\alpha))$ everywhere, then $L$ is a Lipschitz constant for $D^{\alpha}u$, so replacing the named point by its rational approximation $q$ at precision $n$ changes $D^{\alpha}u$ by less than $\varepsilon/2$; the centers returned by the improvement step lie within $\varepsilon/2$ of $D^{\alpha}u(\hat q)$; so the output is within $\varepsilon$ of the true derivative. The linear-combination tools handle fields of the form $u+r\,v$ with a computable real $r$, as needed for a forcing of the form $\partial_tu-\nu\,\Delta u$ with a computable viscosity $\nu$.
--
--   **Formalization Note** The definitions are `readCode`, `precision` (via `Nat.rfind`), the abbreviations `BallVector`, `RationalPoint`, `JetRequest`, `BallOracle` (a partial function `JetRequest →. BallVector`), `radiusSum`, `centers`, `ballTest`, `improve`, `evalJets`, `OracleCorrect`, `realBall`, `linearBalls`, `linearOracle` and `linearBound`. Partial results are values of type `Part`. In `evalJets` the point name is a `Nat.Partrec.Code` whose outputs are decoded as elements of `Fin 4 → ℚ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/EffectiveForcing.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/EffectiveForcing.lean by skeleton subtraction
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
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalBalls
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Computing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Circuits
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_CircuitPrograms

namespace OAI

/-! SheetFlows effective forcing. -/

section
open Set Filter Encodable
open scoped BigOperators Topology
namespace Solenoidal
namespace Computing

def readCode {α : Type*} [Primcodable α] [Inhabited α] (c : Nat.Partrec.Code) (n : ℕ) : Part α :=
  (c.eval n).map (fun k => (decode k).getD default)

def precision (L ε : ℚ) : Part ℕ :=
  Nat.rfind (fun n => Part.some (decide (L*(1/2:ℚ)^n < ε/2)))

abbrev BallVector := Fin 3 → QBall
abbrev RationalPoint := Fin 4 → ℚ
abbrev JetRequest := List (Fin 4) × RationalPoint × ℕ
abbrev BallOracle := JetRequest →. BallVector

def radiusSum (b : BallVector) : ℚ := ∑ j, (b j).2

def centers (b : BallVector) : Fin 3 → ℚ := fun j => (b j).1

def ballTest (ε : ℚ) (b : BallVector) : Bool := decide (radiusSum b < ε/2)

def improve (A : BallOracle) (p : List (Fin 4) × RationalPoint × ℚ) : Part (Fin 3 → ℚ) :=
  (Nat.rfind (fun n => (A (p.1,p.2.1,n)).map (ballTest p.2.2))).bind fun n =>
    (A (p.1,p.2.1,n)).map centers

def evalJets (B : List (Fin 4) → ℚ) (A : BallOracle)
    (p : List (Fin 4) × Nat.Partrec.Code × ℚ) : Part (Fin 3 → ℚ) :=
  (precision (jetLipschitz B p.1) p.2.2).bind fun n =>
    (readCode p.2.1 n).bind fun q => improve A (p.1,q,p.2.2)

end Computing
end Solenoidal
end

section
open Set Filter Encodable
open scoped BigOperators Topology
namespace Solenoidal
namespace Computing

def OracleCorrect (A : BallOracle) (u : Field) : Prop := ∀ a q,
  ∃ b : ℕ → BallVector, (∀ n, b n ∈ A (a,q,n)) ∧
    ∀ j, QBall.Approximates (fun n => b n j) (mixedDerivative u a (Circuit.ofRational q) j)

end Computing

end Solenoidal
end

open Set Filter Encodable
open scoped BigOperators Topology
namespace Solenoidal

namespace Computing

def realBall (c : Nat.Partrec.Code) (n : ℕ) : Part QBall :=
  (@readCode ℚ _ _ c n).map (fun q => (q,(1/2:ℚ)^n))

def linearBalls (r : QBall) (a b : BallVector) : BallVector := fun j => (a j).add (r.mul (b j))

def linearOracle (c : Nat.Partrec.Code) (A B : BallOracle) (p : JetRequest) : Part BallVector :=
  (realBall c p.2.2).bind fun r => (A p).bind fun a =>
    (B p).map (linearBalls r a)

end Computing

def linearBound (M : ℚ) (B C : List (Fin 4) → ℚ) (a : List (Fin 4)) : ℚ := B a + M * C a

end Solenoidal

end OAI


