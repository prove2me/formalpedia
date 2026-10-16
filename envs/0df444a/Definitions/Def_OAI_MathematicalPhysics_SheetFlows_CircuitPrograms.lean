-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_CircuitPrograms
-- name    : OAI_MathematicalPhysics_SheetFlows_CircuitPrograms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:29:34.713306+00:00
-- url     : https://prove2.me/theorems/1c788499-800f-424d-8d4a-8c932b152c50
-- title:
--   Circuit representations of fields and periodic evaluation of their derivatives
-- statement:
--   This file packages arithmetic circuits into the data needed to evaluate a periodic field and its derivatives. Space-time points are $z=(t,x)\in\mathbb{R}\times\mathbb{R}^3$, with coordinates $z_0=t$ and $z_{i+1}=x_i$. Here a *circuit* is a formal arithmetic expression on space-time built from rational constants, sums, products and atoms $P_k(az_j+b)$ with $a,b\in\mathbb{Q}$, whose profiles $P_k$ are the identity, the function $1/(\psi(s)+\psi(1-s))$, or the flat monomials $s^{-m}\psi(s)$, where $\psi(s)=e^{-1/s}$ for $s>0$ and $\psi(s)=0$ for $s\le0$. Each circuit $C$ has a real value $C(z)$, a rational magnitude bound $\mathrm{bound}(C,\rho)$ designed for points whose coordinates satisfy $|z_j|\le\rho$, rational ball approximations $\mathrm{approx}(C,q,n)$ at rational points $q\in\mathbb{Q}^4$ with precision parameter $n$ (a rational ball $(c,r)$ standing for $[c-r,c+r]$), and symbolic mixed derivatives $\partial^{\alpha}C$ for lists $\alpha=(j_1,\dots,j_k)$ of coordinate indices.
--
--   1. **Circuit representation.** A time-dependent vector field $u:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ *has a circuit* if there are circuits $C_0,C_1,C_2$ with
--   $$u(t,x)=\bigl(C_0(t,x),C_1(t,x),C_2(t,x)\bigr)\qquad\text{for all }(t,x)\in[0,1]\times[0,10]^3 .$$
--   2. **Jet bound.** For circuits $C=(C_0,C_1,C_2)$ and a list $\alpha$,
--   $$\mathrm{jetBound}(C,\alpha)=\sum_{j=0}^{2}\mathrm{bound}\bigl(\partial^{\alpha}C_j,\,10\bigr)\in\mathbb{Q},$$
--   a bound for the $\alpha$-th mixed derivative of the circuit field at points all of whose coordinates lie in $[-10,10]$, a region containing the period cell $[0,1]\times[0,10]^3$.
--   3. **Wrapping into the period cell.** For $q\in\mathbb{Q}^4$, $\mathrm{wrap}(q)_j=T_j\,\{q_j/T_j\}$ with $T_0=1$ and $T_1=T_2=T_3=10$, where $\{y\}=y-\lfloor y\rfloor$ is the fractional part; thus the time coordinate is reduced modulo $1$ and the spatial coordinates modulo $10$.
--   4. **Jet approximation.** $\mathrm{jetApprox}(C,\alpha,q,n)$ is the triple of rational balls $\bigl(\mathrm{approx}(\partial^{\alpha}C_j,\,\mathrm{wrap}(q),\,n)\bigr)_{j=0,1,2}$.
--   5. **Lipschitz bound.** For a function $B$ assigning a rational number to every list of coordinate indices,
--   $$\mathrm{jetLipschitz}(B,\alpha)=\sum_{j=0}^{3}B\bigl((j,\alpha)\bigr),$$
--   the sum of the bounds for the four mixed derivatives of one order higher; when $B$ bounds the mixed derivatives of a field everywhere, it serves as a Lipschitz constant for the $\alpha$-th mixed derivative with respect to the maximum norm.
--
--   For a smooth field that is $1$-periodic in time and $10$-periodic in each space direction and has a circuit, every mixed derivative at an arbitrary point equals the corresponding circuit derivative at the wrapped point. Jet bounds and jet approximations therefore provide, from finitely many symbols, the computable rational derivative bounds and the rational ball oracle from which the effectivity of such fields is derived.
--
--   **Formalization Note** The definitions are `HasCircuit` (stated with `Set.EqOn` on `closedPeriodCell` and `Circuit.field`), `Circuit.jetBound`, `Circuit.wrapRat` (using `Int.fract` on $\mathbb{Q}$), `Circuit.jetApprox` and `jetLipschitz`. The `Computing` namespace blocks in this file are empty after extraction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/CircuitPrograms.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/CircuitPrograms.lean by skeleton subtraction
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

namespace OAI

/-! SheetFlows circuit programs. -/

section
open Encodable Denumerable
namespace Solenoidal.Computing
open Nat.Partrec

end Solenoidal.Computing
end

open Set Filter Encodable
open scoped BigOperators Topology
namespace Solenoidal

def HasCircuit (u : Field) : Prop := ∃ e : Fin 3 → Circuit,
  Set.EqOn (fun z => u z.1 z.2) (fun z => Circuit.field e z.1 z.2) closedPeriodCell

namespace Circuit

def jetBound (e : Fin 3 → Circuit) (a : List (Fin 4)) : ℚ :=
  ∑ j, bound (mixed (e j) a) 10

def wrapRat (q : Fin 4 → ℚ) : Fin 4 → ℚ := fun j =>
  let T : ℚ := if j=0 then 1 else 10
  T * Int.fract (q j / T)

def jetApprox (e : Fin 3 → Circuit) (a : List (Fin 4)) (q : Fin 4 → ℚ) (n : ℕ) : Fin 3 → QBall :=
  fun j => approx (mixed (e j) a) (wrapRat q) n

end Circuit

namespace Computing

end Computing

def jetLipschitz (B : List (Fin 4) → ℚ) (a : List (Fin 4)) : ℚ :=
  ∑ j : Fin 4, B (j::a)

namespace Computing

end Computing
end Solenoidal

end OAI


