-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
-- name    : OAI_MathematicalPhysics_SheetFlows_Differential
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T00:56:26.814978+00:00
-- url     : https://prove2.me/theorems/88109714-c043-4228-9cb2-ee659962f2e5
-- title:
--   Scheduled velocity fields, space–time directional derivatives and the global direct force
-- statement:
--   Points of $\mathbb{R}^3$ are $x=(x_0,x_1,x_2)$ with standard basis $e_0,e_1,e_2$; a vector field is a map $u:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$, with spatial partial derivatives $\partial_ju(t,x)=D_xu(t,x)[e_j]$ and Laplacian $\Delta u=\sum_{j=0}^{2}\partial_j\partial_ju$. Let $\psi$ be the standard smooth transition function ($C^\infty$, equal to $0$ on $(-\infty,0]$ and to $1$ on $[1,\infty)$). For $m\in\mathbb{N}$ and $i\in\{0,\dots,m-1\}$ let $\ell_{m,i}=\frac14+\frac{i}{2m}$, $r_{m,i}=\ell_{m,i}+\frac1{4m}$, let $\rho_{m,i}$ be the derivative of the clock $t\mapsto\psi\bigl((t-\ell_{m,i})/(r_{m,i}-\ell_{m,i})\bigr)$, and let $\sigma_{m,i}(t)=\sum_{k\in\mathbb{Z}}\rho_{m,i}(t-k)$ be its $1$-periodization (the scheduled time pulse of slot $i$).
--
--   1. **Scheduled velocity.** For stationary vector fields $v_0,\dots,v_{m-1}:\mathbb{R}^3\to\mathbb{R}^3$,
--   $$
--   U_v(t,x)=\sum_{i=0}^{m-1}\sigma_{m,i}(t)\,v_i(x).
--   $$
--   2. **Directional derivative.** For a map $g:E\to F$ between real normed spaces and a vector $w\in E$, $\partial_wg(x)=Dg(x)[w]$, the Fréchet derivative of $g$ at $x$ applied to $w$; for $g=0$ it is $0$.
--   3. **Two-sided time derivative.** $\dot u(t,x)=\frac{d}{dt}u(t,x)$, the ordinary derivative of $s\mapsto u(s,x)$ at $s=t$.
--   4. **Space–time directional derivative.** For $w\in\mathbb{R}\times\mathbb{R}^3$, $\partial_wu(t,x)=Du(t,x)[w]$, where $u$ is regarded as a map on $\mathbb{R}\times\mathbb{R}^3$ and $D$ denotes its full space–time Fréchet derivative.
--   5. **Global direct force.** For $\nu\in\mathbb{R}$,
--   $$
--   f_{\nu,u}(t,x)=\dot u(t,x)-\nu\,\Delta u(t,x).
--   $$
--
--   $U_v$ is the velocity field of an explicit Navier–Stokes flow construction: each stationary field $v_i$ acts only during its own slot of every unit time interval, with smooth time weight $\sigma_{m,i}$. The force $f_{\nu,u}$ is the forcing for which a divergence-free field $u$ with vanishing advection term solves the forced Navier–Stokes equations with zero pressure. In contrast with the one-sided time derivative (within $[0,\infty)$) used in the notion of classical solution, $\dot u$ is the two-sided derivative, so for smooth $u$ the force is defined and smooth for all real times and is $1$-periodic in time whenever $u$ is. The space–time directional derivative is the tool for handling mixed space–time derivatives of smooth fields.
--
--   **Formalization Note** The objects are `scheduleVelocity`, `directional` (with the simp lemma `directional_zero`), `fullTimePartial` (Lean's `deriv`, which is $0$ where the derivative does not exist), `fieldDirectional` (`directional` applied to `Function.uncurry u` at `(t, x)`) and `globalDirectForce`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/Differential.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Differential.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SolenoidalSheetPrograms mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks

namespace OAI

/-! SheetFlows differential. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

def scheduleVelocity {m : ℕ} (v : Fin m → Space → Space) : Field :=
  fun t x => ∑ i, scheduledPulse m i t • v i x

section DirectionalCalculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def directional (g : E → F) (v : E) : E → F := fun x => fderiv ℝ g x v

@[simp] theorem directional_zero (v : E) : directional (0 : E → F) v = 0 := by
  funext x
  simp [directional]

end DirectionalCalculus

def fullTimePartial (u : Field) : Field := fun t x => deriv (fun s => u s x) t

def fieldDirectional (u : Field) (v : SpaceTime) : Field :=
  fun t x => directional (Function.uncurry u) v (t, x)

def globalDirectForce (ν : ℝ) (u : Field) : Field :=
  fun t x => fullTimePartial u t x - ν • laplacian u t x

end Solenoidal
end

end OAI


