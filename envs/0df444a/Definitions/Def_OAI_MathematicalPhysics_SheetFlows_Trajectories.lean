-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories
-- name    : OAI_MathematicalPhysics_SheetFlows_Trajectories
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:02:15.283261+00:00
-- url     : https://prove2.me/theorems/0891e9ec-f6fb-4cce-82b8-dfcfb272c59e
-- title:
--   Staged displacement maps and the piecewise straight particle paths of a pulse schedule
-- statement:
--   Let $m\in\mathbb{N}$ and let $v_0,\dots,v_{m-1}:\mathbb{R}^3\to\mathbb{R}^3$ be stationary vector fields. Let $\psi$ be the standard smooth transition function ($C^\infty$, equal to $0$ on $(-\infty,0]$ and to $1$ on $[1,\infty)$), let $\theta_{a,b}(t)=\psi\bigl((t-a)/(b-a)\bigr)$ be the smooth clock that switches from $0$ to $1$ during $[a,b]$, and let $[\ell_i,r_i]$ be the time slots $\ell_i=\frac14+\frac{i}{2m}$, $r_i=\ell_i+\frac1{4m}$ for $i<m$. Points of $\mathbb{R}^3$ are $x=(x_0,x_1,x_2)$ with standard basis $e_0,e_1,e_2$.
--
--   1. **Stage fields.** $\tilde v_n=v_n$ for $n<m$ and $\tilde v_n=0$ for $n\ge m$.
--   2. **Stage states.** For a starting point $a\in\mathbb{R}^3$,
--   $$
--   a_0=a,\qquad a_{n+1}=a_n+\tilde v_n(a_n)\quad(n\in\mathbb{N}),
--   $$
--   so the displacement maps $x\mapsto x+v_0(x)$, $x\mapsto x+v_1(x)$, and so on, are applied in turn, and $a_n=a_m$ for $n\ge m$.
--   3. **Stage increments.** $\Delta_i(a)=v_i(a_i)$ for $i<m$, so that $a_{i+1}=a_i+\Delta_i(a)$.
--   4. **Launch path.** For $t\in\mathbb{R}$,
--   $$
--   \Lambda(a,t)=a+\sum_{i=0}^{m-1}\theta_{\ell_i,r_i}(t)\,\Delta_i(a).
--   $$
--   5. **Straight invariance.** A field $w:\mathbb{R}^3\to\mathbb{R}^3$ is straight invariant if $w\bigl(x+c\,w(x)\bigr)=w(x)$ for all $x\in\mathbb{R}^3$ and $c\in\mathbb{R}$, i.e. $w$ is constant along each of its own straight lines. For every $i\in\{0,1,2\}$ and every function $g:\mathbb{R}^3\to\mathbb{R}$, the axial field $x\mapsto g(x-x_ie_i)\,e_i$ is straight invariant.
--   6. **Period states.** $b_0=a$ and $b_{n+1}=(b_n)_m$, the state reached after all $m$ stages when starting from $b_n$.
--   7. **Repeated path.**
--   $$
--   X(t,a)=\Lambda\bigl(b_{\lfloor t\rfloor},\ t-\lfloor t\rfloor\bigr),
--   $$
--   where $\lfloor t\rfloor$ is the integer part of $t$ for $t\ge0$ and is taken to be $0$ for $t<0$.
--
--   Since the slots are ordered and disjoint, during the $i$-th slot all earlier clocks equal $1$ and all later ones equal $0$; hence $\Lambda(a,\cdot)$ rests at $a$ for $t\le\frac14$, moves along the straight segment from $a_i$ to $a_{i+1}$ during $[\ell_i,r_i]$, and rests at $a_m$ for $t\ge\frac34$. For straight-invariant fields $v_i$ the velocity along this segment is a time weight times $v_i$ evaluated at the moving point, so $X$ is the flow of the scheduled velocity $\sum_i\sigma_i(t)\,v_i(x)$, where $\sigma_i$ is the $1$-periodized derivative of $\theta_{\ell_i,r_i}$, and its time-one map is $a\mapsto a_m$, the composition of the displacement maps. This reduces the design of a fluid flow with a prescribed time-one map to composing explicit maps $x\mapsto x+v_i(x)$.
--
--   **Formalization Note** The objects are `stageField` (with the simp lemma `stageField_fin`), `stageState`, `stageIncrement`, `launchPath`, `StraightInvariant`, `periodState` and `repeatedPath`; the floor is the natural-number floor `⌊t⌋₊`. The invariance of axial fields is `axialField_straightInvariant`, stated for the time-$0$ slice of `axialField i (fun _ => g)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/Trajectories.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Trajectories.lean by skeleton subtraction
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

namespace OAI

/-! SheetFlows trajectories. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

def stageField {m : ℕ} (v : Fin m → Space → Space) (n : ℕ) : Space → Space :=
  if h : n < m then v ⟨n, h⟩ else 0

def stageState {m : ℕ} (v : Fin m → Space → Space) (a : Space) : ℕ → Space
  | 0 => a
  | n + 1 => stageState v a n + stageField v n (stageState v a n)

def stageIncrement {m : ℕ} (v : Fin m → Space → Space) (a : Space) (i : Fin m) : Space :=
  v i (stageState v a i.val)

@[simp] theorem stageField_fin {m : ℕ} (v : Fin m → Space → Space) (i : Fin m) :
    stageField v i.val = v i := by simp [stageField, i.isLt]

def launchPath {m : ℕ} (v : Fin m → Space → Space) (a : Space) (t : ℝ) : Space :=
  a + ∑ i : Fin m, pulseClock (slotLeft m i) (slotRight m i) t • stageIncrement v a i

def StraightInvariant (v : Space → Space) : Prop :=
  ∀ (x : Space) (c : ℝ), v (x + c • v x) = v x

theorem axialField_straightInvariant (i : Fin 3) (g : Space → ℝ) :
    StraightInvariant (axialField i (fun _ => g) 0) := by
  intro x c
  simp only [axialField, map_add, map_smul, eraseAxis_basis, smul_zero, add_zero]

def periodState {m : ℕ} (v : Fin m → Space → Space) (a : Space) : ℕ → Space
  | 0 => a
  | n + 1 => stageState v (periodState v a n) m

def repeatedPath {m : ℕ} (v : Fin m → Space → Space) (a : Space) (t : ℝ) : Space :=
  launchPath v (periodState v a ⌊t⌋₊) (t - (⌊t⌋₊ : ℝ))

end Solenoidal

end

end OAI


