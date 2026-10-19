-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
-- name    : OAI_Combinatorics_Hamiltonian_Network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:17:31.105969+00:00
-- url     : https://prove2.me/theorems/bd8771fe-9c79-48e4-9d23-4f79f758b7ef
-- title:
--   Oriented networks, gradient and boundary operators, and algebraic duality of two networks
-- statement:
--   This file sets up the linear-algebraic language for oriented graphs. An **oriented network** $N$ with vertex set $V$ and edge set $E$ consists of two maps $t_N, h_N : E \to V$ giving every edge $e$ a tail $t_N(e)$ and a head $h_N(e)$; loops and parallel edges are allowed. Write $[P]$ for $1$ if the statement $P$ holds and $0$ otherwise.
--
--   1. **Underlying graph.** $G(N)$ is the simple graph on $V$ in which two vertices $v \neq w$ are adjacent when some edge $e$ satisfies $\{t_N(e), h_N(e)\} = \{v, w\}$ (in either orientation). Loops are ignored and parallel edges are merged.
--
--   2. **Gradient.** The linear map $\nabla_N : \mathbb{R}^V \to \mathbb{R}^E$ given by
--   $$
--   (\nabla_N f)(e) = f(h_N(e)) - f(t_N(e)).
--   $$
--   It vanishes on constant functions. A companion linear map $\mathbb{R} \to \mathbb{R}^V$ sends $a$ to the constant function with value $a$.
--
--   3. **Incidence matrix and boundary.** For finite $V$ and $E$, the incidence matrix is the $V \times E$ matrix $B_N(v,e) = [h_N(e) = v] - [t_N(e) = v]$ (a loop gives a zero column), and the boundary operator is the linear map $\partial_N : \mathbb{R}^E \to \mathbb{R}^V$ with matrix $B_N$:
--   $$
--   (\partial_N x)(v) = \sum_{e:\ h_N(e) = v} x_e \;-\; \sum_{e:\ t_N(e) = v} x_e ,
--   $$
--   the net inflow of the edge function $x$ at $v$. The elements of $\ker \partial_N$ are the flows (circulations) of $N$, and $\partial_N$ is the transpose of $\nabla_N$: $\sum_{v} f(v)\,(\partial_N x)(v) = \sum_{e} (\nabla_N f)(e)\, x_e$.
--
--   4. **Duality.** Let $D$ be a second network with finite vertex set $F$ and the *same* finite edge set $E$, with tail and head maps $t_D, h_D : E \to F$. Then $N$ and $D$ are in duality if
--   $$
--   G(N) \text{ and } G(D) \text{ are connected}, \qquad \ker \partial_N = \operatorname{im} \nabla_D, \qquad \ker \partial_D = \operatorname{im} \nabla_N ,
--   $$
--   that is, the flows of each network are exactly the gradients (potential differences) of functions on the vertices of the other one.
--
--   The duality condition is the algebraic form of plane duality: for a connected plane graph and its geometric dual, with every dual edge oriented consistently across its primal edge, the circulations of one graph are exactly the potential differences on the other. In the surrounding development a cubic plane graph is represented by such a dual pair, the vertices of $D$ playing the role of faces, and the later combinatorics of cuts, flow circuits, regions and charges is phrased through $\nabla$ and $\partial$.
--
--   **Formalization Note** `Network V E` is a structure with fields `tail` and `head`; `graph`, `gradient`, `constant`, `incidence` and `boundary` are the objects above, with `boundary` defined as `Matrix.toLin'` of the incidence matrix and the simp lemmas `gradient_apply`, `gradient_const`, `boundary_apply` recording the formulas. `Duality N D` is a `Prop`-valued structure with the four fields listed. Mathlib's notion of a connected graph includes nonemptiness of the vertex type, so duality forces $V$ and $F$ to be nonempty. Decidable equality on vertices and edges is supplied classically.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Network.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Network.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BarnetteHamiltonian mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BarnetteHamiltonian

namespace OAI

/-! Oriented finite networks, cycle and cut spaces, and graph realization. -/

namespace Barnette

structure Network (V E : Type*) where
  tail : E → V
  head : E → V

namespace Network
noncomputable section
variable {V E : Type*} (N : Network V E)

def graph : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ e, (N.tail e = v ∧ N.head e = w) ∨
    (N.tail e = w ∧ N.head e = v)
  symm := ⟨by rintro v w ⟨h, e, hi⟩; exact ⟨h.symm, e, hi.symm⟩⟩
  loopless := ⟨fun v h => h.1 rfl⟩

def gradient : (V → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun f e := f (N.head e) - f (N.tail e)
  map_add' f g := by ext e; dsimp; ring
  map_smul' c f := by ext e; dsimp; ring

@[simp] theorem gradient_apply (f : V → ℝ) (e : E) :
    N.gradient f e = f (N.head e) - f (N.tail e) := rfl

@[simp] theorem gradient_const (a : ℝ) : N.gradient (fun _ => a) = 0 := by
  ext e; simp

def constant : ℝ →ₗ[ℝ] (V → ℝ) where
  toFun a _ := a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [Fintype V] [Fintype E]
local instance instDecidableEq : DecidableEq V := Classical.decEq _
local instance instDecidableEq_1 : DecidableEq E := Classical.decEq _

def incidence : Matrix V E ℝ := fun v e =>
  (if N.head e = v then 1 else 0) - (if N.tail e = v then 1 else 0)

def boundary : (E → ℝ) →ₗ[ℝ] (V → ℝ) := Matrix.toLin' N.incidence

omit [Fintype V] in
@[simp] theorem boundary_apply (x : E → ℝ) (v : V) :
    N.boundary x v = ∑ e, ((if N.head e = v then x e else 0) -
      (if N.tail e = v then x e else 0)) := by
  classical
  simp [boundary, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, incidence,
    sub_mul, ite_mul]

variable {F : Type*} [Fintype F] (D : Network F E)

structure Duality : Prop where
  connected : N.graph.Connected
  dual_connected : D.graph.Connected
  cycles_eq_cuts : N.boundary.ker = D.gradient.range
  dual_cycles_eq_cuts : D.boundary.ker = N.gradient.range

end
end Network
end Barnette

namespace Barnette
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj]

end
end Barnette

end OAI


