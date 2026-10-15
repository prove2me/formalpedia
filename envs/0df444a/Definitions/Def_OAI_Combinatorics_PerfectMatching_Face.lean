-- Prove2me | Definitions.Def_OAI_Combinatorics_PerfectMatching_Face
-- name    : OAI_Combinatorics_PerfectMatching_Face
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:54:14.412046+00:00
-- url     : https://prove2.me/theorems/3b2bc133-ca83-418d-9820-f6d7940c840b
-- title:
--   Active face space and face codimension at a point of the matching constraint system
-- statement:
--   Let $G$ be a loopless multigraph with finite vertex set $V$ and finite edge set $E$. For $x\in\mathbb{R}^E$ let $E_+(x)=\{e\in E: x_e>0\}$ be its positive support, and use the degrees $\deg_x(v)$ and cut masses $x(\delta(S))$ of edge vectors.
--
--   1. *Extension by zero.* $\iota_x:\mathbb{R}^{E_+(x)}\to\mathbb{R}^E$ is the linear map with $(\iota_x u)_e=u_e$ if $x_e>0$ and $(\iota_x u)_e=0$ otherwise.
--   2. *Degree and cut maps.* The degree map $\mathbb{R}^E\to\mathbb{R}^V$, $z\mapsto(\deg_z(v))_{v\in V}$, and for each $S\subseteq V$ the cut functional $z\mapsto z(\delta(S))$ are linear.
--   3. *Face space.* $F_x\subseteq\mathbb{R}^{E_+(x)}$ is the subspace of all $u$ such that
--   $$
--   \deg_{\iota_x u}(v)=0\ \ \text{for all }v\in V,\qquad (\iota_x u)\big(\delta(S)\big)=0\ \ \text{for all }S\subseteq V\text{ with }|S|\text{ odd and }x\big(\delta(S)\big)=1 .
--   $$
--   4. *Face codimension.* $\operatorname{codim}(x)=\dim\big(\mathbb{R}^{E_+(x)}/F_x\big)=|E_+(x)|-\dim F_x$.
--   5. *Side marginal and side restriction.* For $S\subseteq V$, the side marginal $x^S$ is the restriction of $x$ to the edges having an endpoint in $S$, which are the edges of the graph obtained by contracting $V\setminus S$. The side restriction is the linear map $\mathbb{R}^{E_+(x)}\to\mathbb{R}^{E_+(x^S)}$ that restricts a vector on the positive edges of $x$ to those positive edges with an endpoint in $S$.
--
--   The face space consists of the directions supported on the positive edges of $x$ that preserve every degree constraint and every odd-cut constraint that is tight at $x$. They keep every constraint that is active at $x$ active and leave the zero coordinates of $x$ untouched, so for $x$ in the constraint system, small movements along them in either sense stay inside it. A bound on the face codimension in terms of $|V|$ therefore gives a lower bound on the dimension of the space of such two-sided directions at $x$. In the entropy argument this becomes a lower bound on the rank of the covariance matrix of a maximum-entropy law on perfect matchings with marginal $x$.
--
--   **Formalization Note** The names are `positiveExtension`, `degreeLinear`, `cutLinear`, `faceSpace`, `faceCodimension` (via `Module.finrank` of the quotient), `sideMarginal` and `sideRestriction`. The simp lemmas `positiveExtension_pos` and `positiveExtension_zero` evaluate the extension. Odd sets are `Finset V` of odd cardinality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Face.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Face.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingEntropy mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Polytope

namespace OAI

/-!
Active face spaces, their codimension bounds, and local radial extension.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

/-- Restrict the ambient vector space to the genuinely positive edge coordinates. -/
def positiveExtension (x : E → ℝ) : ({e // 0<x e} → ℝ) →ₗ[ℝ] (E → ℝ) := by
  classical
  exact {
    toFun := fun u e => if h : 0<x e then u ⟨e,h⟩ else 0
    map_add' := by intro u v; ext e; by_cases h : 0<x e <;> simp [h]
    map_smul' := by intro a u; ext e; by_cases h : 0<x e <;> simp [h] }

omit [Fintype E] [DecidableEq E] in
@[simp] theorem positiveExtension_pos (x : E → ℝ) (u : {e // 0<x e} → ℝ)
    (e : {e // 0<x e}) : positiveExtension x u e.val=u e := by
  simp [positiveExtension,e.property]

omit [Fintype E] [DecidableEq E] in
@[simp] theorem positiveExtension_zero (x : E → ℝ) (u : {e // 0<x e} → ℝ)
    {e : E} (he : x e=0) : positiveExtension x u e=0 := by
  simp [positiveExtension,he]

def degreeLinear (G : LooplessGraph V E) : (E → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun := G.degree
  map_add' := by
    intro u v
    ext w
    simpa using G.degree_linear u v 1 1 w
  map_smul' := by
    intro a u
    ext w
    simp only [degree,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    split <;> simp

def cutLinear (G : LooplessGraph V E) (S : Finset V) : (E → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun u => G.cutMass u S
  map_add' := by intro u v; simpa using G.cutMass_linear u v 1 1 S
  map_smul' := by intro a u; simp [cutMass,Finset.mul_sum]

/-- The exact active degree and odd-cut kernel, on the positive edge support. -/
def faceSpace (G : LooplessGraph V E) (x : E → ℝ) : Submodule ℝ ({e // 0<x e} → ℝ) where
  carrier := {u | G.degreeLinear (positiveExtension x u)=0 ∧
    ∀ S : Finset V, Odd S.card → G.cutMass x S=1 → G.cutLinear S (positiveExtension x u)=0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    refine ⟨by simp only [map_add,hu.1,hv.1,add_zero],?_⟩
    intro S hS ht
    simp only [map_add,hu.2 S hS ht,hv.2 S hS ht,add_zero]
  smul_mem' := by
    intro a u hu
    refine ⟨by simp only [map_smul,hu.1,smul_zero],?_⟩
    intro S hS ht
    simp only [map_smul,hu.2 S hS ht,smul_zero]

def faceCodimension (G : LooplessGraph V E) (x : E → ℝ) : ℕ :=
  Module.finrank ℝ (({e // 0<x e} → ℝ) ⧸ G.faceSpace x)

abbrev sideMarginal (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) :
    {e // G.left e ∈ S ∨ G.right e ∈ S} → ℝ := fun e => x e.val

def sideRestriction (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) :
    ({e // 0<x e} → ℝ) →ₗ[ℝ] ({e // 0<G.sideMarginal x S e} → ℝ) where
  toFun := fun u e => u ⟨e.val.val,e.property⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

end LooplessGraph

end MatchingEntropy

end

end OAI


