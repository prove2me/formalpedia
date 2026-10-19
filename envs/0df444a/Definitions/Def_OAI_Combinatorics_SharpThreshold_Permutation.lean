-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
-- name    : OAI_Combinatorics_SharpThreshold_Permutation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:13:53.220508+00:00
-- url     : https://prove2.me/theorems/2e840857-55a6-4c17-be03-18843d8f9c12
-- title:
--   Vertex permutations acting on edges and graph configurations
-- statement:
--   Fix $n$. An edge is a $2$-element subset of $\{0,\dots,n-1\}$, and a configuration $x$ assigns true or false to every edge, i.e. it is a graph on $n$ labelled vertices. Under the $p$-biased product measure each edge is present independently with probability $p$, so $x$ has weight $w_p(x)=\prod_ep^{[x_e]}(1-p)^{1-[x_e]}$, and $\mu_p(f)=\sum_xw_p(x)[f(x)]$ is the probability that a property $f$ holds. A vertex permutation $\pi$ maps an edge $e$ to $\pi(e)$ and acts on configurations by $(\pi x)_e=x_{\pi^{-1}(e)}$.
--
--   1. These are group actions: $\mathrm{id}$ acts trivially, $\pi(\rho\,e)=(\pi\rho)(e)$, and $\pi^{-1}$ undoes $\pi$; so $\pi$ induces a bijection of edges.
--   2. The biased weight is invariant, $w_p(\pi x)=w_p(x)$.
--   3. Updating an edge commutes with the action:
--   $$
--   \pi\bigl(x^{e\to b}\bigr)=(\pi x)^{\pi(e)\to b} .
--   $$
--
--   Hence for a vertex-invariant property all edges have the same influence.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/Permutation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/Permutation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SharpThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture

namespace OAI

noncomputable section
namespace Problem313

@[simp] theorem permEdge_refl {n : ℕ} (e : GraphEdge n) :
    permEdge (Equiv.refl _) e = e := by
  apply Subtype.ext
  simp [permEdge]

@[simp] theorem permEdge_permEdge {n : ℕ} (π ρ : Equiv.Perm (Fin n))
    (e : GraphEdge n) :
    permEdge π (permEdge ρ e) = permEdge (ρ.trans π) e := by
  apply Subtype.ext
  simp [permEdge, Finset.map_map]

@[simp] theorem permEdge_symm_permEdge {n : ℕ} (π : Equiv.Perm (Fin n))
    (e : GraphEdge n) : permEdge π.symm (permEdge π e) = e := by
  simp

@[simp] theorem permEdge_permEdge_symm {n : ℕ} (π : Equiv.Perm (Fin n))
    (e : GraphEdge n) : permEdge π (permEdge π.symm e) = e := by
  simp

def permEdgeEquiv {n : ℕ} (π : Equiv.Perm (Fin n)) : GraphEdge n ≃ GraphEdge n where
  toFun := permEdge π
  invFun := permEdge π.symm
  left_inv := permEdge_symm_permEdge π
  right_inv := permEdge_permEdge_symm π

@[simp] theorem permuteConfig_refl {n : ℕ} (x : GraphConfig n) :
    permuteConfig (Equiv.refl _) x = x := by
  funext e
  simp [permuteConfig]

@[simp] theorem permuteConfig_perm {n : ℕ} (π ρ : Equiv.Perm (Fin n))
    (x : GraphConfig n) :
    permuteConfig π (permuteConfig ρ x) = permuteConfig (ρ.trans π) x := by
  funext e
  simp [permuteConfig, permEdge_permEdge]

@[simp] theorem permuteConfig_symm_permuteConfig {n : ℕ} (π : Equiv.Perm (Fin n))
    (x : GraphConfig n) : permuteConfig π.symm (permuteConfig π x) = x := by
  simp

@[simp] theorem permuteConfig_permuteConfig_symm {n : ℕ} (π : Equiv.Perm (Fin n))
    (x : GraphConfig n) : permuteConfig π (permuteConfig π.symm x) = x := by
  simp

@[simp] theorem graphWeight_permuteConfig {n : ℕ} (p : ℝ)
    (π : Equiv.Perm (Fin n)) (x : GraphConfig n) :
    graphWeight p (permuteConfig π x) = graphWeight p x := by
  classical
  exact (permEdgeEquiv π.symm).prod_comp (fun e => if x e = true then p else 1 - p)

@[simp] theorem permuteConfig_update {n : ℕ} (π : Equiv.Perm (Fin n))
    (x : GraphConfig n) (e : GraphEdge n) (b : Bool) :
    permuteConfig π (Function.update x e b) =
      Function.update (permuteConfig π x) (permEdge π e) b := by
  classical
  exact Function.update_comp_equiv x (permEdgeEquiv π.symm) e b

end Problem313

end

end OAI


