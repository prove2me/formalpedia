-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
-- name    : OAI_Combinatorics_Hamiltonian_Quotients
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:21:15.176466+00:00
-- url     : https://prove2.me/theorems/7f4ec9ca-3c65-469e-8fd7-cd6e331ed160
-- title:
--   Push-forward and pull-back along vertex maps, contracted and restricted networks, and connected fibres
-- statement:
--   Let $N$ be an oriented network with vertex set $V$, edge set $E$, tail map $t : E \to V$ and head map $h : E \to V$, with gradient $(\nabla_N f)(e) = f(h(e)) - f(t(e))$ for $f \in \mathbb{R}^V$. Let $q : V \to W$ be a map to another set $W$.
--
--   1. **Push-forward and pull-back.** For finite $V$, the push-forward $q_* : \mathbb{R}^V \to \mathbb{R}^W$ sums over fibres,
--   $$
--   (q_* x)(w) = \sum_{v \in V :\ q(v) = w} x(v),
--   $$
--   and the pull-back $q^* : \mathbb{R}^W \to \mathbb{R}^V$ is composition, $q^* f = f \circ q$. Both maps are linear and they are adjoint to each other: $\sum_{w} (q_* x)(w)\, f(w) = \sum_{v} x(v)\, f(q(v))$.
--
--   2. **Contracted network.** $N/q$ is the network with vertex set $W$, the same edge set $E$, tail $q \circ t$ and head $q \circ h$; edges inside a fibre of $q$ become loops. Its gradient is $\nabla_{N/q} f = \nabla_N (q^* f)$.
--
--   3. **Restricted network.** For a map $j : K \to E$ (typically the inclusion of a set of edges), $N|_j$ is the network with vertex set $V$, edge set $K$, tail $t \circ j$ and head $h \circ j$. Its gradient is $\nabla_{N|_j} f = j^* (\nabla_N f)$.
--
--   4. **Internal edges and connected fibres.** The internal edges of $q$ are those whose endpoints lie in the same fibre, $I_q = \{ e \in E : q(t(e)) = q(h(e)) \}$. The map $q$ has connected fibres (with respect to $N$) if for all $v, w \in V$
--   $$
--   q(v) = q(w) \quad \Longrightarrow \quad v \text{ and } w \text{ are joined by a walk in the underlying graph of } N|_{I_q},
--   $$
--   that is, every fibre of $q$ is connected using only edges with both endpoints in that fibre.
--
--   These operations describe the contraction of connected vertex sets, used to pass to minors of a network. In the surrounding development it is shown that, for a surjective $q$ with connected fibres, the image of the boundary operator of the internal subnetwork is exactly $\ker q_*$, which is how cycle and cut spaces of contractions are computed.
--
--   **Formalization Note** `push q` (requires `Fintype V`), `pull q` (which is `LinearMap.funLeft`), `mapVertices`, `restrict`, `internal` (a `Set E`) and `ConnectedFibers`, stated with `SimpleGraph.Reachable` in the graph of `N.restrict Subtype.val`. The simp lemmas `push_apply`, `pull_apply`, `gradient_mapVertices` and `gradient_restrict` hold by definition; the adjointness above is a direct consequence and not a separate lemma.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Quotients.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Quotients.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BarnetteHamiltonian mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds

namespace OAI

/-! Vertex quotients and connected fibers of incidence networks. -/

namespace Barnette.Network
noncomputable section
variable {V W E K : Type*}
open scoped Classical

def push [Fintype V] (q : V → W) : (V → ℝ) →ₗ[ℝ] (W → ℝ) where
  toFun x w := ∑ v, if q v = w then x v else 0
  map_add' x y := by
    ext w
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp
  map_smul' c x := by
    ext w
    simp [Finset.mul_sum, mul_ite]

def pull (q : V → W) : (W → ℝ) →ₗ[ℝ] (V → ℝ) :=
  LinearMap.funLeft ℝ ℝ q

@[simp] theorem pull_apply (q : V → W) (f : W → ℝ) (v : V) :
    pull q f v = f (q v) := rfl

@[simp] theorem push_apply [Fintype V] (q : V → W) (x : V → ℝ) (w : W) :
    push q x w = ∑ v, if q v = w then x v else 0 := rfl

def mapVertices (N : Network V E) (q : V → W) : Network W E :=
  ⟨q ∘ N.tail, q ∘ N.head⟩

def restrict (N : Network V E) (j : K → E) : Network V K :=
  ⟨N.tail ∘ j, N.head ∘ j⟩

@[simp] theorem gradient_mapVertices (N : Network V E) (q : V → W) (f : W → ℝ) :
    (N.mapVertices q).gradient f = N.gradient (pull q f) := rfl

@[simp] theorem gradient_restrict (N : Network V E) (j : K → E) (f : V → ℝ) :
    (N.restrict j).gradient f = pull j (N.gradient f) := rfl

variable [Fintype V] [Fintype W] [Fintype E] [Fintype K]

def internal (N : Network V E) (q : V → W) : Set E :=
  {e | q (N.tail e) = q (N.head e)}

def ConnectedFibers (N : Network V E) (q : V → W) : Prop :=
  ∀ v w, q v = q w → (N.restrict (Subtype.val : N.internal q → E)).graph.Reachable v w

end
end Barnette.Network

end OAI


