-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
-- name    : OAI_Combinatorics_CliqueFree_MultiplierLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:44:36.45319+00:00
-- url     : https://prove2.me/theorems/5ca6b390-60c5-489d-9282-b063cfe21975
-- title:
--   Restricted weights, bounded multiplier lotteries and expected weighted edge mass
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$ and $w:V\to\mathbb{R}$ a vertex weight, with weighted edge mass $E_w(G)=\sum_{\{u,v\}\in E(G)}w(u)\,w(v)$. A lottery of multipliers is a finite list $L=\bigl((p_1,m_1),\dots,(p_n,m_n)\bigr)$ of real weights $p_i$ and vectors $m_i:V\to\mathbb{R}$, with expectation $\mathbb{E}_L[f]=\sum_i p_i\,f(m_i)$. The file defines:
--
--   1. **Restriction** of $w$ to a set $A\subseteq V$: the vector $w\,\mathbf{1}_A$, equal to $w(v)$ for $v\in A$ and to $0$ outside $A$.
--
--   2. **Bounded on $A$ by $b$:** a lottery $L$ has this property if every entry $(p_i,m_i)$ of the list, including entries of weight $p_i=0$, satisfies
--
--      $$0\le m_i(v)\le b\ \ \text{for all }v\in V\qquad\text{and}\qquad m_i(v)=0\ \ \text{for all }v\notin A .$$
--
--   3. **Expected edge mass** of $L$ relative to $G$ and $w$:
--
--      $$\mathcal{E}_G(w,L)=\mathbb{E}_L\bigl[E_{w\odot m}(G)\bigr]=\sum_{i}p_i\sum_{\{u,v\}\in E(G)}w(u)\,m_i(u)\,w(v)\,m_i(v),$$
--
--      where $(w\odot m)(v)=w(v)\,m(v)$.
--
--   These notions describe random reweightings of a vertex set $A$: a probability lottery bounded on $A$ whose mean multiplier $\mathbb{E}_L[m(v)]$ equals $1$ on $A$ keeps the expected weight of every vertex, while its expected edge mass can be much smaller than that of $w\,\mathbf{1}_A$. Sparse reweightings of this kind exist on sets containing no large clique, and they feed variational estimates for cross masses.
--
--   **Formalization Note** The Lean names are `restrict A w`, `BoundedOn L A b` and `expectedEdges G w L`, where `L : Law (V → ℝ)` is a list of weighted multiplier vectors. The boundedness condition quantifies over list entries regardless of their weights.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/MultiplierLaw.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/MultiplierLaw.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CliqueFreeLog mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence
universe u
namespace WeightedGraph
open Lottery
variable {V : Type u} [Fintype V]

/-- A weight vector restricted to a vertex set. -/
noncomputable def restrict (A : Finset V) (w : V → ℝ) : V → ℝ := fun v ↦ if v ∈ A then w v else 0

/-- Bounded multipliers supported on A, regardless of the lottery weight of the entry. -/
def BoundedOn (L : Law (V → ℝ)) (A : Finset V) (b : ℝ) : Prop :=
  ∀ z ∈ L, (∀ v, 0 ≤ z.2 v ∧ z.2 v ≤ b) ∧ (∀ v, v ∉ A → z.2 v = 0)

noncomputable def expectedEdges (G : SimpleGraph V) (w : V → ℝ) (L : Law (V → ℝ)) : ℝ :=
  expect L (fun m ↦ edgeMass G (fun v ↦ w v*m v))

end WeightedGraph
end CliqueFreeIndependence

end

end OAI


