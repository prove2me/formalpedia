-- Prove2me | Definitions.Def_FlowOptimalSeparators_MinorFree_Connectors
-- name    : FlowOptimalSeparators_MinorFree_Connectors
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T00:06:13.924783+00:00
-- url     : https://prove2.me/theorems/26209ead-465f-486c-a951-d012dc217856
-- title:
--   Wide connectors, loads, quadratic objective, and endpoint path laws
-- statement:
--   A wide connector $C=(X,r,B)$ consists of a rooted tree subgraph with terminal set $B$, using $|B|=\lceil3n/4\rceil$. Its parent paths include the root and terminal. Its load is
--   $$p_C(v)=\frac{|\{b\in B:v\in X[r,b]\}|}{|B|}.$$
--   The tree radius is the maximum full vertex-weight sum of a root path. For nonnegative parameters $\mu,\iota$, define
--   $$H_{\mu,\iota}(p,q)=\mu\sum_vp(v)q(v)+\iota\sum_{uv\in E}(p(u)q(v)+p(v)q(u)),$$
--   $$F_{\mu,\iota}(\lambda)=\sum_C\lambda_C-\sum_{\{C,C'\}:C\ne C'}\lambda_C\lambda_{C'}H_{\mu,\iota}(p_C,p_{C'}).$$
--   Feasibility means $0\le\lambda_C\le1$ and at most one unit of total connector mass at each root. The family contains every valid tree and terminal set. Half an ordered distinct-pair sum implements the unordered sum, with no diagonal.
--
--   Endpoint laws are arbitrary finite probability vectors. Conditional simple-path kernels normalize on each positive-mass ordered endpoint pair; diagonal paths are singletons. Collision probability is the finite double sum for two independent copies. Parent arrays encode trees without cycles. The ceiling count and conditional root inclusion are the explicit integrality reading described in the mission scope.
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 10–11, 13, 17, Section 3.2, Eqs. (9)–(13); Lemma 1; Proposition 2

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_Graph

set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree

/-- A finite parent-array encoding of a rooted subtree and its terminal set. -/
structure ConnectorData (n : ℕ) where
  vertices : Finset (Fin n)
  root : Fin n
  parent : Fin n → Option (Fin n)
  terminals : Finset (Fin n)
  deriving Fintype, DecidableEq

/-- Parent paths include the starting vertex and root, and have at most n vertices. -/
def ancestorPath {n : ℕ} (C : ConnectorData n) : ℕ → Fin n → List (Fin n)
  | 0, _ => []
  | k + 1, v => v :: (match C.parent v with
      | none => []
      | some u => ancestorPath C k u)

/-- Reaching the root excludes cycles and makes the parent edges a tree. The ceiling resolves
"exactly 3n/4" off multiples of four; it does not exclude the root from the terminals. -/
def ConnectorData.Valid {n : ℕ} (G : Graph n) (C : ConnectorData n) : Prop :=
  C.root ∈ C.vertices ∧ C.parent C.root = none ∧
  (∀ v, v ∉ C.vertices → C.parent v = none) ∧
  (∀ v ∈ C.vertices, v ≠ C.root →
    ∃ u ∈ C.vertices, C.parent v = some u ∧ G.Adj v u) ∧
  (∀ v ∈ C.vertices, C.root ∈ ancestorPath C n v) ∧
  C.terminals ⊆ C.vertices ∧ C.terminals.card = (3 * n + 3) / 4

abbrev WideConnector {n : ℕ} (G : Graph n) := {C : ConnectorData n // C.Valid G}

noncomputable instance {n : ℕ} (G : Graph n) : Fintype (WideConnector G) :=
  Fintype.ofFinite _

noncomputable def load {n : ℕ} {G : Graph n} (C : WideConnector G) (v : Fin n) : ℝ :=
  ((C.val.terminals.filter (fun b => v ∈ ancestorPath C.val n b)).card : ℝ) /
    C.val.terminals.card

/-- A true maximum: the vertex set is nonempty (it contains the root) and finite. -/
noncomputable def treeRadius {n : ℕ} {G : Graph n} (C : WideConnector G)
    (w : Fin n → ℝ) : ℝ :=
  sSup ((fun v => vertexWeight w (ancestorPath C.val n v)) ''
    (C.val.vertices : Set (Fin n)))

noncomputable def pathExpectation {n : ℕ} {G : Graph n} (C : WideConnector G)
    (w : Fin n → ℝ) : ℝ :=
  (∑ b ∈ C.val.terminals, vertexWeight w (ancestorPath C.val n b)) /
    C.val.terminals.card

noncomputable def interaction {n : ℕ} (G : Graph n) (μ ι : ℝ)
    (p q : Fin n → ℝ) : ℝ :=
  μ * (∑ v, p v * q v) +
    ι * ∑ e ∈ edges G, (p e.1 * q e.2 + p e.2 * q e.1)

/-- Half the sum over ordered distinct pairs is the unordered-pair sum in (11). No diagonal. -/
noncomputable def objective {n : ℕ} (G : Graph n) (μ ι : ℝ)
    (lam : WideConnector G → ℝ) : ℝ := by
  classical
  exact (∑ C, lam C) - (1 / 2 : ℝ) *
    ∑ C, ∑ C' ∈ (Finset.univ.erase C),
      lam C * lam C' * interaction G μ ι (load C) (load C')

def Feasible {n : ℕ} {G : Graph n} (lam : WideConnector G → ℝ) : Prop :=
  (∀ C, 0 ≤ lam C ∧ lam C ≤ 1) ∧
    ∀ u : Fin n, (∑ C, if C.val.root = u then lam C else 0) ≤ 1

/-- Endpoint laws on the finite vertex set; no restriction to uniform endpoints. -/
def EndpointLaw {n : ℕ} (π : Fin n → ℝ) : Prop :=
  (∀ u, 0 ≤ π u) ∧ ∑ u, π u = 1

/-- A normalized conditional simple-path law for every positive-mass ordered pair.
Unsupported pairs may be zero; supported disconnected pairs cannot satisfy normalization. -/
def PathKernel {n : ℕ} (G : Graph n) (π : Fin n → ℝ)
    (κ : Fin n → Fin n → List (Fin n) → ℝ) : Prop :=
  (∀ u v P, 0 ≤ κ u v P) ∧
  (∀ u v P, ¬ IsSimplePath G u v P → κ u v P = 0) ∧
  (∀ u v, 0 < π u → 0 < π v → ∑ P ∈ simplePaths G u v, κ u v P = 1) ∧
  ∀ u P, P ≠ [u] → κ u u P = 0

noncomputable def pathLaw {n : ℕ} (π : Fin n → ℝ)
    (κ : Fin n → Fin n → List (Fin n) → ℝ) (P : List (Fin n)) : ℝ :=
  ∑ u, ∑ v, π u * π v * κ u v P

noncomputable def collisionProbability {n : ℕ} (π : Fin n → ℝ)
    (κ : Fin n → Fin n → List (Fin n) → ℝ) : ℝ := by
  classical
  exact ∑ P ∈ pathLists n, ∑ Q ∈ pathLists n,
    if ∃ v, v ∈ P ∧ v ∈ Q then pathLaw π κ P * pathLaw π κ Q else 0

end FlowOptimalSeparators.MinorFree


