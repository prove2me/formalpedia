-- Prove2me | Definitions.Def_LeeCutCertificates_Certificate_Flows
-- name    : LeeCutCertificates_Certificate_Flows
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:50.437095+00:00
-- url     : https://prove2.me/theorems/2d7b342a-cab6-47ea-b35a-f082e406fd73
-- title:
--   Signed flows, net outflow and divergence certificates
-- statement:
--   For the graph and pair capacities above, a signed flow is a real function $f:V\times V\to\mathbb R$ with $f(u,v)=-f(v,u)$. Positive $f(u,v)$ means flow from $u$ to $v$. Feasibility and divergence mean
--
--   $$|f(u,v)|\le w_G(u,v),\qquad b(v)=\sum_{u\in V}f(v,u).$$
--
--   Thus divergence is net outflow: sources have positive divergence. A vector $b$ is feasible when some feasible flow has divergence exactly $b$. A finite family $Q$ is a flow certificate for $b$ when $b$ is feasible in every nonnegative graph consistent with $G$ on $Q$. This interface certifies a lower-bound witness without fixing its realization.
--
--   **Formalization Note** All sums are finite, and the capacity constraint uses aggregate undirected pair weights rather than individual edge records. The realizing flow is existentially quantified inside each competitor, so it may change with the graph. The vector $b$ is held fixed across competitors; no source–sink pattern, conservation outside two vertices, or positive global cut value is imposed by the definition.
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), §2.1, printed p.3 (PDF p.4); §7.1, printed pp.18–20 (PDF pp.19–21); pinned PDF sha256 853e2745e72c36e8e0567917faa6eedd8dfe99b4078a34a70d8d4b81516c372d (citation_basis: published, submission artifact, not an acceptance claim).

import Mathlib
import Definitions.Def_LeeCutCertificates_Certificate_CutQueries

set_option autoImplicit false
open scoped BigOperators
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate

/-- Signed flow; positive f(u,v) is directed from u to v. -/
def SignedFlow {n : ℕ} (f : Fin n → Fin n → ℝ) : Prop :=
  ∀ u v, f u v = -f v u

/-- Antisymmetry and aggregate undirected capacity constraints. -/
def FeasibleFlow {n m : ℕ} (G : Graph n m) (f : Fin n → Fin n → ℝ) : Prop :=
  SignedFlow f ∧ ∀ u v, |f u v| ≤ pairWeight G u v

/-- Net outflow, not inflow. -/
def divergence {n : ℕ} (f : Fin n → Fin n → ℝ) (v : Fin n) : ℝ := ∑ u, f v u

/-- The vector b is realized by some feasible flow in G. -/
def FeasibleDivergence {n m : ℕ} (G : Graph n m) (b : Fin n → ℝ) : Prop :=
  ∃ f : Fin n → Fin n → ℝ, FeasibleFlow G f ∧ divergence f = b

/-- Only the divergence is fixed; the realizing flow may change with the completion. -/
def FlowCertificate {n m : ℕ} (G : Graph n m) (b : Fin n → ℝ)
    (Q : Finset (Finset (Fin n))) : Prop :=
  ∀ (k : ℕ) (H : Graph n k), Nonnegative H → Agrees G H Q → FeasibleDivergence H b

end LeeCutCertificates.Certificate


