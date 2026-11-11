-- Prove2me | Definitions.Def_CubicPermFPRAS_Asg
-- name    : CubicPermFPRAS_Asg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:15.520055+00:00
-- url     : https://prove2.me/theorems/0fceb180-8c26-4011-9433-01fa92f2f863
-- title:
--   Assignments $\Omega_{\mathrm{aux}}$ and matchings $\mathcal P$, $\mathcal N(u,v)$, $\Omega$ of $K_{n,n}$
-- statement:
--   Let $V_1=V_2=\{0,\dots,n-1\}$. An **assignment** $\sigma\in\Omega_{\mathrm{aux}}=(V_2\cup\{*\})^{V_1}$ sends each left vertex $u$ either to a right vertex $\sigma_u\in V_2$ or to $*$ (unassigned). Its edge set is $\{(u,\sigma_u):\sigma_u\neq *\}$.
--
--   1. $\sigma$ is a **matching** of the complete bipartite graph $K_{n,n}$ when no right vertex receives two left vertices.
--   2. $\mathcal P$ is the set of **perfect matchings** (every left vertex assigned, injectively).
--   3. $\mathcal N(u,v)$ is the set of **near-perfect matchings with holes** $u\in V_1$, $v\in V_2$: matchings of size $n-1$ in which $u$ is the only unassigned left vertex and $v$ the only unused right vertex.
--   4. $\Omega=\mathcal P\cup\bigcup_{u,v}\mathcal N(u,v)$ is the state space of the JSV and FAR chains.
--
--   For $\sigma\in\Omega_{\mathrm{aux}}$ the paper uses $d_v(\sigma)=|\{u:\sigma_u=v\}|$, $\mathrm{un}(\sigma)=|\{u:\sigma_u=*\}|$, $\mathrm{cr}(\sigma)=\sum_v\max\{d_v(\sigma)-1,0\}$, the set $C(\sigma)$ of **conflicted** left vertices (assigned to a right vertex $v$ with $d_v(\sigma)\ge2$), the all-unassigned configuration $\sigma^*$, the size $|M|$, and the identity matching, used as the algorithm's fixed fallback perfect matching.
--
--   **Formalization Note** Assignments are functions `Fin n → Option (Fin n)`; `none` is $*$.
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), §2.1, p.2 (PDF 4); §5.1, p.12 (PDF 14)

import Mathlib

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **Assignments and matchings of `K_{n,n}`** (X. Chen, H. Guo, E. Vigoda, X. Yang,
*An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717, held version sha256 9e14f335…;
§2.1, p.2 (PDF 4) and §5.1, p.12 (PDF 14)).

An element `σ : Asg n` is a configuration of `Ω_aux = (V₂ ∪ {∗})^{V₁}` with
`V₁ = V₂ = Fin n`: `σ u = some v` means that the left vertex `u` is assigned to the right
vertex `v`, and `σ u = none` means that `u` is unassigned (`∗`).

**Formalization Note.** Matchings of the complete bipartite graph `K_{n,n}` are the
assignments that are injective on assigned vertices (`IsMatching`); the edge set of `σ` is
`{(u, v) : σ u = some v}`. Perfect matchings `P` are the total injective assignments
(bijections `V₁ → V₂`); `N(u,v)` are the matchings of size `n − 1` whose unmatched vertices
are `u ∈ V₁` and `v ∈ V₂`; `Ω = P ∪ ⋃ N(u,v)`. -/
abbrev Asg (n : ℕ) : Type := Fin n → Option (Fin n)

variable {n : ℕ}

/-- `σ` is a matching: no right vertex receives two left vertices. -/
def IsMatching (σ : Asg n) : Prop :=
  ∀ u u' v, σ u = some v → σ u' = some v → u = u'

instance (σ : Asg n) : Decidable (IsMatching σ) := by
  unfold IsMatching; infer_instance

/-- `σ ∈ P`: a perfect matching of `K_{n,n}` (every left vertex assigned, injectively). -/
def IsPerfect (σ : Asg n) : Prop :=
  IsMatching σ ∧ ∀ u, σ u ≠ none

instance (σ : Asg n) : Decidable (IsPerfect σ) := by
  unfold IsPerfect; infer_instance

/-- `σ ∈ N(u,v)`: a near-perfect matching with holes `u ∈ V₁` and `v ∈ V₂`, i.e. a matching
in which `u` is the only unassigned left vertex and `v` is the only unused right vertex. -/
def IsNear (u v : Fin n) (σ : Asg n) : Prop :=
  IsMatching σ ∧ σ u = none ∧ (∀ u', u' ≠ u → σ u' ≠ none) ∧ ∀ u', σ u' ≠ some v

instance (u v : Fin n) (σ : Asg n) : Decidable (IsNear u v σ) := by
  unfold IsNear; infer_instance

/-- `σ ∈ Ω = P ∪ ⋃_{u,v} N(u,v)`. -/
def InOmega (σ : Asg n) : Prop :=
  IsPerfect σ ∨ ∃ u v, IsNear u v σ

instance (σ : Asg n) : Decidable (InOmega σ) := by
  unfold InOmega; infer_instance

/-- The state space `Ω` of the JSV and FAR chains, as a finite type. -/
abbrev Omega (n : ℕ) : Type := {σ : Asg n // InOmega σ}

/-- The set `P` of perfect matchings of `K_{n,n}`. -/
def PSet (n : ℕ) : Finset (Asg n) := Finset.univ.filter IsPerfect

/-- The set `N(u,v)` of near-perfect matchings with holes `u, v`. -/
def NSet (u v : Fin n) : Finset (Asg n) := Finset.univ.filter (IsNear u v)

/-- The edge set `{(u, v) : σ u = some v}` of an assignment. -/
def edges (σ : Asg n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun e => σ e.1 = some e.2

/-- `d_v(σ) = |{u : σ_u = v}|`, the number of left vertices assigned to `v` (p.12). -/
def deg (σ : Asg n) (v : Fin n) : ℕ := (Finset.univ.filter fun u => σ u = some v).card

/-- `un(σ) = |{u : σ_u = ∗}|`, the number of unassigned left vertices (p.12). -/
def un (σ : Asg n) : ℕ := (Finset.univ.filter fun u => σ u = none).card

/-- `cr(σ) = ∑_v max{d_v(σ) − 1, 0}`, the number of assignments beyond the first at each right
vertex (p.12). Natural-number subtraction is exactly `max{d − 1, 0}`. -/
def cr (σ : Asg n) : ℕ := ∑ v, (deg σ v - 1)

/-- `u` is conflicted in `σ`: it is assigned to a crowded right vertex (`d_{σ_u}(σ) ≥ 2`). -/
def IsConflicted (σ : Asg n) (u : Fin n) : Prop :=
  ∃ v, σ u = some v ∧ 2 ≤ deg σ v

instance (σ : Asg n) (u : Fin n) : Decidable (IsConflicted σ u) := by
  unfold IsConflicted; infer_instance

/-- The set `C(σ)` of conflicted left vertices (p.50). -/
def conflicted (σ : Asg n) : Finset (Fin n) := Finset.univ.filter (IsConflicted σ)

/-- `σ*`, the configuration in which every left vertex is unassigned (p.12). -/
def sigmaStar (n : ℕ) : Asg n := fun _ => none

/-- The number `|M|` of edges of an assignment (`n − un(σ)`). -/
def size (σ : Asg n) : ℕ := (Finset.univ.filter fun u => σ u ≠ none).card

/-- The identity perfect matching `u ↦ u`, the algorithm's fixed fallback perfect matching
("an arbitrary fixed perfect matching", p.13). -/
def idMatching (n : ℕ) : Asg n := fun u => some u

end CubicPermFPRAS


