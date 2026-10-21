-- Prove2me | Definitions.Def_TraceAdopt_LPReform_Model
-- name    : TraceAdopt_LPReform_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:51.777986+00:00
-- url     : https://prove2.me/theorems/c79ebfea-87e7-4e03-b2f0-a7b7d672f5eb
-- title:
--   §3.1, §3.3, Definition 2 — adoption model, auxiliary graph, and hypergraph treewidth
-- statement:
--   An **instance** has a finite set of firms $N_F=\{1,\ldots,n\}$, supply chains $N_{SC}=\{1,\ldots,m\}$, a hyperedge $e_j\subseteq N_F$ for each supply chain, nonnegative integral benefits $r_{ji}$, positive integral adoption costs $c_i$, and integral thresholds $2\le\theta_j\le|e_j|$. Benefits for $i\notin e_j$ are ignored. The connectedness convention is read through the incidence graph $G'$. Each firm's total incident benefit is at least its adoption cost.
--
--   Starting from a seed set $S$, one **SCTM step** retains active firms and adds every firm whose incident supply chains have enough other active firms and whose total benefit covers its cost:
--
--   $$S_{t+1}=S_t\cup\left\{i\notin S_t: c_i\le\sum_{j:i\in e_j,\ |S_t\cap e_j|\ge\theta_j-1}r_{ji}\right\}.$$
--
--   $S$ fully activates the system when some finite iterate is all of $N_F$. $\mathrm{OPT}(w)$ is the minimum of $\sum_{i\in S}w_i$ over fully activating sets. The **auxiliary graph** $G'$ has firm and supply-chain vertices; an incident firm sends weight $1$ to its supply chain, and the supply chain sends weight $r_{ji}$ to that firm. Supply-chain vertices have threshold $\theta_j-1$ and firm vertices threshold $c_i$. Its weighted LTM step activates a vertex once the incoming weight from active vertices reaches its threshold. The definition also provides the primal graph, treewidth at most $\omega$ using vertex bags containing every hyperedge, the indicator $\mathbf1_S$, and $\vartheta_{\max}=\max(\max_i c_i,\max_j(\theta_j-1))$.
--
--   These definitions fix the optimization problem and graph parameters used throughout the mission.
--
--   **Formalization Note** The instance data are natural numbers, and $G'$ uses a disjoint union of firm and supply-chain vertices. Connectivity of $G$ means connectivity of its incidence graph. The paper treats connectedness as without loss of generality. The empty-family maximum is $0$; finite minimum is taken over a nonempty family because the all-firm seed set is feasible. The paper's gcd normalization and upper bound on hyperedge size are preprocessing conventions, not additional hypotheses.
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, pp. 5–7, 9–10, 13, 18, §3.1, §3.3, Definition 2, Proposition 9

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

namespace TraceAdopt.LPReform

/-- The hypergraph and adoption parameters of §3.1. -/
structure Instance where
  n : ℕ
  m : ℕ
  e : Fin m → Finset (Fin n)
  r : Fin m → Fin n → ℕ
  c : Fin n → ℕ
  θ : Fin m → ℕ

/-- The undirected version of the bipartite auxiliary graph `G′` of §3.3. -/
def auxGraph (I : Instance) : SimpleGraph (Fin I.n ⊕ Fin I.m) where
  Adj u v := match u, v with
    | Sum.inl i, Sum.inr j => i ∈ I.e j
    | Sum.inr j, Sum.inl i => i ∈ I.e j
    | _, _ => False
  symm := by
    constructor
    intro u v h
    cases u <;> cases v <;> simp_all
  loopless := by
    constructor
    intro u
    cases u <;> simp

/-- The paper's connectedness convention for the hypergraph, read through `G′`. -/
def Instance.Connected (I : Instance) : Prop := (auxGraph I).Connected

/-- Standing assumptions of §3.1, pp. 5–7. -/
def Instance.Standing (I : Instance) : Prop :=
  (∀ i, 0 < I.c i) ∧
  (∀ j, 2 ≤ I.θ j ∧ I.θ j ≤ (I.e j).card) ∧
  (∀ i, I.c i ≤ ∑ j ∈ Finset.univ.filter (fun j => i ∈ I.e j), I.r j i) ∧
  I.Connected

/-- One synchronous SCTM update, equation (1). -/
def step (I : Instance) (S : Finset (Fin I.n)) : Finset (Fin I.n) :=
  S ∪ Finset.univ.filter (fun i => i ∉ S ∧
    I.c i ≤ ∑ j ∈ Finset.univ.filter
      (fun j => i ∈ I.e j ∧ I.θ j - 1 ≤ (S ∩ I.e j).card), I.r j i)

/-- The seed set eventually activates every firm. -/
def FullyActivates (I : Instance) (S : Finset (Fin I.n)) : Prop :=
  ∃ t : ℕ, (step I)^[t] S = Finset.univ

/-- The minimum seeding cost in (1); the feasible family always contains `univ`. -/
noncomputable def OPT (I : Instance) (w : Fin I.n → ℝ) : ℝ := by
  classical
  exact (Finset.univ.filter (FullyActivates I)).inf'
    (by
      refine ⟨Finset.univ, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨0, rfl⟩)
    (fun S => ∑ i ∈ S, w i)

/-- One synchronous weighted LTM update on `G′`, p. 10. -/
noncomputable def ltmStep (I : Instance) (S : Finset (Fin I.n ⊕ Fin I.m)) :
    Finset (Fin I.n ⊕ Fin I.m) := by
  classical
  exact S ∪ Finset.univ.filter (fun v => v ∉ S ∧
    match v with
    | Sum.inl i => I.c i ≤ ∑ j ∈ Finset.univ.filter
        (fun j => Sum.inr j ∈ S ∧ i ∈ I.e j), I.r j i
    | Sum.inr j => I.θ j - 1 ≤
        (Finset.univ.filter (fun i => Sum.inl i ∈ S ∧ i ∈ I.e j)).card)

/-- The primal graph: two different firms are adjacent when they share a hyperedge. -/
def primalGraph (I : Instance) : SimpleGraph (Fin I.n) where
  Adj i k := i ≠ k ∧ ∃ j, i ∈ I.e j ∧ k ∈ I.e j
  symm := by
    constructor
    intro i k h
    obtain ⟨hne, j, hi, hk⟩ := h
    exact ⟨Ne.symm hne, j, hk, hi⟩
  loopless := by
    constructor
    intro i h
    exact h.1 rfl

/-- Hypergraph treewidth at most `ω`, Definition 2, p. 13. -/
def HypTreewidthLE (I : Instance) (ω : ℕ) : Prop :=
  ∃ (T : Type) (_ : Fintype T) (t : SimpleGraph T)
      (X : T → Finset (Fin I.n)),
    RobertsonSeymour1986.GM5.IsTreeDecomposition (primalGraph I) t X ∧
    (∀ j, ∃ s, I.e j ⊆ X s) ∧
    ∀ s, (X s).card ≤ ω + 1

/-- `ϑ_max = max(max_i c_i, max_j (θ_j-1))`, Proposition 9, p. 18. -/
def varthetaMax (I : Instance) : ℕ :=
  max (Finset.univ.sup I.c) (Finset.univ.sup (fun j => I.θ j - 1))

/-- The indicator of a seed set. -/
def ind {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- Firm vertices corresponding to a seed set, embedded in `G′`. -/
def liftSeeds (I : Instance) (S : Finset (Fin I.n)) :
    Finset (Fin I.n ⊕ Fin I.m) :=
  S.map ⟨Sum.inl, Sum.inl_injective⟩

end TraceAdopt.LPReform


