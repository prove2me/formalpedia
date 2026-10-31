-- Prove2me | Definitions.Def_OnlineGND_Model
-- name    : OnlineGND_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:00.39734+00:00
-- url     : https://prove2.me/theorems/fb2d7ad4-81f3-4d47-8530-19176d666dfd
-- title:
--   §1.1 — the GND model, loads, the τ-approximate min-cost oracle and the online run
-- statement:
--   This module fixes the generalized network design (GND) model of §1.1 (p.2) and the oracle assumption of p.3.
--
--   1. **Requests.** A finite set $E$ of resources and $N$ requests. Request $i$ has a collection $\mathcal P_i\subseteq 2^E$ of replies and a weight vector $w_i\in\mathbb R^E$.
--   2. **Loads.** A solution chooses a reply $p_i\in\mathcal P_i$ for every $i$; the load on $e$ is
--   $$\ell_e=\sum_{i:\,e\in p_i} w_{i,e}.$$
--   3. **The τ-approximate min-cost oracle.** A map $O$ that, for every request $i$ of the instance and all costs $\{d_e\ge 0\}_{e\in E}$, returns a reply $O(i,d)\in\mathcal P_i$ with
--   $$\sum_{e\in O(i,d)} d_e\le\tau\sum_{e\in p}d_e\quad\text{for every }p\in\mathcal P_i.$$
--   4. **The online run.** Given a rule that maps the current loads and the arriving request to a reply, request $i$ receives the reply chosen from the loads $\ell_e=\sum_{j<i:\,e\in p_j}w_{j,e}$ of the earlier replies, and the reply is never changed.
--   5. **The maximum exponent.** $\alpha=\max(1,\max_e\alpha_e)$.
--
--   These are the objects every theorem of the mission is stated over.
--
--   **Formalization Note** Requests are indexed by `Fin N` (0-based). Reply collections are finite sets of finite sets. The weight bound $w_{i,e}\ge1$ is a hypothesis of each theorem rather than part of the structure. The oracle is a function of the request and the cost vector, so the algorithms built from it are deterministic.
-- source:
--   Nagarajan & Wang, Online Generalized Network Design Under (Dis)Economies of Scale, arXiv:2007.07721v1, §1.1, p.2 (model); p.3 (α, Min-cost Oracle); (11) p.10 and (20) p.12 (current loads)

import Mathlib

namespace OnlineGND

/-! # The generalized network design (GND) model (Nagarajan & Wang, arXiv:2007.07721v1, §1.1, pp.2–3)

A finite set `E` of resources, `N` requests arriving online, reply collections `𝒫ᵢ ⊆ 2^E`, weight
vectors `wᵢ`, loads, the τ-approximate min-cost oracle, and the deterministic online rule
"choose a reply from the current loads and the current request".

**Formalization Note.** Requests are values `Request E` (a finite reply collection and a weight
vector); the instance is `reqs : Fin N → Request E`, 0-based. The oracle is a function
`O : Request E → (E → ℝ) → Finset E` of the request and the cost vector, so it is deterministic. -/

/-- A request `i` of GND (arXiv:2007.07721v1, §1.1, p.2): a collection `𝒫ᵢ ⊆ 2^E` of replies and a
weight vector `wᵢ ∈ ℝ^E`. The requirement `w_{i,e} ≥ 1` is a hypothesis of each theorem, not part of
the structure (Lemma 2 is posed for `w ≥ 0`).

**Formalization Note.** The reply collection is a `Finset (Finset E)`, which is no restriction since
`E` is finite. -/
structure Request (E : Type*) where
  /-- The reply collection `𝒫ᵢ`. -/
  replies : Finset (Finset E)
  /-- The weight vector `wᵢ`: request `i` induces load `w_{i,e}` on each resource `e` it uses. -/
  w : E → ℝ

variable {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ}

/-- The load of a solution (arXiv:2007.07721v1, §1.1, p.2): `ℓₑ = Σ_{i : e ∈ pᵢ} w_{i,e}`. -/
noncomputable def load (reqs : Fin N → Request E) (sol : Fin N → Finset E) (e : E) : ℝ :=
  ∑ i, if e ∈ sol i then (reqs i).w e else 0

/-- A solution of GND (arXiv:2007.07721v1, §1.1, p.2): a reply `pᵢ ∈ 𝒫ᵢ` for each request `i`. -/
def IsReplyProfile (reqs : Fin N → Request E) (sol : Fin N → Finset E) : Prop :=
  ∀ i, sol i ∈ (reqs i).replies

/-- The τ-approximate min-cost oracle (arXiv:2007.07721v1, p.3, "Min-cost Oracle"): for every
request `i` of the instance and all scalars `{dₑ ≥ 0}`, `O` returns a reply `O(i, d) ∈ 𝒫ᵢ` whose cost
`Σ_{e ∈ O(i,d)} dₑ` is at most `τ · Σ_{e∈p} dₑ` for every `p ∈ 𝒫ᵢ`, i.e. a `τ`-approximation of
`min_{p∈𝒫ᵢ} Σ_{e∈p} dₑ`.

**Formalization Note.** The predicate is required on the instance's requests only. It forces every
`𝒫ᵢ` to be nonempty. -/
def IsApproxOracle (τ : ℝ) (reqs : Fin N → Request E) (O : Request E → (E → ℝ) → Finset E) :
    Prop :=
  ∀ i, ∀ d : E → ℝ, (∀ e, 0 ≤ d e) →
    O (reqs i) d ∈ (reqs i).replies ∧
      ∀ p ∈ (reqs i).replies, ∑ e ∈ O (reqs i) d, d e ≤ τ * ∑ e ∈ p, d e

/-- The deterministic online run of a reply rule (arXiv:2007.07721v1, §1.1, p.2, "In the online
setting …"; the loads `ℓₑ := Σ_{j<i : e∈pⱼ} w_{j,e}` of (11), p.10, and (20), p.12): the reply to
request `i` is `rule ℓ (reqs i)`, where `ℓ` is the load of the replies already chosen for requests
`j < i`.

**Formalization Note.** Reply `i` depends only on requests `0, …, i` and is never revised, which is
what "online" and "deterministic" mean here. -/
noncomputable def onlineReplies (rule : (E → ℝ) → Request E → Finset E)
    (reqs : Fin N → Request E) : Fin N → Finset E
  | i => rule (fun e => ∑ j : Fin N,
      if _h : j < i then (if e ∈ onlineReplies rule reqs j then (reqs j).w e else 0) else 0) (reqs i)
termination_by i => i

/-- The maximum exponent `α := max_{e∈E} αₑ` (arXiv:2007.07721v1, p.3), computed as
`max(1, maxₑ αₑ)`.

**Formalization Note.** Every theorem assumes `αₑ ≥ 1`, so this equals the paper's `maxₑ αₑ` when
`E ≠ ∅`; for `E = ∅` it is `1`. -/
noncomputable def alphaMax {R : Type*} [Fintype R] (α : R → ℝ) : ℝ :=
  Finset.univ.fold max 1 α

end OnlineGND


