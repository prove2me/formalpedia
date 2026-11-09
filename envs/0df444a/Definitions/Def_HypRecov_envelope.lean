-- Prove2me | Definitions.Def_HypRecov_envelope
-- name    : HypRecov_envelope
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:37:26.094881+00:00
-- url     : https://prove2.me/theorems/65cda426-bfe4-4454-9651-221bbbcb931c
-- title:
--   Codegrees, available low lists, known members $P_e$, the graphs $G_0,G$, the envelope $U_e$ and the completion test (∗)
-- statement:
--   This item collects the deterministic objects of the recovery argument of §4–§6, for $k\ge 3$, $M=2^{\lceil\log_2 k\rceil-1}$, a residual hypergraph $J$ and a base partition $P_0$.
--
--   1. The **pair codegree** $w_J(uv)=|\{e\in E(J):\{u,v\}\subseteq e\}|$.
--   2. A pair $u\ne v$ is **available** if $u,v$ lie in different blocks of $P_0$ and $1\le w_J(uv)<M$: its complete low list of residual edges is known.
--   3. The **known members** $P_e$ of an edge $e$: the vertices $x\in e$ with an available pair $\{x,y\}\subseteq e$.
--   4. The **block graph** of a partition $P$: distinct $u,v$ are adjacent if they share a block or $w_J(uv)\ge 1$. With $P_0$ it is $G_0$; with the current partition it is $G$.
--   5. The **membership envelope** $U_e=\bigcap_{p\in P_e}N_{G_0}[p]$, minus every $v$ such that some available pair $\{p,v\}$, $p\in P_e$, has $e$ absent from its list.
--   6. The **number of Cauchy points** of $e$: two for each available pair inside $e$.
--   7. The **completion test** (∗)/(4): $\#\text{points}\ge 2\min\{r-|P_e|,\ |U_e|-r\}$. An edge **qualifies** if it is a residual edge appearing in an available list, passes the test and spans the current partition; a state is **completion-terminal** if no edge qualifies.
--
--   **Formalization Note** These are stated on the true residual hypergraph: on the success event of the cache (Proposition 4.1) every count and list the algorithm reads equals the true one and the tags are injective (p.9). The envelope is taken without the optional extra negative certificates, so it is the largest one.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), §4, p.8 (PDF p.9); §5.1, pp.9–10; Theorem 5.3, p.11; §6.1, p.13

import Mathlib
import Definitions.Def_HypRecov_Safe

namespace HypRecov

/-- The power of two `M = 2^{⌈log₂ k⌉−1}`. Zhang, Chen, Shen, *Hypergraph Recovery from Anonymous
Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), §4, p.8 (PDF p.9): "Fix
k ≥ 3, put K = k − 1, and let M = 2^{⌈log₂ k⌉−1}, so M ≤ K < 2M." -/
def Mpow (k : ℕ) : ℕ := 2 ^ (Nat.clog 2 k - 1)

/-- The pair codegree `w_J(uv) = |{e ∈ E(J) : {u, v} ⊆ e}|` (ibid., §4, p.8). -/
def codeg {n : ℕ} (J : Finset (Finset (Fin n))) (u v : Fin n) : ℕ :=
  (J.filter (fun e => u ∈ e ∧ v ∈ e)).card

/-- **An available complete low list.** Ibid., §4, p.8 ("call it low when 1 ≤ w_J(uv) < M"),
Proposition 4.1, p.8, and §5.1, p.9: "every positive pair crossing P0 has an exact residual count. A
count below M gives the complete list of residual edge tags … The query interface is restricted to
cross-base pairs."

`avail J P₀ M u v`: `u ≠ v` lie in different blocks of the base partition `P₀` and
`1 ≤ w_J(uv) < M`; the complete list of the residual edges containing `{u, v}` is then known.

**Formalization Note.** Stated on the true residual hypergraph: on the success event of the cache
(Proposition 4.1) every count and list the algorithm reads equals the true one, and tags are injective,
so "the tag of `e` occurs in the list of `{u, v}`" is `{u, v} ⊆ e`. -/
def avail {n : ℕ} (J : Finset (Finset (Fin n))) (P₀ : Fin n → Fin n) (M : ℕ) (u v : Fin n) :
    Prop :=
  u ≠ v ∧ P₀ u ≠ P₀ v ∧ 1 ≤ codeg J u v ∧ codeg J u v < M

open Classical in
/-- **Known members `P_e`.** Ibid., §5.1, p.9: "A complete pair list containing the tag certifies
both endpoints as members of e. Let P_e contain all members obtained this way." -/
noncomputable def knownMembers {n : ℕ} (J : Finset (Finset (Fin n))) (P₀ : Fin n → Fin n) (M : ℕ)
    (e : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun x => x ∈ e ∧ ∃ y ∈ e, avail J P₀ M x y)

/-- **The block graph.** Ibid., §5.1, p.9 and §6.1, p.13: "Define G_0 by filling every base block into
a clique and adding the positive residual cross-base pairs." "The graph G completes each current
block to a clique and contains the positive residual pairs joining different current blocks."
`blockGraph J P₀` is `G_0` and `blockGraph J P` is `G`. -/
def blockGraph {n : ℕ} (J : Finset (Finset (Fin n))) (P : Fin n → Fin n) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (P u = P v ∨ 1 ≤ codeg J u v)
  symm := ⟨fun u v h => ⟨h.1.symm, h.2.elim (fun h' => Or.inl h'.symm) (fun h' => Or.inr (by
    unfold codeg at h' ⊢
    simpa only [and_comm] using h'))⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

open Classical in
/-- **The membership envelope `U_e`.** Ibid., §5.1, pp.9–10: "Start with ⋂_{p∈P_e} N_{G_0}[p] and
delete every vertex v for which some available complete list for pv, with p ∈ P_e, omits the tag. We
call the resulting set U_e the membership envelope of e."

**Formalization Note.** The paper allows "additional sound negative certificates" to shrink `U_e`
further; this is the envelope without them, the largest one, for which every statement using it is
strongest. For `P_e = ∅` the intersection is all of `V`. -/
noncomputable def envelope {n : ℕ} (J : Finset (Finset (Fin n))) (P₀ : Fin n → Fin n) (M : ℕ)
    (e : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v =>
    (∀ p ∈ knownMembers J P₀ M e, v = p ∨ (blockGraph J P₀).Adj p v) ∧
      ¬ ∃ p ∈ knownMembers J P₀ M e, avail J P₀ M p v ∧ ¬ (p ∈ e ∧ v ∈ e))

open Classical in
/-- **The number of distinct available Cauchy points for `e`.** Ibid., Proposition 4.1(3), p.8: "For
each hyperedge e whose label occurs in the complete list for a low pair f, the records give two values
β_{f,ℓ}(e), ℓ ∈ {1, 2}. All … pair-specific evaluation points a_{f,ℓ} are distinct." Two points for
each available pair `f ⊆ e`. -/
noncomputable def numPoints {n : ℕ} (J : Finset (Finset (Fin n))) (P₀ : Fin n → Fin n) (M : ℕ)
    (e : Finset (Fin n)) : ℕ :=
  2 * ((e.powersetCard 2).filter (fun f => ∃ u ∈ f, ∃ v ∈ f, avail J P₀ M u v)).card

/-- **The completion test (∗) / (4).** Ibid., Theorem 5.3, p.11 and §6.1, p.13:
"#{distinct available Cauchy points for e} ≥ 2 min{r − |P_e|, |U_e| − r}".

**Formalization Note.** Natural-number subtraction; for a residual edge `e` of size `r` one has
`P_e ⊆ e ⊆ U_e`, so both differences are the true ones there. -/
def CompletionTest {n : ℕ} (r : ℕ) (J : Finset (Finset (Fin n))) (P₀ : Fin n → Fin n) (M : ℕ)
    (e : Finset (Fin n)) : Prop :=
  2 * min (r - (knownMembers J P₀ M e).card) ((envelope J P₀ M e).card - r) ≤ numPoints J P₀ M e

/-- **A qualifying edge.** Ibid., §6.1, p.13: the residual edge `e` appears in an available complete
low list, passes the completion test (4), and spans current blocks of `P`. -/
def Qualifies {n : ℕ} (r : ℕ) (J : Finset (Finset (Fin n))) (P₀ P : Fin n → Fin n) (M : ℕ)
    (e : Finset (Fin n)) : Prop :=
  e ∈ J ∧ (∃ u ∈ e, ∃ v ∈ e, avail J P₀ M u v) ∧ CompletionTest r J P₀ M e ∧ Spans P e

/-- **Completion-terminal state.** Ibid., §6.1, p.13: "We apply the rule until no qualifying edge
spans current blocks … We call this a completion-terminal state." -/
def CompletionTerminal {n : ℕ} (r : ℕ) (J : Finset (Finset (Fin n))) (P₀ P : Fin n → Fin n)
    (M : ℕ) : Prop :=
  ∀ e : Finset (Fin n), ¬ Qualifies r J P₀ P M e

end HypRecov


