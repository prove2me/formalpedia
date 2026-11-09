-- Prove2me | Definitions.Def_RelativisticZK205_ThreeCol_Protocol
-- name    : RelativisticZK205_ThreeCol_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:08:11.421136+00:00
-- url     : https://prove2.me/theorems/ed86b7eb-eec7-4f90-86c8-6e24d1402b69
-- title:
--   Protocol $\Pi^{(2)}_{\mathrm{LHV}}$: queries, aborts and the real provers' response channel
-- statement:
--   Let $G=(V,E)$ be a graph on the vertices $0,\dots,n-1$ and $c$ a colouring with values in $\mathbb F_3$. A verifier's message is a **query** $((i,j),r)$ with $i,j$ vertices and $r\in\mathbb F_2$. The query is **valid** when $(i,j)\in E$, edges being always written with $i<j$.
--
--   The two provers pre-agree on a uniformly random permutation $\Pi$ of $\mathbb F_3$ and on independent uniform masks $\ell_{i0}\in\mathbb F_3$, one per vertex, and set
--
--   $$
--   \ell_{i1}=\Pi(c_i)-\ell_{i0}.
--   $$
--
--   On a valid query $((i,j),r)$ a prover replies $(w_i,w_j)=(\ell_{ir},\ell_{jr})$; on an invalid one it aborts. The **real response channel** sends prover 1 the query $q_1$ and prover 2 the query $q_2$, and outputs the pair of their replies, both computed from one common draw of $(\Pi,\ell_{\cdot0})$.
--
--   This is the commit phase of the two-prover 3-colouring proof system of [ABC+21] as restated in §5.1; the simulators must reproduce this channel without knowing $c$.
--
--   **Formalization Note** Vertices are `Fin n`, a query is `Fin n × Fin n × Bool`, and a reply is `Option (ZMod 3 × ZMod 3)` with `none` the abort. The shared randomness is uniform on `Equiv.Perm (ZMod 3) × (Fin n → ZMod 3)`. The verifiers' query distribution $D_{G'}$ is left unspecified by the source (footnote 5) and does not enter here: verifiers are a separate definition.
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), §5.1, pp.9–10, Protocol Π^(2)_LHV[G, C], commit phase

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_Channel

/-!
# Protocol `Π^(2)_LHV`: queries, replies and the real provers' response channel

Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, *Relativistic Zero
Knowledge*, STOC 2027 submission #205 (October 2026), §5.1, pp.9–10.

Vertices are `Fin n` (`|V| = n`, labels `0, …, n-1`), the graph is a `SimpleGraph (Fin n)`, a
colouring is `c : Fin n → ZMod 3`, and `F₂` is `Bool`.
-/

namespace RelativisticZK205.ThreeCol

/-- p.9: a verifier's message `((i, j), r) ∈ V² × F₂`, stored as `(i, j, r)`. -/
abbrev Query (n : ℕ) : Type := Fin n × Fin n × Bool

/-- p.10: a prover's reply: `some (w_i, w_j)`, or `none` for an abort. -/
abbrev Reply : Type := Option (ZMod 3 × ZMod 3)

/-- The vertex `i` (for `u = 0`, i.e. `false`) or `j` (for `u = 1`, i.e. `true`) of a query
`((i, j), r)`. -/
def labelOf {n : ℕ} (u : Bool) (q : Query n) : Fin n := if u then q.2.1 else q.1

/-- p.9–10: a query `((i, j), r)` is valid iff `(i, j) ∈ E`, where "edges are always represented
with `i < j`" (p.9). -/
def IsValid {n : ℕ} (G : SimpleGraph (Fin n)) (q : Query n) : Prop :=
  q.1 < q.2.1 ∧ G.Adj q.1 q.2.1

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : Query n) :
    Decidable (IsValid G q) := by
  unfold IsValid; infer_instance

/-- p.9: the provers' shared randomness: a permutation `Π` of `F₃` and one mask `ℓ_{i0} ∈ F₃` per
vertex. -/
abbrev ProverCoins (n : ℕ) : Type := Equiv.Perm (ZMod 3) × (Fin n → ZMod 3)

/-- p.9: the provers' values `ℓ_{i0}` (the mask) and `ℓ_{i1} = Π(c_i) − ℓ_{i0}`, for `r = 0`
(`false`) and `r = 1` (`true`). -/
def ell {n : ℕ} (c : Fin n → ZMod 3) (ω : ProverCoins n) (i : Fin n) (r : Bool) : ZMod 3 :=
  if r then ω.1 (c i) - ω.2 i else ω.2 i

/-- p.10, commit phase: an honest prover's reply to `((i, j), r)` is `(w_i, w_j) = (ℓ_{ir}, ℓ_{jr})`
if `(i, j) ∈ E`, and it aborts otherwise. -/
def proverReply {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c : Fin n → ZMod 3)
    (ω : ProverCoins n) (q : Query n) : Reply :=
  if IsValid G q then some (ell c ω q.1 q.2.2, ell c ω q.2.1 q.2.2) else none

/-- pp.9–10: the real provers' joint response channel in protocol `Π^(2)_LHV[G, C]`. One draw of the
shared randomness — `Π` uniform among the `3! = 6` permutations of `F₃` and the masks `ℓ_{i0}`
independent and uniform — is used by both provers; prover 1 answers the query `q₁` and prover 2
the query `q₂`. -/
noncomputable def realChannel {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → ZMod 3) : Channel (Query n) (Query n) Reply Reply := fun q₁ q₂ =>
  (PMF.uniformOfFintype (ProverCoins n)).map fun ω =>
    (proverReply G c ω q₁, proverReply G c ω q₂)

end RelativisticZK205.ThreeCol


