-- Prove2me | Definitions.Def_SingleOrSample_multiBucketLaw
-- name    : SingleOrSample_multiBucketLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:33.799858+00:00
-- url     : https://prove2.me/theorems/9d9b72c1-74bf-442b-9e0f-29ec9ecc66ee
-- title:
--   Multi-bucket SwR with adaptive buckets and probabilities
-- statement:
--   A single iteration of the **multi-bucket SwR** process on a finite set $G$ with probability bound $p$ runs as follows. Starting from $G^{(0)}=G$ and $A=\emptyset$, while $G^{(\ell)}$ is nonempty, a nonempty subset $B^{(\ell)}\subseteq G^{(\ell)}$ and a probability $p^\ell\le p$ are chosen; $A^{(\ell)}$ is drawn from $\mathrm{SwR}(B^{(\ell)},p^\ell)$; then $G^{(\ell+1)}=G^{(\ell)}\setminus B^{(\ell)}$ and $A^{(\ell)}$ is added to $A$.
--
--   The buckets and probabilities may depend on the entire history of the iteration, which here means a **rule** mapping histories to pairs $(B^{(\ell)},p^\ell)$.
--
--   **Formalization Note** The law is on the list of triples (bucket, probability, sample). The fuel $|G|+1$ of the recursion is never exhausted by a valid rule, since each bucket is nonempty and leaves $G^{(\ell)}$. The iterated process across several iterations (Lemmas 2.3 and B.3) is not part of this mission.
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Definition 4, p.8

import Mathlib
import Definitions.Def_SingleOrSample_swr

open scoped Classical

namespace SingleOrSample

/-- The sampled set `A_i = ∪_ℓ A^(ℓ)` of a multi-bucket history, whose entries are (bucket, probability,
sample) (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for
Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286, manuscript sha256 28cd3d7b…, Definition 4,
p.8). -/
noncomputable def sampledSet {α : Type*} (l : List (Finset α × unitInterval × Finset α)) : Finset α :=
  l.foldl (fun A e => A ∪ e.2.2) ∅

/-- The set `G^(ℓ)` after the buckets of a multi-bucket history have left `G` (Definition 4, p.8). -/
noncomputable def mbRemaining {α : Type*} (G : Finset α) (l : List (Finset α × unitInterval × Finset α)) : Finset α :=
  l.foldl (fun R e => R \ e.1) G

/-- A rule for the **multi-bucket SwR** process on `G` with probability bound `p` (Definition 4, p.8):
while `G^(ℓ)` is nonempty, it maps the whole history of the iteration to a nonempty subset `B^(ℓ)` of
`G^(ℓ)` and a probability `p^ℓ ≤ p`. Both may depend adaptively on the history. -/
def IsMultiBucketRule {α : Type*} (G : Finset α) (p : unitInterval)
    (rule : List (Finset α × unitInterval × Finset α) → Finset α × unitInterval) : Prop :=
  ∀ l, (mbRemaining G l).Nonempty →
    (rule l).1.Nonempty ∧ (rule l).1 ⊆ mbRemaining G l ∧ (rule l).2 ≤ p

/-- The multi-bucket SwR process (Definition 4, p.8), as a law on its history: while `G^(ℓ)` is nonempty,
ask the rule for a bucket and a probability, draw from `SwR(B^(ℓ), p^ℓ)`, and continue.

**Formalization Note.** `fuel` makes the recursion structural; `multiBucketLaw` uses `|G| + 1`, which a
valid rule never exhausts, as each bucket is nonempty and leaves `G^(ℓ)`. -/
noncomputable def mbLoop {α : Type*} (G : Finset α)
    (rule : List (Finset α × unitInterval × Finset α) → Finset α × unitInterval) :
    ℕ → List (Finset α × unitInterval × Finset α) → PMF (List (Finset α × unitInterval × Finset α))
  | 0, l => PMF.pure l
  | fuel + 1, l =>
    if (mbRemaining G l).Nonempty then
      (swr (rule l).1 (rule l).2).bind fun S =>
        mbLoop G rule fuel (l ++ [((rule l).1, (rule l).2, S)])
    else
      PMF.pure l

/-- The law of the history of one multi-bucket SwR iteration on `G` (Definition 4, p.8). -/
noncomputable def multiBucketLaw {α : Type*} (G : Finset α)
    (rule : List (Finset α × unitInterval × Finset α) → Finset α × unitInterval) :
    PMF (List (Finset α × unitInterval × Finset α)) :=
  mbLoop G rule (G.card + 1) []

end SingleOrSample


