-- Prove2me | Definitions.Def_ClawFreeChoosable_SatisfiesM
-- name    : ClawFreeChoosable_SatisfiesM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:17.919677+00:00
-- url     : https://prove2.me/theorems/3faac9ea-c08d-4368-9582-c8526b431bd3
-- title:
--   The mixed-list property (Mk)
-- statement:
--   Let $G$ be a graph and $k$ a nonnegative integer.
--
--   An **(Mk)-instance** is a tuple $(G, Q, r, L)$ where $r \ge 0$ is an integer, $Q$ is an attachable clique of $G$ with $|Q| + r \le k$, and $L$ is a list assignment on $V(G)$ with
--   $$|L(v)| \ge \begin{cases} k - r, & v \in Q,\\ k, & v \notin Q.\end{cases}$$
--   The instance is **colourable** if $G$ has a proper $L$-colouring. $G$ **satisfies (Mk)** if every (Mk)-instance on $G$ is colourable.
--
--   Deleting the colours of a precoloured simplicial clique $S$ from the lists on $Q = N_G(S)$ turns a (Pk)-instance into an equivalent (Mk)-instance on $G - S$ (Lemma 7.3).
--
--   **Formalization Note** $|Q|$ is the cardinality of $Q$; because $|Q| + r \le k$, the natural-number difference $k - r$ is not truncated. Colourability is the published `OAI.LinearListHadwiger.ListColorable`. As for (Pk), $k \ge \omega(G)$ is a hypothesis of each theorem, not part of the property.
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Definition 7.2, p.10

import Mathlib
import Definitions.Def_ListHadwiger
import Definitions.Def_ClawFreeChoosable_IsAttachable

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **(Mk)-instance** (arXiv:2611.01068v1, Definition 7.2, p.10): `(G, Q, r, L)` where `r ≥ 0` is
an integer, `Q` is an attachable clique of `G` with `|Q| + r ≤ k`, and `L` is a list assignment
on `V(G)` with `|L(v)| ≥ k − r` for `v ∈ Q` and `|L(v)| ≥ k` for `v ∉ Q`.

**Formalization Note.** `|Q|` is `Set.ncard Q`, the cardinality on the finite vertex types used
throughout. Since `|Q| + r ≤ k`, the natural-number subtraction `k - r` is not truncated. The
standing requirement `k ≥ ω(G)` is a separate hypothesis of each theorem. -/
def IsMInstance {V α : Type} (G : SimpleGraph V) (k : ℕ) (Q : Set V) (r : ℕ)
    (L : V → Finset α) : Prop :=
  IsAttachable G Q ∧ Q.ncard + r ≤ k ∧ (∀ v ∈ Q, k - r ≤ (L v).card) ∧
    ∀ v, v ∉ Q → k ≤ (L v).card

/-- `G` **satisfies (Mk)** (arXiv:2611.01068v1, Definition 7.2, p.10): every (Mk)-instance on `G`,
over every colour type, is colorable, i.e. `G` has a proper `L`-colouring (the published
`OAI.LinearListHadwiger.ListColorable`). -/
def SatisfiesM {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (α : Type) (Q : Set V) (r : ℕ) (L : V → Finset α),
    IsMInstance G k Q r L → OAI.LinearListHadwiger.ListColorable G L

end ClawFreeChoosable


