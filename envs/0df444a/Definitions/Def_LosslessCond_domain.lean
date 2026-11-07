-- Prove2me | Definitions.Def_LosslessCond_domain
-- name    : LosslessCond_domain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:34:13.863199+00:00
-- url     : https://prove2.me/theorems/1972517d-492c-499b-bdad-d1f5406c593a
-- title:
--   Protocol domain $G_P(U)$
-- statement:
--   Let $M:X\times Y\to\{0,1\}$ be a Boolean matrix, $U\subseteq X$ a set of rows, and $P$ a partial protocol of depth $s$. A column $y\in Y$ is **compatible** with $P$ on $U$ if there is **one** assignment $\beta$ of bits to all Bob nodes such that the tree is correct on every pair $(x,y)$ with $x\in U$:
--   $$
--   G_P(U)=\{\,y\in Y:\ \exists\beta\ \ \forall x\in U,\ \ \mathrm{run}_P(\beta,x)=M(x,y)\,\}.
--   $$
--   The set $G_P(U)$ is the **protocol domain** of $P$ on $U$. The assignment may depend on $y$ (Bob knows his input) but not on $x$. If $U=\emptyset$, every column is compatible.
--
--   Protocol domains are the column sets on which a short protocol with fixed Alice instructions can be completed; Lemma 3.2 relates them to the communication cost of restrictions.
--
--   **Formalization Note** The domain is defined directly by this condition, not by the intersection/union recursion of §3.2, which is a separate theorem.
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), Definition 3.1, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_LosslessCond_PartialProtocol

namespace LosslessCond

/-- The **protocol domain** `G_P(U)` (Mackenzie, arXiv:2609.28691, held version sha256 ce75e6d4…,
Definition 3.1, p.8): a column `y` is *compatible* with the partial protocol `P` on the row set `U`
if there is **one** assignment `β` of bits to all Bob nodes that makes the tree correct on every
pair `(x, y)` with `x ∈ U`; `G_P(U)` is the set of compatible columns.

**Formalization Note** The assignment `β` may depend on `y` but not on `x`: the existential is
outside the quantifier over rows (p.8: "The assignment may depend on y, since Bob knows his own
input. It may not depend on x"). If `U` is empty, every column is compatible, as on p.8. The
domain is defined directly from this condition, not by the intersection/union recursion of §3.2,
which is a theorem of the mission. -/
def domain {X Y : Type} {s : ℕ} (M : X → Y → Bool) (P : PartialProtocol X s) (U : Set X) :
    Set Y :=
  {y | ∃ β : P.BobBits, ∀ x ∈ U, P.run β x = M x y}

end LosslessCond


