-- Prove2me | Definitions.Def_ElimAgree_CostLE
-- name    : ElimAgree_CostLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:53.821188+00:00
-- url     : https://prove2.me/theorems/425b99e5-7915-4287-bece-5a3cdf10a2ec
-- title:
--   Cost and failure probability of a public-coin protocol
-- statement:
--   Protocol trees are the published deterministic two-party trees `OneOfManyCC.Protocol α β L` (reference item): each internal node belongs to Alice (input $x\in\alpha$) or Bob (input $y\in\beta$) and carries a bit-valued function of that party's input only; the run continues in the left subtree on $0$ and in the right subtree on $1$; each leaf carries a label in $L$. The **depth** of a tree is the number of bits sent on the longest path, and $T(x,y)$ is the label of the leaf reached on $(x,y)$.
--
--   A **public-coin protocol** (which may also use private coins) is a probability distribution $\mu$ over such trees: once the public coins and both parties' private coins are fixed, a deterministic tree remains. Its **cost** is at most $c$ when every tree in the support of $\mu$ has depth at most $c$. For a failure predicate $E$ on labels, the failure probability on input $(x,y)$ is
--   $$\Pr_{T\sim\mu}\big[E(T(x,y))\big].$$
--
--   These objects carry every model of Definition 2.1; the leaf labels fix the output convention.
--
--   **Formalization Note** The distribution is a `PMF` over `OneOfManyCC.Protocol α β L`; probabilities are values in $[0,\infty]$ (`ENNReal`).
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Definition 2.1, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_OneOfManyCC_Protocol

namespace ElimAgree

variable {α β L : Type}

/-- Cost at most `c` of a public-coin protocol (Ben Daniel, *Can Many Instances Be Cheaper Than
One? The Price of Agreement in Elimination*, manuscript, STOC 2027 submission, Definition 2.1,
p.6): every deterministic tree in the support of `μ` sends at most `c` bits on every input
(worst-case communication over inputs and coins).

**Formalization Note.** The trees are the published `OneOfManyCC.Protocol α β L`: each internal
node belongs to Alice or Bob and carries a bit-valued function of that party's input only
(`false` selects `p₀`, `true` selects `p₁`), each leaf carries a label in `L`; `depth` is the
number of bits on the longest path and `eval` the label reached on `(x, y)`. A public-coin
protocol (which may also use private coins) is a probability distribution `PMF` over such trees:
once the public coins and both parties' private coins are fixed, a deterministic tree remains,
and conversely every distribution over trees is a public-coin protocol. The leaf labels fix the
output convention (see `ComLabel`). -/
def CostLE (μ : PMF (OneOfManyCC.Protocol α β L)) (c : ℕ) : Prop :=
  ∀ T ∈ μ.support, T.depth ≤ c

/-- The probability, over the coins of the protocol `μ`, that the leaf label reached on input
`(x, y)` satisfies the failure predicate `E` (Definition 2.1, p.6). -/
noncomputable def failProb (μ : PMF (OneOfManyCC.Protocol α β L)) (x : α) (y : β)
    (E : L → Prop) : ENNReal :=
  μ.toOuterMeasure {T | E (T.eval x y)}

end ElimAgree


