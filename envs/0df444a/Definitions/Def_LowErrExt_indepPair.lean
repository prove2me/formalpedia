-- Prove2me | Definitions.Def_LowErrExt_indepPair
-- name    : LowErrExt_indepPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:17.077669+00:00
-- url     : https://prove2.me/theorems/24444ed2-06fc-4315-8fd0-eafa305b93f0
-- title:
--   Independent pair of sources $(\mathbf X,\mathbf Y)$
-- statement:
--   For probability distributions $\mathbf X$ on a set $A$ and $\mathbf Y$ on a set $B$, the **independent pair** $(\mathbf X,\mathbf Y)$ is the product distribution on $A\times B$:
--   $$\Pr[(\mathbf X,\mathbf Y)=(x,y)]=\Pr[\mathbf X=x]\cdot\Pr[\mathbf Y=y].$$
--   The law of $f(\mathbf X,\mathbf Y)$ for independent sources is the image of this product under $f$. The paper writes $f(\mathbf X,\mathbf Y)$ with the sources "treated as independent".
--
--   **Formalization Note** Sources are probability mass functions; the product is built by binding $\mathbf X$ and mapping $\mathbf Y$.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), §2, p.10

import Mathlib

namespace LowErrExt

/-- **Independent pair of sources.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…), §2, p.10:
"For sets X, Y we let f(X, Y) denote the image of the set, where they are treated as independent."

`indepPair X Y` is the joint law of `(X, Y)` with `X`, `Y` independent: the product of the two
probability mass functions. The law of `f(X, Y)` for independent `X, Y` is `(indepPair X Y).map f`.

**Formalization Note.** Sources are probability mass functions (`PMF`); "`X ∼ S`" (support contained
in `S`) is the ambient type itself, or an explicit support condition where the paper names a subset. -/
noncomputable def indepPair {α β : Type*} (X : PMF α) (Y : PMF β) : PMF (α × β) :=
  X.bind fun x => Y.map fun y => (x, y)

end LowErrExt


