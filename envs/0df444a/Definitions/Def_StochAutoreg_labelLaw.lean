-- Prove2me | Definitions.Def_StochAutoreg_labelLaw
-- name    : StochAutoreg_labelLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:16:15.938567+00:00
-- url     : https://prove2.me/theorems/65a29614-1eef-447b-b9ba-fa44ffcb3f86
-- title:
--   Law of a labelled sample $(X,Y)$, $Y\mid X\sim\mathrm{Bern}(p(X))$
-- statement:
--   For a prompt law $P$ and a function $p:\Sigma^\star\to[0,1]$, the law of $(X,Y)$ with $X\sim P$ and $Y\mid X\sim\mathrm{Bern}(p(X))$. With $p=p_{g_\star}$ this is one **base** sample of the paper; the same law is the sample of Lemma 4.1.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §1.1, p.3

import Mathlib
import Definitions.Def_StochAutoreg_bernPMF

namespace StochAutoreg

/-- The law of one labelled sample `(X, Y)` with `X ∼ P` and `Y | X ∼ Bern(p(X))`.
With `p = g` this is the **base** sample `(X_i, Y_i)`, `Y_i | X_i ∼ Bern(p_{g⋆}(X_i))`, of p.3; the same
law is the sample of Lemma 4.1, p.10. Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §1.1, p.3.

**Formalization Note.** The mass at `(x, y)` is `P x * bernMass (p x) y` (verification file). -/
noncomputable def labelLaw (P : PMF (List Bool)) (p : List Bool → unitInterval) :
    PMF (List Bool × Bool) :=
  P.bind fun x => (bernPMF (p x)).map fun y => (x, y)

end StochAutoreg


