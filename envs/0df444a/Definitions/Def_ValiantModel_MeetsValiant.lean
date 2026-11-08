-- Prove2me | Definitions.Def_ValiantModel_MeetsValiant
-- name    : ValiantModel_MeetsValiant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:30.980767+00:00
-- url     : https://prove2.me/theorems/d42e7b54-cc3b-42be-8f3c-94a57825c03b
-- title:
--   The conclusions of Definition 1: no false positives, and false-negative mass at most $\varepsilon$
-- statement:
--   Given a target $h$, a distribution $D$ and an error parameter $\varepsilon$, a hypothesis $g$ **meets the conclusions of Definition 1** if
--
--   $$
--   \mathrm{supp}(g)\subseteq\mathrm{supp}(h)\qquad\text{and}\qquad \Pr_{x\sim D}\bigl(x\notin\mathrm{supp}(g)\bigr)\le\varepsilon .
--   $$
--
--   The first condition is one-sided: no false positive is allowed at any point of the domain, whatever its mass. The second bounds the false negatives under $D$.
--
--   **Formalization Note** The mass is `PMF.toOuterMeasure`, valued in $[0,\infty]$, and $\varepsilon$ enters through `ENNReal.ofReal`; every use has $\varepsilon>0$.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.1 (PDF p.3), Definition 1

import Mathlib
import Definitions.Def_ValiantModel_ConceptSequence

namespace ValiantModel

/-- **The conclusions of Definition 1**, arXiv:2605.13840 (version held), p.1 (PDF p.3), for an
output hypothesis `g`, a target `h`, a distribution `D` and an error parameter `ε`:
`supp(g) ⊆ supp(h)` and `Pr_{x∼D}(x ∉ supp(g)) ≤ ε`.

**Formalization Note.** The mass of `{x | g x = false}` is `ℝ≥0∞`-valued (`PMF.toOuterMeasure`),
and `ε : ℝ` enters through `ENNReal.ofReal`; every use has `0 < ε`. -/
def MeetsValiant {d : ℕ} (h : Hypothesis d) (D : PMF (Point d)) (ε : ℝ) (g : Hypothesis d) :
    Prop :=
  supp g ⊆ supp h ∧ D.toOuterMeasure {x | g x = false} ≤ ENNReal.ofReal ε

end ValiantModel


