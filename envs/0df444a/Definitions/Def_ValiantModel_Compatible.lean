-- Prove2me | Definitions.Def_ValiantModel_Compatible
-- name    : ValiantModel_Compatible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:27.163965+00:00
-- url     : https://prove2.me/theorems/0cccc891-928f-4a46-b949-b39c2be77343
-- title:
--   Definition 4, p.14 — a distribution compatible with a concept
-- statement:
--   A distribution $D$ on $\{0,1\}^d$ is **compatible** with a concept $h$ if a draw from $D$ is positive for $h$ almost surely, that is, $D(\mathrm{supp}(h))=1$.
--
--   This is the condition that makes the example oracle a source of positive examples only. The all-zero function has no compatible distribution, so a learner has no obligation towards it as a target.
--
--   **Formalization Note** On a finite domain a distribution is a `PMF`, and $D(\mathrm{supp}(h))=1$ is written in the equivalent form that every point of positive mass lies in the support.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.14 (PDF p.16), Definition 4

import Mathlib
import Definitions.Def_ValiantModel_ConceptSequence

namespace ValiantModel

/-- **Definition 4 (Compatibility)**, arXiv:2605.13840 (version held), p.14 (PDF p.16): a
distribution `D` over `{0,1}^d` is compatible with `h` if `D(supp h) = 1`.

**Formalization Note.** The domain is finite, so a distribution is a `PMF`, and `D(supp h) = 1` is
equivalent to every point of positive mass lying in `supp h`, which is the form written here. The
all-zero function has no compatible distribution. -/
def Compatible {d : ℕ} (D : PMF (Point d)) (h : Hypothesis d) : Prop :=
  ∀ x ∈ D.support, h x = true

end ValiantModel


