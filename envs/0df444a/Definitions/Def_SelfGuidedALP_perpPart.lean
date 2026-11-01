-- Prove2me | Definitions.Def_SelfGuidedALP_perpPart
-- name    : SelfGuidedALP_perpPart
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:27:53.749661+00:00
-- url     : https://prove2.me/theorems/271d7ceb-6386-48e8-ba17-c2354be47f9d
-- title:
--   The component $B^{\perp}_N$ of $B$ in $\bar{\mathcal B}_N^\perp$
-- statement:
--   For $B\in\mathcal B$, $B^\perp_N$ is the orthogonal projection of $B$ onto $\bar{\mathcal B}_N^\perp$. For $B=B^*$ this is the paper's $B^{*,\perp}_N$.
--
--   It is the only quantity through which the first $N$ samples enter the goal's constant.
--
--   **Formalization Note** Any decomposition $B=B^o+B^\perp$ as in Proposition EC.2(iii) has this projection as its orthogonal part; the verification file proves it. Because $\bar{\mathcal B}_N=\{0\}$ under the printed definition, this projection is $B$ itself.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Proposition EC.2(iii), p.ec8

import Mathlib
import Definitions.Def_SelfGuidedALP_BNbar

namespace SelfGuidedALP

/-- `B^⊥_N`, the component of `B` in `ℬ̄_N^⊥`: the orthogonal projection of `B` onto `ℬ̄_N^⊥`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Proposition EC.2(iii), p.ec8). For `B = B*` this is `B^{*,⊥}_N`. -/
noncomputable def perpPart {d N : ℕ} (R : RBClass d) (θs : Fin N → EuclideanSpace ℝ (Fin (d + 1)))
    (B : Bspace R) : Bspace R :=
  ((BNbar R θs)ᗮ.orthogonalProjectionOnto B : (BNbar R θs)ᗮ)

end SelfGuidedALP


