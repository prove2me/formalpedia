-- Prove2me | Definitions.Def_OWFLocalDesc_gmin
-- name    : OWFLocalDesc_gmin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:46:10.930125+00:00
-- url     : https://prove2.me/theorems/3d5673b8-55f3-4701-970f-97c31b44a639
-- title:
--   Minimum valid charged length $g^t_w(x,y)$ (Definition 2.5)
-- statement:
--   For a clock $t$, a tape $w$ and a dataset $(x,y)$,
--   $$g^t_w(x,y)=\min\{\text{price of } c : c \text{ is a certificate valid on } w\},$$
--   and $g^t_w(x,y)=\infty$ if no certificate is valid on $w$.
--
--   **Formalization Note** The value lies in $\mathbb N\cup\{\infty\}$ (`ℕ∞`), where the infimum of the empty family is $\infty$.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition 2.5, p.13

import Mathlib
import Definitions.Def_OWFLocalDesc_price
import Definitions.Def_OWFLocalDesc_ValidOn
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Minimum valid charged length `g^t_w(x,y)` (Definition 2.5).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e),
Definition 2.5, p.13: "For each tape w, let g^t_w(x,y) be the minimum charged length of a
certificate valid on w, or ∞ if no such certificate exists."

**Formalization Note.** The value is in `ℕ∞`; the infimum of the empty family is `⊤ = ∞`. -/
noncomputable def gmin (U : Decoder) (t : ℕ) {m n : ℕ} (x : Fin m → Fin n → Bool)
    (y : Fin m → Bool) (w : List Bool) : ℕ∞ :=
  ⨅ (c : Certificate m) (_ : ValidOn U t x y w c), (price c : ℕ∞)

end OWFLocalDesc


