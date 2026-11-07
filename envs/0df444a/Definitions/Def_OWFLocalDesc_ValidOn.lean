-- Prove2me | Definitions.Def_OWFLocalDesc_ValidOn
-- name    : OWFLocalDesc_ValidOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:44:32.878741+00:00
-- url     : https://prove2.me/theorems/b835931a-6d8d-40c4-b678-eb1f4c41a869
-- title:
--   Validity of a certificate on a tape (Definition 2.5)
-- statement:
--   Let $(x,y)$ be a dataset with points $x_1,\dots,x_m\in\{0,1\}^n$ and labels $y\in\{0,1\}^m$. A certificate is **valid on the tape** $w$ (at clock $t$) if its hypothesis on $w$ returns $y_i$ on the query $x_i$ for every $i\in[m]$.
--
--   The tags need not equal the true labels.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition 2.5, p.12

import Mathlib
import Definitions.Def_OWFLocalDesc_Certificate
import Definitions.Def_OWFLocalDesc_hyp
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Validity of a certificate on a tape (Definition 2.5).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e),
Definition 2.5, p.12: "The certificate is valid on the tape w if, on that tape, the hypothesis
returns y_i on the query x_i for every i ∈ [m]."

For a dataset `(x, y)` with points `x i ∈ {0,1}ⁿ` and labels `y i`, the certificate `c` is
valid on `w` at clock `t` when its hypothesis returns `y i` on every query `x i`. -/
def ValidOn (U : Decoder) (t : ℕ) {m n : ℕ} (x : Fin m → Fin n → Bool) (y : Fin m → Bool)
    (w : List Bool) (c : Certificate m) : Prop :=
  ∀ i : Fin m, hyp U c.prog (c.anchorList x) w (List.ofFn (x i)) t = y i

end OWFLocalDesc


