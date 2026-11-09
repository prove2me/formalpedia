-- Prove2me | Definitions.Def_KSPolySign_certZ
-- name    : KSPolySign_certZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:39:36.476203+00:00
-- url     : https://prove2.me/theorems/8710b79b-7427-458e-a0ff-c33e773400a3
-- title:
--   The certificate quantity $\mathfrak z$
-- statement:
--   $$\mathfrak z = 2\mathfrak u + \delta F - \frac Fk\Big(1-\frac{j}{(1+j_0)^2}\Big),$$
--   a function of $(y,u,v)$ (Definition 3.20). (Fraktur $\mathfrak z$, not $z_i$ or $z:=y_i$.)
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32 (PDF p.32)

import Mathlib
import Definitions.Def_KSPolySign_certU
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The certificate quantity `𝔷 = 2𝔲 + δF − (F/k)(1 − j/(1 + j₀)²)`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32
(PDF p.32) (fraktur `𝔷`, not `z_i` or `z := y_i`). -/
noncomputable def certZ (y u v : ℝ) : ℝ :=
  2 * certU y u v + deltaC y u v * certF y u v -
    certF y u v / kC y u v * (1 - jC y u v / (1 + j0) ^ 2)

end KSPolySign


