-- Prove2me | Definitions.Def_QMAvsQCIP_bernExp
-- name    : QMAvsQCIP_bernExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:46:30.502121+00:00
-- url     : https://prove2.me/theorems/00469ad6-c041-416a-88ed-2d8a8045ffca
-- title:
--   Expectation under independent Bernoulli values
-- statement:
--   For a finite set $X$, $p\in[0,1]$ and $F$ a real function of $f:X\to\{0,1\}$, the **expectation**
--   $$
--   \mathbb E_f[F(f)]=\sum_{f:X\to\{0,1\}}\Pr[f]\,F(f)
--   $$
--   when the values $f(x)$ are independent Bernoulli$(p)$. The probability of an event $E$ is the expectation of its indicator.
--
--   **Formalization Note** A finite sum.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Section 3.1, p.13

import Definitions.Def_QMAvsQCIP_bernW

set_option autoImplicit false

namespace QMAvsQCIP

/-- The **expectation** `E_f[F(f)] = ∑_f bernW p f · F(f)` of `F` when `f : X → {0,1}` has
independent Bernoulli(`p`) values (`X` finite). The probability of an event `E` is
`bernExp p (E.indicator 1)`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Section 3.1, p.13 (PDF p.16): "µ(z) = Pr_{x←µ}[x = z] and
µ(E) = Pr_{x←µ}[x ∈ E]".

**Formalization Note.** A finite sum; no measurability is involved. -/
noncomputable def bernExp {X : Type} [Fintype X] [DecidableEq X] (p : ℝ)
    (F : (X → Bool) → ℝ) : ℝ :=
  ∑ f : X → Bool, bernW p f * F f

end QMAvsQCIP


