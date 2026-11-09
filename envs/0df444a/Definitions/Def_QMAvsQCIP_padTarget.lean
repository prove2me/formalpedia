-- Prove2me | Definitions.Def_QMAvsQCIP_padTarget
-- name    : QMAvsQCIP_padTarget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:26.027207+00:00
-- url     : https://prove2.me/theorems/099b95c9-1240-4980-90bd-69b081297753
-- title:
--   Target $y\|0^{q-\lambda}$
-- statement:
--   For $y\in\{0,1\}^\lambda$, the target $y\|0^{q-\lambda}\in\{0,1\}^q$ has coordinate $i$ equal to $y_i$ for $i<\lambda$ and $0$ for $\lambda\le i<q$.
--
--   It is the target of the YES oracles ($O(y,v)=1$ iff $H(v)=y\|0^{q-\lambda}$) and of the decoder in Lemma 2 and the verifier of Section 7.1.
--
--   **Formalization Note** Coordinates $i\in[q]$ are the elements $\alpha$ of `ZMod q`, ordered by $\alpha$'s representative.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Definition 8, p.24; Lemma 2, p.18

import Mathlib

set_option autoImplicit false

namespace QMAvsQCIP

/-- The target `y ∥ 0^{q−λ} ∈ {0,1}^q` for `y ∈ {0,1}^λ`: coordinate `i` is `y_i` for `i < λ` and
`0` otherwise.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Definition 8, p.24 (PDF p.27): "O(y, v) = 1 if H(v) = y∥0^{q−λ}, 0 otherwise"; Lemma 2,
p.18 (PDF p.21): "Decode(y∥0^{q−λ}, |Ψ_H⟩)"; Section 3.1, p.13: "x∥y for concatenation".

**Formalization Note.** Coordinates `i ∈ [q]` are the elements `α` of `ZMod q`, in the order of
`α.val`, so "the first `λ` coordinates" are `α.val < λ`. -/
def padTarget (lam q : ℕ) (y : Fin lam → Bool) : ZMod q → Bool :=
  fun α => if h : α.val < lam then y ⟨α.val, h⟩ else false

end QMAvsQCIP


