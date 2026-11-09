-- Prove2me | Definitions.Def_KSPolySign_IsLight
-- name    : KSPolySign_IsLight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:38:04.623578+00:00
-- url     : https://prove2.me/theorems/a89ae362-72ef-49f7-8c52-a170bfdfc4ad
-- title:
--   Light states
-- statement:
--   A fractional signing $y\in[-1,1]^k$ is **light** when its optimizer $(b,U,V)$ satisfies, for every active coordinate $i$ (one with $-1<y_i<1$),
--   $$\iota\,\beta(y_i)\,u_i < 1+y_i \qquad\text{and}\qquad \iota\,\beta(y_i)\,v_i < 1-y_i,$$
--   where $u_i = a_i^*Ua_i$ and $v_i=a_i^*Va_i$ for $C_i=a_ia_i^*$. At a state that is not light some coordinate can be moved to an endpoint without increasing the potential (Lemma 3.10).
--
--   **Formalization Note** $a_i^*Ua_i=\mathrm{tr}[C_iU]$. The optimizer is unique (Lemma 3.7(a)), so "its optimizer" is written as "some optimizer".
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.9, p.22 (PDF p.22); Definition 3.8, pp.21–22; Definition 2.3, p.7

import Mathlib
import Definitions.Def_KSPolySign_IsOptimal
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Light states.** `y ∈ [−1, 1]^k` is light when, for its optimizer `(b, U, V)`, every active
coordinate `i` (`−1 < y_i < 1`) satisfies `ι β_i u_i < 1 + y_i` and `ι β_i v_i < 1 − y_i`, where
`β_i = β(y_i)`, `u_i = a_i* U a_i`, `v_i = a_i* V a_i` for `C_i = a_i a_i*`.
Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.9, p.22 (PDF p.22), with Definition 3.8, pp.21–22; Definition 2.3, p.7.

**Formalization Note** For `C_i = a_i a_i*`, `a_i* U a_i = tr[C_i U]`, the form Algorithm 3 uses
(line 18, p.69). The optimizer is unique by Lemma 3.7(a), so "for its optimizer" is written as
"for some optimizer". -/
def IsLight {n k : ℕ} (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ)
    (ρ : ℝ) (y : Fin k → ℝ) : Prop :=
  (∀ i, |y i| ≤ 1) ∧ ∃ (b : ℝ) (U V : Matrix (Fin n) (Fin n) ℂ), IsOptimal C F ρ y b U V ∧
    ∀ i, |y i| < 1 →
      iota * beta (y i) * (C i * U).trace.re < 1 + y i ∧
      iota * beta (y i) * (C i * V).trace.re < 1 - y i

end KSPolySign


