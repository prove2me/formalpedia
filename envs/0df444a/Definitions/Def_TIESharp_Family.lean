-- Prove2me | Definitions.Def_TIESharp_Family
-- name    : TIESharp_Family
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:46.73932+00:00
-- url     : https://prove2.me/theorems/cf78d8d7-26ee-46df-8cd6-41fca0b9e015
-- title:
--   Mechanism family: assignment laws $y^m(b)$ and expected payments $p^m_i(b)$
-- statement:
--   Fix $n$ machines. A **family** consists of one direct-revelation mechanism for each finite job count $m\ge0$. At bids $b\in[0,\infty)^{n\times m}$, the allocation rule specifies weights $y^m_A(b)$ on the assignments $A\in\mathcal A_{m,n}$ (a distribution over assignments), and $p^m_i(b)\in\mathbb R$ is machine $i$'s finite expected net payment (transfers to $i$ counted positively, charges negatively).
--
--   No measurability, continuity, column-locality or independence across jobs is imposed: the lower bound of the paper allows arbitrary correlations among job assignments and "imposes no continuity, differentiability, joint measurability in the reports, or computational restriction".
--
--   **Formalization Note.** A structure with fields `alloc m b A` $=y^m_A(b)$ and `pay m b i` $=p^m_i(b)$. That the weights form a probability vector is the separate predicate `IsFeasible`.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §2, pp.3–4

import Mathlib

set_option autoImplicit false

namespace TIESharp

/-- A **mechanism family** on `n` machines (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, §2, pp.3–4): "For fixed n, a family consists of one mechanism for
each finite m ≥ 0". At job count `m` and bids `b`, `alloc m b A = y^m_A(b)` is the probability of
the assignment `A : [m] → [n]`, and `pay m b i = p^m_i(b) ∈ ℝ` is machine `i`'s finite expected net
payment.

**Formalization Note.** Machines are `Fin n`, jobs `Fin m`, bids `Fin n → Fin m → ℝ`. The
assignment law is a real weight function on the finite set `Fin m → Fin n`; that it is a
probability vector is the separate predicate `IsFeasible`. Payments are real numbers, hence finite.
No measurability, continuity, column-locality or independence across jobs is imposed: the lower
bound "imposes no continuity, differentiability, joint measurability in the reports" (p.4). -/
structure Family (n : ℕ) where
  /-- the assignment probabilities `y^m_A(b)` -/
  alloc : (m : ℕ) → (Fin n → Fin m → ℝ) → (Fin m → Fin n) → ℝ
  /-- the expected net payments `p^m_i(b)` -/
  pay : (m : ℕ) → (Fin n → Fin m → ℝ) → Fin n → ℝ

end TIESharp


