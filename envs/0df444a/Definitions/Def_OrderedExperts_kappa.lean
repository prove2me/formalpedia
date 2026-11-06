-- Prove2me | Definitions.Def_OrderedExperts_kappa
-- name    : OrderedExperts_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:37.930106+00:00
-- url     : https://prove2.me/theorems/c046dec5-097d-48fd-ab99-7e2b02841dc5
-- title:
--   The pair kernel $\kappa$
-- statement:
--   For a chain of $m$ active ranks with intended distribution $\pi$, the **pair kernel** is
--   $$
--   \kappa(b,a)=\frac{\Gamma(a,b)}{\pi(b)}\quad(a\ne b),\qquad
--   \kappa(b,b)=1-\sum_{a\ne b}\kappa(b,a),
--   $$
--   the sum running over the active ranks $a\in\{1,\dots,m\}$. Algorithm 1's sampler draws $A\sim\pi$ and then $B\sim\kappa(A,\cdot)$, so the queried pair has law $P(A=a,B=b)=\pi(a)\kappa(a,b)$.
--
--   **Formalization Note** The diagonal is not clipped at $0$: that it is nonnegative (indeed at least $1/2$) under the floor is Lemma 2.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Sec. 3.3, p.8; Algorithm 1, p.9

import Definitions.Def_OrderedExperts_gamma

namespace OrderedExperts

/-- **The pair kernel `κ`.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Sec. 3.3, p.8: "define the kernel
`κ(b, a) = Γ(a, b)/π(b)` (`a ≠ b`), `κ(b, b) = 1 − Σ_{a≠b} κ(b, a)`." Algorithm 1 (p.9): "Draw
`A ∼ π` and then `B ∼ κ(A, ·)`".

`kappa m ξ π b a = κ(b, a)` is the probability of moving from rank `b` to rank `a`; the diagonal is
`1` minus the off-diagonal row mass over the active ranks `a ∈ {1, …, m}`, `a ≠ b`.

**Formalization Note.** The diagonal is not clipped at `0`: its nonnegativity is the content of
Lemma 2 (`OrderedExperts.lemma_2`). -/
noncomputable def kappa (m : ℕ) (ξ : ℝ) (π : ℕ → ℝ) (b a : ℕ) : ℝ :=
  if a = b then 1 - ∑ a' ∈ (Finset.Icc 1 m).erase b, gamma m ξ π a' b / π b
  else gamma m ξ π a b / π b

end OrderedExperts


