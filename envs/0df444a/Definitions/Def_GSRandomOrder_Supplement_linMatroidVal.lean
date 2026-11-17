-- Prove2me | Definitions.Def_GSRandomOrder_Supplement_linMatroidVal
-- name    : GSRandomOrder_Supplement_linMatroidVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:09:41.348536+00:00
-- url     : https://prove2.me/theorems/4ce176d3-b9c4-4aad-a3eb-7cd2124f927a
-- title:
--   Weighted matroid valuation (31) of a represented matroid
-- statement:
--   Let $M$ be a matroid on $N$ represented over a field $\mathbb F$ by vectors $u_g\in\mathbb F^d$, that is, $X$ is independent exactly when $(u_g)_{g\in X}$ is linearly independent, and let $w_g\in\mathbb R$ be weights, possibly negative. The **weighted matroid valuation** is
--   $$
--   v(S)=\sum_{g\in S}w_g\quad\text{if }S\text{ is independent},\qquad v(S)=-\infty\ \text{otherwise}.\qquad(31)
--   $$
--   By Lemma 2.6 of the paper it is a GS valuation; it is the valuation of the bidders of Theorem E.1.
--
--   **Formalization Note** Independence is `LinearIndepOn K u S`, linear independence of the family $(u_g)_{g\in S}$; every matroid representable over $\mathbb F$ arises this way, and $v$ depends on the matroid only. $-\infty$ is $\bot$ in `WithBot ℝ`.
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), App. E, p.31, eq. (31) and the definition of a represented matroid

import Mathlib

set_option autoImplicit false

namespace GSRandomOrder.Supplement

open Classical in
/-- **Weighted matroid valuation** (31) of a represented matroid (R. Paes Leme, M. Pál, N. Patel,
*Gross Substitutes Welfare in Random Order*, STOC 2027 submission, manuscript sha256 69787f50…,
App. E, p.31, eq. (31)). The matroid `M` on `N` is represented over `K` by vectors
`u_g ∈ K^d`: `X` is independent iff `(u_g)_{g ∈ X}` is linearly independent. With real weights
`w_g` (possibly negative), `v(S) = Σ_{g ∈ S} w_g` if `S` is independent and `v(S) = −∞`
otherwise.

**Formalization Note.** Independence is `LinearIndepOn K u S` (the family `(u_g)_{g ∈ S}`, so a
repeated vector makes a set dependent). `−∞` is `⊥ : WithBot ℝ`. Every matroid representable over
`K` arises in this way, and the valuation depends on the matroid only. -/
noncomputable def linMatroidVal {n : ℕ} {K : Type*} [Semiring K] {d : ℕ} (u : Fin n → Fin d → K)
    (w : Fin n → ℝ) : Finset (Fin n) → WithBot ℝ :=
  fun S => if LinearIndepOn K u (S : Set (Fin n)) then ((∑ g ∈ S, w g : ℝ) : WithBot ℝ) else ⊥

end GSRandomOrder.Supplement


