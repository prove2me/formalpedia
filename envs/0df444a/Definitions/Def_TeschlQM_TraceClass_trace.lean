-- Prove2me | Definitions.Def_TeschlQM_TraceClass_trace
-- name    : TeschlQM_TraceClass_trace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T09:30:56.339542+00:00
-- url     : https://prove2.me/theorems/2f771864-8dd8-4226-a1b2-582db99f1828
-- title:
--   The trace tr(K), Eq. (6.26)
-- statement:
--   Let $\mathfrak{H}$ be a complex Hilbert space and fix an orthonormal basis $\{\varphi_n\}$ of $\mathfrak{H}$. For $K \in \mathfrak{L}(\mathfrak{H})$ the **trace** is
--   $$\operatorname{tr}(K) = \sum_n \langle \varphi_n, K\varphi_n \rangle.$$
--   For trace class $K$ the series converges and its value does not depend on the orthonormal basis (Lemma 6.15, the goal of this mission).
--
--   **Formalization Note.** The basis is a fixed choice (`Classical.choose` of Mathlib's `exists_hilbertBasis`), indexed by a subset of $\mathfrak{H}$; no separability is assumed. The sum is Mathlib's `tsum`, which is $0$ for a non-summable family, so the value carries meaning only for trace class $K$, the only case in which it is used. The inner product is conjugate-linear in the first argument, as in the book.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 143, Lemma 6.15, Eq. (6.26)

import Mathlib

namespace TeschlQM.TraceClass

open scoped InnerProductSpace

/-- A fixed (choice of) orthonormal basis of `ℌ`, indexed by a subset of `ℌ`. -/
noncomputable def someONB (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : HilbertBasis (Classical.choose (exists_hilbertBasis ℂ H) : Set H) ℂ H :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))

/-- Teschl (6.26), p. 143: the **trace** `tr(K) = ∑_n ⟨φ_n, Kφ_n⟩`, computed in one fixed orthonormal
basis `{φ_n}` of `ℌ`. By Lemma 6.15 the series converges and its value does not depend on the basis
when `K` is trace class; only that case is ever used. (For a non-summable family Mathlib's `tsum` is
`0`, so the value off the trace class carries no meaning.) -/
noncomputable def trace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K : H →L[ℂ] H) : ℂ :=
  ∑' n, ⟪someONB H n, K (someONB H n)⟫_ℂ

end TeschlQM.TraceClass


