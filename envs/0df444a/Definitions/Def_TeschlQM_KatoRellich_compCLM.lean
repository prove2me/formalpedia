-- Prove2me | Definitions.Def_TeschlQM_KatoRellich_compCLM
-- name    : TeschlQM_KatoRellich_compCLM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T22:06:35.459991+00:00
-- url     : https://prove2.me/theorems/814f4d67-9cd0-489c-b619-f5412ee613f5
-- title:
--   The product B R of an operator with a bounded operator (BR_A(z))
-- statement:
--   For a linear operator $B$ with domain $\mathfrak{D}(B)$ and a bounded, everywhere defined operator $R \in \mathfrak{L}(\mathfrak{H})$, the product $BR$ is the operator
--   $$\mathfrak{D}(BR) = \{ \varphi \in \mathfrak{H} \mid R\varphi \in \mathfrak{D}(B) \}, \qquad (BR)\varphi = B(R\varphi).$$
--
--   With $R = R_A(z)$ this is the operator $BR_A(z)$ of Lemmas 6.2 and 6.3. When $\mathfrak{D}(A) \subseteq \mathfrak{D}(B)$ its domain is all of $\mathfrak{H}$.
--
--   **Formalization Note.** `compCLM B R` is a `LinearPMap` with domain `B.domain.comap R`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 134, Section 6.1 (notation of Lemma 6.2)

import Mathlib

namespace TeschlQM.KatoRellich

/-- The product `B R` of an operator `B : 𝔇(B) → ℌ` with an everywhere defined bounded operator
`R ∈ L(ℌ)`, in the usual sense of unbounded operators: `𝔇(BR) = {φ ∈ ℌ | Rφ ∈ 𝔇(B)}` and
`(BR)φ = B(Rφ)`. With `R = R_A(z)` this is Teschl's `BR_A(z)` (p. 134). -/
noncomputable def compCLM {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (B : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) : H →ₗ.[ℂ] H where
  domain := B.domain.comap (R : H →ₗ[ℂ] H)
  toFun := B.toFun.comp ((R : H →ₗ[ℂ] H).restrict (fun _ hx => hx))

end TeschlQM.KatoRellich


