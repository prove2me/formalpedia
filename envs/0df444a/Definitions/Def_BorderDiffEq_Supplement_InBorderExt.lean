-- Prove2me | Definitions.Def_BorderDiffEq_Supplement_InBorderExt
-- name    : BorderDiffEq_Supplement_InBorderExt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:51:33.170967+00:00
-- url     : https://prove2.me/theorems/06d607b1-5881-4755-8cf3-dd1b8a3b70e3
-- title:
--   The border of the extended class $\overline{\text{Ext-}\Sigma^{[k]}\wedge^e\mathcal D(c_1,c_2)}$
-- statement:
--   For classes $\mathcal D_1,\mathcal D_2$ and an exponent bound $e$, the **extended class** is
--   $$
--   \text{Ext-}\Sigma^{[k]}\wedge^e\mathcal D(c_1,c_2)=\Bigl\{\sum_{i=1}^k q_i(x)P_i(x)^{e_i} : P_i\in\mathcal D_1,\ q_i\in\mathcal D_2,\ 1\le e_i\le e\Bigr\}.
--   $$
--   A polynomial $f\in F[x]$ is in its **border** if at most $k$ triples $(q_i,P_i,e_i)$ of this form, with $P_i,q_i\in F((\epsilon))[x]$ satisfying their constraints over $F((\epsilon))$, give $\sum_i q_iP_i^{e_i}=f+\epsilon S$ with $S\in F[[\epsilon]][x]$.
--
--   With $\mathcal D_1=\mathcal D_{\text{small-pd}}(\lambda)$, $\mathcal D_2=\mathcal D_{\text{small-pd}}(\Gamma)$ or with roABP classes this is the hypothesis of Theorem 6.1. With $q_i=a_i(\epsilon)$ constants and unrestricted exponents it is the presentation (69) of §9.2 used in Theorem 2.9.
--
--   **Formalization Note** $e\in\mathbb N\cup\{\infty\}$ (`ℕ∞`); $e=\infty$ means no restriction on the exponents. "$k$ summands" is read as "at most $k$" (every class used contains $0$).
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), §5.3, p.37, display (29); p.38 (D_small-pd(λ, Γ), D_roABP((w1, R1), (w2, R2))); §9.2, p.71, display (69)

import Mathlib
import Definitions.Def_BorderDiffEq_IsEpsApprox

namespace BorderDiffEq.Supplement

open BorderDiffEq

/-- **The border of the extended class, `f ∈ cl(Ext-Σ^{[k]} ∧^e D(c₁, c₂))`**
(Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits via
Differential Equations*, manuscript (STOC 2027 submission), §5.3, p.37, display (29):
`Ext-Σ^{[k]} ∧^e D(c₁, c₂) := {∑_{i=1}^k qᵢ(x) Pᵢ(x)^{eᵢ} : Pᵢ ∈ D(c₁), qᵢ ∈ D(c₂),
1 ≤ eᵢ ≤ e}`; classes `D_small-pd(λ, Γ)` and `D_roABP((w₁, R₁), (w₂, R₂))`, p.38; and §9.2, p.71,
display (69), where `qᵢ = aᵢ(ε)` are constants and the exponents are unrestricted): `f ∈ F[x]` is
in the border if there are at most `k` triples `(qᵢ, Pᵢ, eᵢ)` with `Pᵢ ∈ D₁`, `qᵢ ∈ D₂`
(polynomials over `F((ε))`), `1 ≤ eᵢ ≤ e`, and `∑ᵢ qᵢ Pᵢ^{eᵢ} = f + ε·S`, `S ∈ F[[ε]][x]`.

**Formalization Note.** The exponent bound `e` is in `ℕ∞`; `e = ⊤` is "no restriction on the
exponents", as in (69). The classes `D₁`, `D₂` are predicates on polynomials over `F((ε))`
(constraints read over `F((ε))`). "`k` summands" is read as "at most `k`"; for every class used
here `0 ∈ D₁ ∩ D₂`, so this is the same class. `IsEpsApprox` is the base mission's border
relation. -/
def InBorderExt (F : Type) [Field F] (n k : ℕ) (e : ℕ∞)
    (D₁ D₂ : MvPolynomial (Fin n) (LaurentSeries F) → Prop) (f : MvPolynomial (Fin n) F) : Prop :=
  ∃ (t : ℕ) (q P : Fin t → MvPolynomial (Fin n) (LaurentSeries F)) (ex : Fin t → ℕ),
    t ≤ k ∧ (∀ i, 1 ≤ ex i ∧ (ex i : ℕ∞) ≤ e) ∧ (∀ i, D₁ (P i)) ∧ (∀ i, D₂ (q i)) ∧
    IsEpsApprox (∑ i, q i * P i ^ ex i) f

end BorderDiffEq.Supplement


