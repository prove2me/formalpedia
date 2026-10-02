-- Prove2me | Definitions.Def_LeblSCV_Dolbeault_dbar
-- name    : LeblSCV_Dolbeault_dbar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T19:50:21.31247+00:00
-- url     : https://prove2.me/theorems/66cfc8f3-d705-42d7-b559-bd77c26bf56e
-- title:
--   Definition 4.4.1 — the operator ∂̄ on differential forms
-- statement:
--   Let $U \subset \mathbb{C}^n$ be open. For strictly increasing tuples $\alpha = (\alpha_1 < \dots < \alpha_p)$ and $\beta = (\beta_1 < \dots < \beta_q)$ in $\{1,\dots,n\}$ write $dz_\alpha = dz_{\alpha_1}\wedge\cdots\wedge dz_{\alpha_p}$ and $d\bar z_\beta = d\bar z_{\beta_1}\wedge\cdots\wedge d\bar z_{\beta_q}$. A differential form is a sum $\eta = \sum_{\alpha,\beta} \eta_{\alpha\beta}\, dz_\alpha \wedge d\bar z_\beta$ with coefficient functions $\eta_{\alpha\beta}$, and
--   $$\bar\partial \eta = \sum_{\alpha,\beta}\sum_{k=1}^n \frac{\partial \eta_{\alpha\beta}}{\partial \bar z_k}\, d\bar z_k \wedge dz_\alpha \wedge d\bar z_\beta .$$
--   Rewritten in the basis $dz_\alpha\wedge d\bar z_\gamma$ with $\gamma$ increasing, the coefficient of $dz_\alpha \wedge d\bar z_\gamma$ in $\bar\partial\eta$ is
--   $$(\bar\partial\eta)_{\alpha\gamma} = \sum_{k \in \gamma} (-1)^{|\alpha| + \#\{j\in\gamma\,:\,j<k\}}\, \frac{\partial \eta_{\alpha,\gamma\setminus\{k\}}}{\partial \bar z_k},$$
--   since moving $d\bar z_k$ past the $|\alpha|$ factors $dz_{\alpha_i}$ costs $(-1)^{|\alpha|}$, sorting it into $d\bar z_{\gamma\setminus\{k\}}$ costs $(-1)^{\#\{j \in \gamma : j < k\}}$, and $d\bar z_k\wedge d\bar z_\beta = 0$ when $k\in\beta$. $\bar\partial$ maps $(p,q)$-forms to $(p,q+1)$-forms.
--
--   **Formalization Note.** A form is its coefficient family `FormCoeffs n := Finset (Fin n) → Finset (Fin n) → (Fin n → ℂ) → ℂ`: an increasing tuple is the finite set of its entries (0-based), and `η A B z` is the coefficient of $dz_A \wedge d\bar z_B$ at $z$. `dbar` is the displayed formula. A sorry-free check shows that the two signs with which each mixed second derivative $\partial^2\eta_{\alpha,\gamma\setminus\{k,l\}}/\partial\bar z_k\partial\bar z_l$ enters $\bar\partial\bar\partial\eta$ are opposite, which is the sign content of $\bar\partial^2 = 0$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 138, Definition 4.4.1

import Mathlib
import Definitions.Def_LeblSCV_Shared_wirtingerBar

namespace LeblSCV.Dolbeault

/-- Coefficients of a differential form on `ℂⁿ` in the basis `dz_α ∧ dz̄_β` (Lebl, p. 138,
Definition 4.4.1). A strictly increasing tuple `1 ≤ α_1 < ⋯ < α_p ≤ n` is encoded by the finite set
`A = {α_1, …, α_p} ⊆ Fin n` (0-based), and `η A B z` is the coefficient `η_{αβ}(z)` of
`dz_α ∧ dz̄_β = dz_{α_1} ∧ ⋯ ∧ dz_{α_p} ∧ dz̄_{β_1} ∧ ⋯ ∧ dz̄_{β_q}`, both tuples in increasing order.
The bidegree is imposed separately (`IsSmoothForm`). -/
abbrev FormCoeffs (n : ℕ) : Type := Finset (Fin n) → Finset (Fin n) → (Fin n → ℂ) → ℂ

/-- The operator `∂̄` of Definition 4.4.1 (Lebl, p. 138),
`∂̄η = ∑_{α,β} ∑_{k=1}^n ∂η_{αβ}/∂z̄_k dz̄_k ∧ dz_α ∧ dz̄_β`,
written in the basis `dz_A ∧ dz̄_C` with `A`, `C` increasing. Moving `dz̄_k` past the `|A|` factors
`dz_α` gives the sign `(-1)^{|A|}`; inserting it into `dz̄_β` (`β = C ∖ {k}`, and the term vanishes when
`k ∈ β`) gives `(-1)^{#{j ∈ C : j < k}}`. Hence the coefficient of `dz_A ∧ dz̄_C` in `∂̄η` is
`∑_{k ∈ C} (-1)^{|A| + #{j ∈ C : j < k}} ∂η_{A, C∖{k}}/∂z̄_k`. -/
noncomputable def dbar {n : ℕ} (η : FormCoeffs n) : FormCoeffs n :=
  fun A C z =>
    ∑ k ∈ C, (-1 : ℂ) ^ (A.card + (C.filter (fun j => j < k)).card) *
      LeblSCV.Shared.wirtingerBar k (η A (C.erase k)) z

end LeblSCV.Dolbeault


