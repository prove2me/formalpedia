-- Prove2me | Definitions.Def_Holant3Dich_CLXForms
-- name    : Holant3Dich_CLXForms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:46:18.957209+00:00
-- url     : https://prove2.me/theorems/7ad2ad08-a7ef-4c1f-999b-3d67f6ed3076
-- title:
--   The three tractable forms of a ternary signature (Theorem 2.6, [CLX13])
-- statement:
--   A ternary signature $F$ on $\{\mathsf B,\mathsf G,\mathsf R\}$ is in one of the **forms of Theorem 2.6** if
--
--   1. $F=\alpha^{\otimes3}+\beta^{\otimes3}+\gamma^{\otimes3}$ for pairwise orthogonal $\alpha,\beta,\gamma\in\mathbb C^3$; or
--   2. $F=\alpha^{\otimes3}+\beta_1^{\otimes3}+\beta_2^{\otimes3}$ with $\langle\alpha,\beta_1\rangle=\langle\alpha,\beta_2\rangle=0$ and $\langle\beta_1,\beta_1\rangle=\langle\beta_2,\beta_2\rangle=0$; or
--   3. $F=F_\beta+\mathrm{Sym}(\beta,\beta,\gamma)$ for vectors $\beta\neq0$, $\gamma$ with $\langle\beta,\beta\rangle=0$ and a ternary signature $F_\beta$ with $\langle F_\beta,\beta\rangle=0$.
--
--   These are the tractable forms of the single-signature dichotomy of Cai, Lu and Xia [CLX13].
--
--   **Formalization Note** $\langle F_\beta,\beta\rangle$ connects $\beta$ to the last input of $F_\beta$; for symmetric $F$, $F_\beta=F-\mathrm{Sym}(\beta,\beta,\gamma)$ is symmetric, so the input does not matter.
-- source:
--   Cai, Ihm, Group Action and Spin Representation Lead to a Holant* Complexity Dichotomy on Domain Size 3, STOC 2027 submission, arXiv:2610.04750 (held manuscript sha256 b608db44…), Theorem 2.6 p.15

import Mathlib
import Definitions.Def_Holant3Dich_Sig
import Definitions.Def_Holant3Dich_IsOrth3

set_option autoImplicit false

namespace Holant3Dich

/-- The **three tractable forms of Theorem 2.6** ([CLX13]) for a ternary signature `F`. Cai–Ihm,
*Group Action and Spin Representation Lead to a Holant\* Complexity Dichotomy on Domain Size 3*,
STOC 2027 submission, arXiv:2610.04750 (held manuscript sha256 b608db44…), Theorem 2.6, p.15:
"1. There exists three vectors α, β, γ ∈ C^3 such that ⟨α, β⟩ = 0, ⟨α, γ⟩ = 0, and ⟨β, γ⟩ = 0, and
F = α^{⊗3} + β^{⊗3} + γ^{⊗3}.
2. There exists three vectors α, β1, β2 ∈ C^3 such that ⟨α, β1⟩ = 0, ⟨α, β2⟩ = 0, ⟨β1, β1⟩ = 0,
⟨β2, β2⟩ = 0 and F = α^{⊗3} + β1^{⊗3} + β2^{⊗3}.
3. There exists two vectors β, γ ∈ C^3 and a signature Fβ of arity 3, such that β ≠ 0,
⟨β, β⟩ = 0, ⟨Fβ, β⟩ = 0 and F = Fβ + Sym(β, β, γ)."

**Formalization Note.** `Sym(β, β, γ)` is `symUV β γ 3`; `⟨Fβ, β⟩ = 0` is the vanishing of the
contraction of `Fβ` with `β` on its last input. For a symmetric `F`, `Fβ = F − Sym(β, β, γ)` is
symmetric, so the choice of input does not matter. Applied to ternary `F`, so `F.1 = 3`. -/
def CLXForms (F : Sig 3) : Prop :=
  (∃ α β γ : Fin 3 → ℂ, dot α β = 0 ∧ dot α γ = 0 ∧ dot β γ = 0 ∧
      F.2 = tpow α F.1 + tpow β F.1 + tpow γ F.1) ∨
  (∃ α β₁ β₂ : Fin 3 → ℂ, dot α β₁ = 0 ∧ dot α β₂ = 0 ∧ dot β₁ β₁ = 0 ∧ dot β₂ β₂ = 0 ∧
      F.2 = tpow α F.1 + tpow β₁ F.1 + tpow β₂ F.1) ∨
  (∃ (β γ : Fin 3 → ℂ) (Fβ : (Fin F.1 → Fin 3) → ℂ), β ≠ 0 ∧ dot β β = 0 ∧
      contractT Fβ β = 0 ∧ F.2 = Fβ + symUV β γ F.1)

end Holant3Dich


