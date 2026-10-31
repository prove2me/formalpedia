-- Prove2me | Definitions.Def_OnlineGND_DualFitting
-- name    : OnlineGND_DualFitting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:23:00.222519+00:00
-- url     : https://prove2.me/theorems/59cbcd62-7bde-44bd-9645-f05c99258cdf
-- title:
--   §4.1 — the dual solution $(y, z)$ of the proof of Theorem 6
-- statement:
--   Let $A$ be the final loads of the algorithm (20) with parameter $\rho$, and $\alpha=\max_e\alpha_e$. The proof of Theorem 6 (p.13) sets
--
--   1. $z_e=\frac1\rho A_e^{\alpha_e-1}$ for $e\in E\setminus E_1$, and $z_e=1$ for $e\in E_1$;
--   2. $$y_i=\min_{p\in\mathcal P_i}\Bigl(\sum_{e\in p\cap E_1}c_ew_{i,e}+\sum_{e\in p\setminus E_1}\Bigl(c_e\alpha_ew_{i,e}z_e+\frac{c_e\alpha_e}{e^\alpha}w_{i,e}^{\alpha_e}\Bigr)\Bigr).$$
--
--   This dual is feasible for (D″), and comparing the algorithm's cost with its objective proves Theorem 6.
--
--   **Formalization Note** The minimum is the infimum over the finite set $\mathcal P_i$, which equals the paper's minimum whenever $\mathcal P_i\ne\emptyset$; the oracle hypothesis of the theorems guarantees this.
-- source:
--   Nagarajan & Wang, Online Generalized Network Design Under (Dis)Economies of Scale, arXiv:2007.07721v1, §4.1, proof of Theorem 6, p.13

import Definitions.Def_OnlineGND_PowerAlg
import Definitions.Def_OnlineGND_Relaxation

namespace OnlineGND

/-! # The dual solution of the proof of Theorem 6 (Nagarajan & Wang, arXiv:2007.07721v1, §4.1, p.13)

`zₑ := (1/ρ) Aₑ^{αₑ−1}` for `e ∈ E ∖ E₁` (and `z = 1` on `E₁ ∪ E″`), and
`yᵢ := min_{p∈𝒫ᵢ} (Σ_{e∈p∩E₁} cₑ w_{i,e} + Σ_{e∈p∖E₁} (cₑ αₑ w_{i,e} zₑ + (cₑαₑ/e^α) w_{i,e}^{αₑ}))`,
where `A` are the algorithm's final loads. -/

variable {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ}

/-- The dual variable `zₑ` of the proof of Theorem 6 (arXiv:2007.07721v1, §4.1, p.13):
`zₑ := (1/ρ) · Aₑ^{αₑ−1}` for `e ∈ E ∖ E₁`, and `zₑ := 1` for `e ∈ E₁`. -/
noncomputable def zVar (α : E → ℝ) (ρ : ℝ) (A : E → ℝ) (e : E) : ℝ :=
  if α e = 1 then 1 else 1 / ρ * A e ^ (α e - 1)

/-- The dual variable `yᵢ` of the proof of Theorem 6 (arXiv:2007.07721v1, §4.1, p.13):
`yᵢ := min_{p∈𝒫ᵢ} (Σ_{e∈p∩E₁} cₑ w_{i,e} + Σ_{e∈p∖E₁} (cₑ αₑ w_{i,e} · zₑ + (cₑαₑ/e^α) w_{i,e}^{αₑ}))`.

**Formalization Note.** The minimum is the infimum over the finite subtype of `𝒫ᵢ`; it is the
paper's minimum whenever `𝒫ᵢ ≠ ∅`, which the oracle hypothesis guarantees. -/
noncomputable def dualY (c α : E → ℝ) (ρ : ℝ) (A : E → ℝ) (r : Request E) : ℝ :=
  ⨅ p : r.replies,
    (∑ e ∈ (p : Finset E).filter (fun e => α e = 1), c e * r.w e
      + ∑ e ∈ (p : Finset E).filter (fun e => α e ≠ 1),
          (c e * α e * r.w e * zVar α ρ A e + c e * α e / Real.exp (alphaMax α) * r.w e ^ α e))

end OnlineGND


