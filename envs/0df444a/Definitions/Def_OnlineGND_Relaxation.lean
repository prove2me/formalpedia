-- Prove2me | Definitions.Def_OnlineGND_Relaxation
-- name    : OnlineGND_Relaxation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:01.43386+00:00
-- url     : https://prove2.me/theorems/3be99535-2d1c-47ad-b114-905c9955f443
-- title:
--   (P), (D), (12), (21) — the convex relaxation, its dual and the relaxations with linear terms
-- statement:
--   For GND with weighted power costs $c_e x^{\alpha_e}$:
--
--   1. **Fractional load.** For primal variables $x_{i,p}$, $p\in\mathcal P_i$: $\ell_e=\sum_i w_{i,e}\sum_{p\in\mathcal P_i:e\in p}x_{i,p}$.
--   2. **(P), p.7.** Minimize $\sum_e c_e\ell_e^{\alpha_e}$ subject to (4) $\sum_{p\in\mathcal P_i}x_{i,p}\ge1$ for all $i$, and $x\ge0$.
--   3. **(D), p.7.** Maximize $\sum_i y_i-\sum_{e\in E\setminus E_1}\frac{c_e\alpha_e}{\beta_e}z_e^{\beta_e}$ subject to (5) $\sum_{e\in p}w_{i,e}c_e\alpha_e z_e\ge y_i$ for all $p\in\mathcal P_i$ and all $i$, (6) $z_e\le1$ for $e\in E_1$, and $y,z\ge0$. Here $\beta_e=\alpha_e/(\alpha_e-1)$ is the conjugate exponent.
--   4. **(12), p.10 and (21), p.12.** For a set $S\subseteq E$, the objective
--   $$\sum_{e\in E}c_e\ell_e^{\alpha_e}+\sum_{e\in S}\frac{c_e\alpha_e}{e^\alpha}\sum_i w_{i,e}^{\alpha_e}\sum_{p\in\mathcal P_i:e\in p}x_{i,p};$$
--   $S=E$ is (12) and $S=E\setminus E_1$ is (21).
--
--   These are the programs of the dual-fitting analysis (Lemmas 2 and 3, Theorem 6).
--
--   **Formalization Note** Primal variables are a function of the request index and a reply; only their values at $p\in\mathcal P_i$ are read. $\beta_e$ is only read for $\alpha_e\ne1$. $e^\alpha$ uses the global $\alpha=\max(1,\max_e\alpha_e)$.
-- source:
--   Nagarajan & Wang, Online Generalized Network Design Under (Dis)Economies of Scale, arXiv:2007.07721v1, §3, (P), (4), (D), (5), (6), p.7; (12) p.10; (21) p.12

import Definitions.Def_OnlineGND_Model

namespace OnlineGND

/-! # The convex relaxation (P), its dual (D), and the objectives (12)/(21) (Nagarajan & Wang, arXiv:2007.07721v1, §3 p.7, §4 (12) p.10, §4.1 (21) p.12)

Primal variables `x_{i,p} ≥ 0` for `p ∈ 𝒫ᵢ`, the covering constraints (4), the fractional loads,
the dual variables `(y, z)` with constraints (5), (6), and the conjugate exponents `βₑ`.

**Formalization Note.** `x : Fin N → Finset E → ℝ`; only its values at `p ∈ 𝒫ᵢ` are read.
`βₑ := αₑ/(αₑ − 1)` is only read for `αₑ ≠ 1`. -/

variable {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ}

/-- The fractional load `ℓₑ := Σᵢ w_{i,e} Σ_{p∈𝒫ᵢ : e∈p} x_{i,p}` (arXiv:2007.07721v1, §3, objective
of (P) and proof of Lemma 2, p.7). -/
noncomputable def fracLoad (reqs : Fin N → Request E) (x : Fin N → Finset E → ℝ) (e : E) : ℝ :=
  ∑ i, (reqs i).w e * ∑ p ∈ (reqs i).replies.filter (fun p => e ∈ p), x i p

/-- Feasibility in (P) (arXiv:2007.07721v1, §3, p.7): `x ≥ 0` and the covering constraints (4)
`Σ_{p∈𝒫ᵢ} x_{i,p} ≥ 1` for all `i`. -/
def IsPrimalFeasible (reqs : Fin N → Request E) (x : Fin N → Finset E → ℝ) : Prop :=
  (∀ i, ∀ p ∈ (reqs i).replies, 0 ≤ x i p) ∧ ∀ i, 1 ≤ ∑ p ∈ (reqs i).replies, x i p

/-- The objective of (P) (arXiv:2007.07721v1, §3, p.7):
`Σ_{e∈E} cₑ (Σᵢ w_{i,e} Σ_{p∈𝒫ᵢ:e∈p} x_{i,p})^{αₑ}`. -/
noncomputable def primalObj (c α : E → ℝ) (reqs : Fin N → Request E) (x : Fin N → Finset E → ℝ) :
    ℝ :=
  ∑ e, c e * fracLoad reqs x e ^ α e

/-- The conjugate exponent `βₑ` with `1/αₑ + 1/βₑ = 1`, i.e. `βₑ = αₑ/(αₑ − 1)`, for `e ∈ E ∖ E₁`
(arXiv:2007.07721v1, §3, p.7). -/
noncomputable def conjExp (α : E → ℝ) (e : E) : ℝ :=
  α e / (α e - 1)

/-- Feasibility in (D) (arXiv:2007.07721v1, §3, p.7): constraints (5)
`Σ_{e∈p} w_{i,e} cₑ αₑ zₑ ≥ yᵢ` for all `p ∈ 𝒫ᵢ` and all `i`, (6) `zₑ ≤ 1` for `e ∈ E₁`, and
`y, z ≥ 0`. -/
def IsDualFeasible (c α : E → ℝ) (reqs : Fin N → Request E) (y : Fin N → ℝ) (z : E → ℝ) : Prop :=
  (∀ i, ∀ p ∈ (reqs i).replies, y i ≤ ∑ e ∈ p, (reqs i).w e * c e * α e * z e) ∧
    (∀ e, α e = 1 → z e ≤ 1) ∧ (∀ i, 0 ≤ y i) ∧ ∀ e, 0 ≤ z e

/-- The objective of (D) (arXiv:2007.07721v1, §3, p.7):
`Σᵢ yᵢ − Σ_{e∈E∖E₁} (cₑαₑ/βₑ) · zₑ^{βₑ}`. -/
noncomputable def dualObj (c α : E → ℝ) (y : Fin N → ℝ) (z : E → ℝ) : ℝ :=
  ∑ i, y i - ∑ e ∈ Finset.univ.filter (fun e => α e ≠ 1),
    c e * α e / conjExp α e * z e ^ conjExp α e

/-- The relaxation objective with linear terms on a set `S ⊆ E` (arXiv:2007.07721v1, (12) p.10 for
`S = E`, (21) p.12 for `S = E ∖ E₁`):
`Σ_{e∈E} cₑ (Σᵢ w_{i,e} Σ_{p:e∈p} x_{i,p})^{αₑ} + Σ_{e∈S} (cₑαₑ/e^α) Σᵢ w_{i,e}^{αₑ} Σ_{p:e∈p} x_{i,p}`,
with `α = alphaMax α`. -/
noncomputable def relaxObj (c α : E → ℝ) (S : Finset E) (reqs : Fin N → Request E)
    (x : Fin N → Finset E → ℝ) : ℝ :=
  primalObj c α reqs x + ∑ e ∈ S, c e * α e / Real.exp (alphaMax α) *
    ∑ i, (reqs i).w e ^ α e * ∑ p ∈ (reqs i).replies.filter (fun p => e ∈ p), x i p

end OnlineGND


