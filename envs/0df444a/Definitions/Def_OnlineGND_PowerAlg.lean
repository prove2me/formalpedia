-- Prove2me | Definitions.Def_OnlineGND_PowerAlg
-- name    : OnlineGND_PowerAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:48.946405+00:00
-- url     : https://prove2.me/theorems/c39b96c3-6302-4c48-94c5-056034f4eb87
-- title:
--   (20) — the online algorithm of Theorem 6 for weighted power costs, and the costs $L$, $H$
-- statement:
--   For GND with weighted power costs $g_e(x)=c_e x^{\alpha_e}$ ($c_e\ge0$, $\alpha_e\ge1$), let $E_1=\{e:\alpha_e=1\}$ and $\alpha=\max_e\alpha_e$.
--
--   1. **The cost of loads** $\ell$ is $\sum_e c_e\ell_e^{\alpha_e}$.
--   2. **The costs (20), p.12.** With current loads $\ell$ and arriving request $i$,
--   $$\bar\psi_e=\begin{cases}\alpha_e c_e\,\ell_e^{\alpha_e-1}w_{i,e}+\dfrac{\rho}{e^{\alpha}}\,c_e\alpha_e w_{i,e}^{\alpha_e} & e\in E\setminus E_1,\\[4pt] \rho\,c_e w_{i,e} & e\in E_1.\end{cases}$$
--   3. **The algorithm.** Upon arrival of request $i$, select the reply returned by the min-cost oracle under the costs $\bar\psi$, evaluated at the loads of the earlier replies.
--   4. **The costs of the algorithm.** With final loads $A$, $L=\sum_{e\in E_1}c_eA_e$ and $H=\sum_{e\in E\setminus E_1}c_eA_e^{\alpha_e}$.
--
--   This is the algorithm of Theorem 6, which §5 runs on the doubled instance.
--
--   **Formalization Note** $e^\alpha$ is `Real.exp α` with the global $\alpha=\max(1,\max_e\alpha_e)$. The split on $E_1$ is kept, so $\ell_e^{\alpha_e-1}$ is never evaluated with $\alpha_e=1$. The algorithm makes one oracle call and $|E|$ closed-form cost evaluations per request.
-- source:
--   Nagarajan & Wang, Online Generalized Network Design Under (Dis)Economies of Scale, arXiv:2007.07721v1, §4.1, (20) p.12; L, H p.12; power costs §2 end p.6, §3 p.7

import Definitions.Def_OnlineGND_Model

namespace OnlineGND

/-! # Power-cost GND and the online algorithm of Theorem 6 (Nagarajan & Wang, arXiv:2007.07721v1, §2 p.6, §3 p.7, §4.1 (20) p.12)

Each resource has a weighted power cost `gₑ(x) = cₑ · x^{αₑ}` (`cₑ ≥ 0`, `αₑ ≥ 1`); `E₁ = {e : αₑ = 1}`.
On arrival of request `i` the algorithm picks the oracle's reply under the costs `ψ̄ₑ` of (20).

**Formalization Note.** `e^α` is `Real.exp α` with `α = alphaMax α` (the global maximum exponent),
never the per-resource `αₑ`. `x^{y}` is `Real.rpow`; (20) keeps the paper's split on `E₁`, so
`ℓₑ^{αₑ−1}` is never evaluated with `αₑ = 1`. -/

variable {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ}

/-- The cost of loads `ℓ` under weighted power functions (arXiv:2007.07721v1, §2 p.6, §3 p.7):
`Σ_{e∈E} cₑ · ℓₑ^{αₑ}`. Applied to the loads of a reply profile it is that profile's objective. -/
noncomputable def powerCost (c α : E → ℝ) (ℓ : E → ℝ) : ℝ :=
  ∑ e, c e * ℓ e ^ α e

/-- The costs (20) (arXiv:2007.07721v1, §4.1, p.12), for current loads `ℓ` and arriving request `r`:
`ψ̄ₑ := αₑ cₑ ℓₑ^{αₑ−1} w_{i,e} + (ρ/e^α) cₑ αₑ w_{i,e}^{αₑ}` if `e ∈ E ∖ E₁`, and
`ψ̄ₑ := ρ cₑ w_{i,e}` if `e ∈ E₁ = {e : αₑ = 1}`. -/
noncomputable def psiBar (c α : E → ℝ) (ρ : ℝ) (ℓ : E → ℝ) (r : Request E) (e : E) : ℝ :=
  if α e = 1 then ρ * c e * r.w e
  else α e * c e * ℓ e ^ (α e - 1) * r.w e
    + ρ / Real.exp (alphaMax α) * c e * α e * r.w e ^ α e

/-- The online algorithm of Theorem 6 (arXiv:2007.07721v1, §4.1, p.12) with parameter `ρ`: upon
arrival of request `i`, select the reply `pᵢ` returned by the oracle `O` under the costs `ψ̄` of (20),
evaluated at the current loads `ℓₑ = Σ_{j<i : e∈pⱼ} w_{j,e}`.

**Formalization Note.** One oracle call and `|E|` closed-form cost evaluations per request; this is
how the paper's "polynomial time" (relative to the oracle) is carried. -/
noncomputable def powerAlg (c α : E → ℝ) (ρ : ℝ) (O : Request E → (E → ℝ) → Finset E)
    (reqs : Fin N → Request E) : Fin N → Finset E :=
  onlineReplies (fun ℓ r => O r (psiBar c α ρ ℓ r)) reqs

/-- `L := Σ_{e∈E₁} cₑ Aₑ`, the cost on resources with `αₑ = 1` (arXiv:2007.07721v1, §4.1, p.12). -/
noncomputable def costL (c α : E → ℝ) (A : E → ℝ) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => α e = 1), c e * A e

/-- `H := Σ_{e∈E∖E₁} cₑ Aₑ^{αₑ}`, the cost on resources with `αₑ ≠ 1` (arXiv:2007.07721v1, §4.1,
p.12). -/
noncomputable def costH (c α : E → ℝ) (A : E → ℝ) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => α e ≠ 1), c e * A e ^ α e

end OnlineGND


