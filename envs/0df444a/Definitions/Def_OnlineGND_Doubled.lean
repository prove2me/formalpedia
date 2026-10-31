-- Prove2me | Definitions.Def_OnlineGND_Doubled
-- name    : OnlineGND_Doubled
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:45.228217+00:00
-- url     : https://prove2.me/theorems/5e6564ba-a666-49db-a75d-35f063248969
-- title:
--   §5 — the power-cost instance 𝒥, the lifted oracle and the algorithm of Theorem 1
-- statement:
--   Given a GND instance $\mathcal I$ with (D)oS costs, §5 (p.14) builds a power-cost instance $\mathcal J$.
--
--   1. **Resources.** Each $e\in E$ has two copies $e_1$ and $e_a$.
--   2. **Costs.** $c_{e_1}=\xi_eq_e^{\alpha_e-1}$, $\alpha_{e_1}=1$; $c_{e_a}=\xi_e$, $\alpha_{e_a}=\alpha_e$; so $g_{e_1}(x)+g_{e_a}(x)=h_e(x)$.
--   3. **Replies and weights.** Each reply $p\in\mathcal P_i$ corresponds to the reply of $\mathcal J$ containing both copies of every $e\in p$; $w_{i,e_1}=w_{i,e_a}=w_{i,e}$.
--   4. **Oracle.** Given costs $d$ on $\mathcal J$, call the oracle of $\mathcal I$ under $d'_e=d_{e_1}+d_{e_a}$ and lift its reply (the construction of p.15); this keeps the approximation factor $\tau$.
--   5. **The algorithm of Theorem 1.** Run the algorithm of Theorem 6 on $\mathcal J$ with $\rho=(e\tau\alpha)^{\alpha-1}$. Since both copies of $e$ carry the load of $e$, request $i$ receives $O(i,d')$ with
--   $$d'_e=\rho\,\xi_eq_e^{\alpha_e-1}w_{i,e}+\begin{cases}\alpha_e\xi_e\ell_e^{\alpha_e-1}w_{i,e}+\frac{\rho}{e^\alpha}\xi_e\alpha_ew_{i,e}^{\alpha_e} & \alpha_e>1,\\ \rho\,\xi_ew_{i,e} & \alpha_e=1.\end{cases}$$
--
--   **Formalization Note** The resources of $\mathcal J$ are $E\times\{\text{false},\text{true}\}$, with false the linear copy $e_1$ and true the power copy $e_a$. The maximum exponent of $\mathcal J$ is $\max(1,\max_e\alpha_e)$, the $\alpha$ of $\mathcal I$.
-- source:
--   Nagarajan & Wang, Online Generalized Network Design Under (Dis)Economies of Scale, arXiv:2007.07721v1, §5, p.14 (instance 𝒥, ρ = (eτα)^{α−1}); p.15 (lifting the oracle)

import Definitions.Def_OnlineGND_DoS
import Definitions.Def_OnlineGND_PowerAlg

namespace OnlineGND

/-! # The power-cost instance 𝒥 and the algorithm of Theorem 1 (Nagarajan & Wang, arXiv:2007.07721v1, §5, p.14; the oracle lift, p.15)

Each resource `e ∈ E` gets two copies `e₁ = (e, false)` and `e_a = (e, true)`, with
`c_{e₁} := ξₑ qₑ^{αₑ−1}`, `α_{e₁} := 1`, `c_{e_a} := ξₑ`, `α_{e_a} := αₑ`. Every reply `p` becomes the
reply `p × {false, true}` containing both copies of each `e ∈ p`, with the same weights. The oracle
for 𝒥 calls the oracle for `𝓘` under `d′ₑ := d_{e₁} + d_{e_a}` and lifts its reply.

**Formalization Note.** The resources of 𝒥 are `E × Bool`. The algorithm of Theorem 1 runs Theorem 6's
algorithm (20) on 𝒥 with `ρ = (eτα)^{α−1}`; since 𝒥's loads on `e₁` and `e_a` both equal the load on
`e` in `𝓘`, the run is computed directly on `𝓘`: the reply to request `i` is
`O(i, d′)` with `d′ₑ = ψ̄_{e₁} + ψ̄_{e_a}`, i.e.
`d′ₑ = ρ ξₑ qₑ^{αₑ−1} w_{i,e} + [αₑ > 1](αₑ ξₑ ℓₑ^{αₑ−1} w_{i,e} + (ρ/e^α) ξₑ αₑ w_{i,e}^{αₑ}) + [αₑ = 1] ρ ξₑ w_{i,e}`. -/

variable {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ}

/-- The lift of a reply `p ⊆ E` to 𝒥: both copies `e₁, e_a` of each `e ∈ p`
(arXiv:2007.07721v1, §5, p.14). -/
def liftSet (p : Finset E) : Finset (E × Bool) :=
  p ×ˢ Finset.univ

/-- The lift of a request to 𝒥 (arXiv:2007.07721v1, §5, p.14): replies `{lift p : p ∈ 𝒫ᵢ}` and
weights `w_{i,e₁} = w_{i,e_a} = w_{i,e}`. -/
def liftReq (r : Request E) : Request (E × Bool) where
  replies := r.replies.image liftSet
  w := fun x => r.w x.1

/-- The scalars of 𝒥 (arXiv:2007.07721v1, §5, p.14): `c_{e₁} := ξₑ qₑ^{αₑ−1}`, `c_{e_a} := ξₑ`. -/
noncomputable def cJ (σ ξ α : E → ℝ) : E × Bool → ℝ
  | (e, false) => ξ e * qPar σ ξ α e ^ (α e - 1)
  | (e, true) => ξ e

/-- The exponents of 𝒥 (arXiv:2007.07721v1, §5, p.14): `α_{e₁} := 1`, `α_{e_a} := αₑ`. -/
def alphaJ (α : E → ℝ) : E × Bool → ℝ
  | (_, false) => 1
  | (e, true) => α e

/-- The parameter `ρ = (eτα)^{α−1}` fixed in the proof of Theorem 6 (arXiv:2007.07721v1, p.14),
for a power-cost instance with exponents `α`. -/
noncomputable def rhoStar {R : Type*} [Fintype R] (τ : ℝ) (α : R → ℝ) : ℝ :=
  (Real.exp 1 * τ * alphaMax α) ^ (alphaMax α - 1)

/-- The online algorithm of Theorem 1 (arXiv:2007.07721v1, §5, p.14): Theorem 6's algorithm with
`ρ = (eτα)^{α−1}` run on 𝒥, with 𝒥's oracle obtained from `O` by the lift (p.15). The reply to
request `i` in `𝓘` is `O(i, d′)` with `d′ₑ := ψ̄_{e₁} + ψ̄_{e_a}`, the costs (20) of 𝒥 at the current
loads (the load of both copies of `e` is the current load `ℓₑ` of `e`). -/
noncomputable def dosAlg (σ ξ α : E → ℝ) (τ : ℝ) (O : Request E → (E → ℝ) → Finset E)
    (reqs : Fin N → Request E) : Fin N → Finset E :=
  onlineReplies (fun ℓ r => O r (fun e =>
      psiBar (cJ σ ξ α) (alphaJ α) (rhoStar τ (alphaJ α)) (fun x => ℓ x.1) (liftReq r) (e, false)
      + psiBar (cJ σ ξ α) (alphaJ α) (rhoStar τ (alphaJ α)) (fun x => ℓ x.1) (liftReq r) (e, true)))
    reqs

end OnlineGND


