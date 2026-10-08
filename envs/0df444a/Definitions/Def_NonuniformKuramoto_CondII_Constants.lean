-- Prove2me | Definitions.Def_NonuniformKuramoto_CondII_Constants
-- name    : NonuniformKuramoto_CondII_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:46.613343+00:00
-- url     : https://prove2.me/theorems/92ea3c85-0986-44dd-a246-5e94e0612f37
-- title:
--   Constants of Theorem V.5: κ, α, ϕ_max, X̃, λ_critical (33), the Lyapunov function W (34), its derivative (35), Ω and λ_fe (19)
-- statement:
--   The quantities entering condition (33) and its proof, for parameters $D,\omega,P,\varphi$ of the non-uniform Kuramoto model (8).
--
--   1. $\kappa=\sum_{k=1}^nD_k$, $\max_{i\ne j}\{D_iD_j\}$, $\min_{i\ne j}\{D_iD_j\}$ and $\alpha=\sqrt{\min_{i\ne j}\{D_iD_j\}/\max_{i\ne j}\{D_iD_j\}}$; $\varphi_{\max}=\max_{i,j}\varphi_{ij}$; $D_{\max}=\max_iD_i$.
--   2. The lossless coupling weights $P_{ij}\cos(\varphi_{ij})$, and the lossy coupling vector $\big[\dots,\sum_{j=1}^n\frac{P_{ij}}{D_i}\sin(\varphi_{ij}),\dots\big]$ with $\tilde X=\sqrt n\,\big\|\big[\dots,\sum_j\frac{P_{ij}}{D_i}\sin(\varphi_{ij}),\dots\big]\big\|_2$.
--   3. The **critical value**
--   $$
--   \lambda_{\mathrm{critical}}=\frac{\|HD^{-1}\omega\|_2+\sqrt n\,\big\|\big[\sum_{j=1}^n\frac{P_{1j}}{D_1}\sin(\varphi_{1j}),\dots,\sum_{j=1}^n\frac{P_{nj}}{D_n}\sin(\varphi_{nj})\big]\big\|_2}{\cos(\varphi_{\max})(\kappa/n)\alpha/\max_{i\ne j}\{D_iD_j\}},\tag{33}
--   $$
--   where $\|HD^{-1}\omega\|_2=\|(\omega_2/D_2-\omega_1/D_1,\dots)\|_2$.
--   4. The state-dependent lossy vector $X_i(\theta)=\sum_{j=1}^n(P_{ij}/D_i)\sin(\varphi_{ij})\cos(\theta_i-\theta_j)$ of (31).
--   5. The Lyapunov function $W(H\theta)=\tfrac12(H\theta)^T\operatorname{diag}(D_iD_j)(H\theta)=\tfrac14\sum_i\sum_jD_iD_j|\theta_i-\theta_j|^2$ of (34), and its derivative along (8), $\dot W(H\theta)=(H\theta)^T\operatorname{diag}(D_iD_j)H\dot\theta$, with $\dot\theta$ the right-hand side of (8) divided by $D$; this is (35).
--   6. $\Omega=\sum_i\omega_i/\sum_iD_i$, $\cos(\angle(D\mathbf 1,\mathbf 1))=\sum_iD_i/(\sqrt n\,\|D\|_2)$, and the rate of (19), $\lambda_{\mathrm{fe}}(\gamma)=\lambda_2(L(P_{ij}))\cos(\gamma)\cos(\angle(D\mathbf 1,\mathbf 1))^2/D_{\max}$.
--
--   These are the explicit constants of Synchronization condition II; each is written exactly as printed.
--
--   **Formalization Note** Maxima and minima over $i\ne j$ are real suprema/infima over a finite index set, which is nonempty under the standing assumption $n\ge2$, so they are attained. Diagonal matrices indexed by pairs, $\operatorname{diag}(D_iD_j)$ and $\operatorname{diag}(P_{ij}\cos\varphi_{ij})$, are indexed by the pairs $i<j$. Equation (19) prints $\lambda_{\mathrm{fe}}$ with a leading minus sign; a rate of exponential convergence is positive, and the formula here drops that sign.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 23, (31), (33), κ and α; p. 24, (34), (35), Remark V.6; p. 25, X̃; p. 16, Ω and (19); p. 4, ∠(x, y)

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondII_Graph
import Definitions.Def_NonuniformKuramoto_CondII_Model
import Definitions.Def_NonuniformKuramoto_CondI_Constants

namespace NonuniformKuramoto.CondII

open Matrix

/-- `κ := ∑_{k=1}^n D_k` (p. 23). -/
def kappa {n : ℕ} (D : Fin n → ℝ) : ℝ := ∑ k, D k

/-- `max_{i≠j} {D_i D_j}` (p. 23); a maximum over a finite set, nonempty when `n ≥ 2`. -/
noncomputable def maxDD {n : ℕ} (D : Fin n → ℝ) : ℝ :=
  ⨆ p : {p : Fin n × Fin n // p.1 ≠ p.2}, D p.1.1 * D p.1.2

/-- `min_{i≠j} {D_i D_j}` (p. 23); a minimum over a finite set, nonempty when `n ≥ 2`. -/
noncomputable def minDD {n : ℕ} (D : Fin n → ℝ) : ℝ :=
  ⨅ p : {p : Fin n × Fin n // p.1 ≠ p.2}, D p.1.1 * D p.1.2

/-- `α := (min_{i≠j}{D_iD_j} / max_{i≠j}{D_iD_j})^{1/2}` (p. 23). -/
noncomputable def alpha {n : ℕ} (D : Fin n → ℝ) : ℝ :=
  Real.sqrt (minDD D / maxDD D)

/-- `ϕ_max := max_{i,j} ϕ_ij`, over all pairs (p. 4). -/
noncomputable def phiMax {n : ℕ} (ϕ : Fin n → Fin n → ℝ) : ℝ :=
  ⨆ p : Fin n × Fin n, ϕ p.1 p.2

/-- `D_max := max_i D_i`. -/
noncomputable def Dmax {n : ℕ} (D : Fin n → ℝ) : ℝ := ⨆ i, D i

/-- The lossless coupling weights `P_ij cos(ϕ_ij)` (p. 23). -/
noncomputable def lossless {n : ℕ} (P ϕ : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => P i j * Real.cos (ϕ i j)

/-- The vector of lossy coupling strengths in (33): its `i`-th entry is
`∑_{j=1}^n (P_ij / D_i) sin(ϕ_ij)`. -/
noncomputable def lossyVec {n : ℕ} (D : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j, P i j / D i * Real.sin (ϕ i j)

/-- `X̃ := √n ‖[…, ∑_j (P_ij/D_i) sin(ϕ_ij), …]‖₂` (p. 25). -/
noncomputable def Xtilde {n : ℕ} (D : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) : ℝ :=
  Real.sqrt n * euclNorm (lossyVec D P ϕ)

/-- The critical value of (33):
`λ_critical := (‖HD⁻¹ω‖₂ + √n ‖[…, ∑_j (P_ij/D_i) sin(ϕ_ij), …]‖₂) /
(cos(ϕ_max) (κ/n) α / max_{i≠j}{D_iD_j})`. -/
noncomputable def lambdaCritical {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) : ℝ :=
  (normH (fun i => ω i / D i) + Real.sqrt n * euclNorm (lossyVec D P ϕ)) /
    (Real.cos (phiMax ϕ) * (kappa D / n) * alpha D / maxDD D)

/-- The lossy coupling vector `X` of (31): `X_i = ∑_{j=1}^n (P_ij/D_i) sin(ϕ_ij) cos(θ_i − θ_j)`
(p. 23). -/
noncomputable def lossyX {n : ℕ} (D : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) (θ : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ∑ j, P i j / D i * Real.sin (ϕ i j) * Real.cos (θ i - θ j)

/-- The weights `D_i D_j` on the edges `(i, j)`, `i < j`, of the complete graph, i.e. the
diagonal of `diag(D_iD_j)` (p. 24). -/
def pairDD {n : ℕ} (D : Fin n → ℝ) : Pairs n → ℝ := fun p => D p.1.1 * D p.1.2

/-- The lossless weights `P_ij cos(ϕ_ij)` on the edges `(i, j)`, `i < j`, of the complete
graph, i.e. the diagonal of `diag(P_ij cos(ϕ_ij))` (p. 23). -/
noncomputable def pairLossless {n : ℕ} (P ϕ : Fin n → Fin n → ℝ) : Pairs n → ℝ :=
  fun p => P p.1.1 p.1.2 * Real.cos (ϕ p.1.1 p.1.2)

/-- The Lyapunov function (34): `W(Hθ) = ½ (Hθ)ᵀ diag(D_iD_j) (Hθ)
= ¼ ∑_i ∑_j D_iD_j |θ_i − θ_j|²`. -/
noncomputable def W {n : ℕ} (D : Fin n → ℝ) (θ : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ((incH n *ᵥ θ) ⬝ᵥ (Matrix.diagonal (pairDD D) *ᵥ (incH n *ᵥ θ)))

/-- The derivative of `W(Hθ)` along the trajectories of (8) at the configuration `θ` (35):
`Ẇ(Hθ) = (Hθ)ᵀ diag(D_iD_j) H θ̇`, with `θ̇` the vector NonuniformKuramoto.CondI.field of (8) at `θ`. -/
noncomputable def Wdot {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) (θ : Fin n → ℝ) :
    ℝ :=
  (incH n *ᵥ θ) ⬝ᵥ (Matrix.diagonal (pairDD D) *ᵥ (incH n *ᵥ NonuniformKuramoto.CondI.field D ω P ϕ θ))

/-- The frequency-synchronization rate of (19), taken positive:
`λ_fe(γ) = λ₂(L(P_ij)) cos(γ) cos(∠(D𝟙, 𝟙))² / D_max` (p. 16; the page prints a minus sign
in front, a slip: a rate of exponential convergence is positive). -/
noncomputable def lambdaFe {n : ℕ} (D : Fin n → ℝ) (P : Fin n → Fin n → ℝ) (γ : ℝ) : ℝ :=
  lambda2 P * Real.cos γ * NonuniformKuramoto.CondI.cosAngleD D ^ 2 / Dmax D

end NonuniformKuramoto.CondII


