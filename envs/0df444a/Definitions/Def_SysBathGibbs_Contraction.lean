-- Prove2me | Definitions.Def_SysBathGibbs_Contraction
-- name    : SysBathGibbs_Contraction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:26.366058+00:00
-- url     : https://prove2.me/theorems/d6b39686-0666-4bb1-bbc3-fa2296168128
-- title:
--   Dirichlet form $\mathcal E_{\mathrm{KMS}}$, $\Theta_s$, $\mathcal D_\mu$, $\mathcal E_\mu$ and $\mathcal Q_{\mathrm{Lamb}}$
-- statement:
--   The Dirichlet form of $\mathcal L_{\mathrm{KMS}}$ is
--   $$
--   \mathcal E_{\mathrm{KMS}}(O)=-\big\langle O-\operatorname{Tr}(\rho_\beta O)\mathbf 1,\ \mathcal L_{\mathrm{KMS}}^\dagger(O-\operatorname{Tr}(\rho_\beta O)\mathbf 1)\big\rangle_{\rho_\beta}.
--   $$
--   With $T$ drawn from $\mu_{T_0}$, (8.5)–(8.6) define $\Theta_s=\mathbb E_T[\mathcal U(T)e^{s\mathcal L}\mathcal U(T)]$, $M_\mu=\Theta_0=\mathbb E_T\,\mathcal U(2T)$,
--   $$
--   \mathcal D_\mu(X)=\|\Gamma^{-1}(X)\|^2_{\rho_\beta}-\|\Gamma^{-1}(M_\mu X)\|^2_{\rho_\beta},\qquad \mathcal E_\mu(X)=\mathbb E_T\,\mathcal E_{\mathrm{KMS}}(\Gamma^{-1}(\mathcal U(T)X)),
--   $$
--   and $\mathcal Q_{\mathrm{Lamb}}(\rho)=-i[H_{\mathrm{Lamb}},\rho]$. These are the quantities of the contraction analysis of §8.
--
--   **Formalization Note** $\mathcal E_{\mathrm{KMS}}$ is the real part of the displayed quantity, which is real by Proposition 3.4.
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), (2.17), p.12; (8.4), p.62; (8.5)–(8.6), p.63; Q_Lamb, p.29

import Definitions.Def_SysBathGibbs_Generator

open Matrix MeasureTheory

namespace SysBathGibbs

/-!
# Dirichlet forms and the averaged ideal channel

Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), (2.17), p.12; (8.4), p.62;
(8.5)–(8.6), p.63.

**Formalization Note.** The quantity `⟨O, L†_KMS O⟩_{ρ_β}` is real, since `L†_KMS` is KMS-self-adjoint
(Proposition 3.4). `kmsDirichlet` takes its real part to land in `ℝ`.
-/

variable {n q : ℕ}

/-- The Dirichlet form `E_KMS(O) = -⟨O - Tr(ρ_β O) 1, L†_KMS(O - Tr(ρ_β O) 1)⟩_{ρ_β}`, (2.17),
(8.4). -/
noncomputable def kmsDirichlet (β : ℝ) (h : Fin (n - 1) → SysMat n q) (O : SysMat n q) : ℝ :=
  let O' := O - Matrix.trace (gibbs β (chainHam h) * O) • (1 : SysMat n q);
  -(kmsInner β (chainHam h) O' (hsAdjoint (LKMS β h) O')).re

/-- The Lamb-shift map `Q_Lamb(ρ) = -i[H_Lamb, ρ]`, p.29. -/
noncomputable def QLamb (β : ℝ) (h : Fin (n - 1) → SysMat n q) (ρ : SysMat n q) : SysMat n q :=
  (-Complex.I) • comm (HLamb β h) ρ

/-- `Θ_s = E_T[U(T) e^{sL} U(T)]`, (8.5), with `T` drawn from `μ_{T₀}`. -/
noncomputable def Theta (β : ℝ) (h : Fin (n - 1) → SysMat n q) (T₀ s : ℝ) (X : SysMat n q) :
    SysMat n q :=
  matInt (timeLaw T₀) fun T =>
    fwd (chainHam h) T (superExp s (Leff β h) (fwd (chainHam h) T X))

/-- `M_μ = Θ₀ = E_T U(2T)`, (8.5). -/
noncomputable def Mmu (h : Fin (n - 1) → SysMat n q) (T₀ : ℝ) (X : SysMat n q) : SysMat n q :=
  matInt (timeLaw T₀) fun T => fwd (chainHam h) (2 * T) X

/-- `D_μ(X) = ‖Γ⁻¹(X)‖²_{ρ_β} - ‖Γ⁻¹(M_μ X)‖²_{ρ_β}`, (8.6). -/
noncomputable def Dmu (β : ℝ) (h : Fin (n - 1) → SysMat n q) (T₀ : ℝ) (X : SysMat n q) : ℝ :=
  kmsNorm β (chainHam h) (Gam β (chainHam h) (-1) X) ^ 2 -
    kmsNorm β (chainHam h) (Gam β (chainHam h) (-1) (Mmu h T₀ X)) ^ 2

/-- `E_μ(X) = E_T E_KMS(Γ⁻¹(U(T) X))`, (8.6). -/
noncomputable def Emu (β : ℝ) (h : Fin (n - 1) → SysMat n q) (T₀ : ℝ) (X : SysMat n q) : ℝ :=
  ∫ T, kmsDirichlet β h (Gam β (chainHam h) (-1) (fwd (chainHam h) T X)) ∂(timeLaw T₀)

end SysBathGibbs


