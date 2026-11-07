-- Prove2me | Definitions.Def_OnlineShadow_LogRate_Xbar
-- name    : OnlineShadow_LogRate_Xbar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:08:42.961635+00:00
-- url     : https://prove2.me/theorems/3497247d-c359-4d1e-b44e-c540ef875ecd
-- title:
--   Centred lifted observable $\overline X=\overline A\otimes1_{\mathcal R}-\mathrm{Tr}(A\rho)1$
-- statement:
--   Let $\psi$ be a unit vector on $\mathcal H\otimes\mathcal R$ purifying $\rho=\mathrm{Tr}_{\mathcal R}|\psi\rangle\langle\psi|$, and $A$ a single-copy observable. With $\mu=\mathrm{Tr}(A\rho)$ and $X=(A-\mu1)\otimes1_{\mathcal R}$, the centred lifted observable on $(\mathcal H\otimes\mathcal R)^{\otimes n}$ is
--   $$\overline X=\frac1n\sum_{j=1}^nX_j=\overline{A\otimes1_{\mathcal R}}-\mu\,1 .$$
--   Its spectrum measures how far the empirical average of $A$ over the copies is from the true mean $\mathrm{Tr}(A\rho)$.
--
--
--   **Formalization Note** The paper uses $\mu$ without defining it; the display $PXP=(\mathrm{Tr}(A\rho)-\mu)P=0$ on p. 9 forces $\mu=\mathrm{Tr}(A\rho)$.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 3.3, p. 9

import Mathlib
import Definitions.Def_OnlineShadow_LogRate_liftObs
import Definitions.Def_OnlineShadow_LogRate_marginal

open scoped Kronecker

namespace OnlineShadow.LogRate

/-- The centred lifted observable `X̄ = Ā ⊗ 1_R − μ1` on `(H ⊗ R)^{⊗n}` with `μ = Tr(Aρ)` and
`ρ = Tr_R |ψ⟩⟨ψ|` (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 3.3, p.9: "`X ≜ (A − μ1) ⊗ 1_R`", `X̄` its lift). Equivalently
`X̄ = (1/n) ∑ⱼ Xⱼ`.

**Formalization Note** The paper uses `μ` without defining it; the display `PXP = (Tr(Aρ) − μ)P = 0`
on p.9 forces `μ = Tr(Aρ)` (paper.md R6). -/
noncomputable def Xbar {d r : ℕ} (ψ : Fin d × Fin r → ℂ) (n : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin n → Fin d × Fin r) (Fin n → Fin d × Fin r) ℂ :=
  liftObs n (A ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ)) - (((A * marginal ψ).trace.re : ℝ) : ℂ) • 1

end OnlineShadow.LogRate


