-- Prove2me | Definitions.Def_RouzeFranca_LearnGibbs_relEnt
-- name    : RouzeFranca_LearnGibbs_relEnt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:46:39.321925+00:00
-- url     : https://prove2.me/theorems/622a6073-260a-4469-a3d9-f95dc78f7f5f
-- title:
--   Quantum relative entropy $D(\rho\|\sigma)$ in nats
-- statement:
--   For operators $\rho,\sigma$ on $n$ qubits, the **relative entropy** is
--   $$
--   D(\rho\|\sigma)=\begin{cases}\operatorname{tr}\bigl[\rho(\log\rho-\log\sigma)\bigr], & \operatorname{supp}\rho\subseteq\operatorname{supp}\sigma,\\ +\infty, & \text{otherwise,}\end{cases}
--   $$
--   with the natural logarithm.
--
--   It is the divergence in which the paper measures the quality of the learned Gibbs state; the transportation cost inequality converts it into a Wasserstein bound.
--
--   **Formalization Note** Valued in the extended reals. The support condition is $\ker\sigma\subseteq\ker\rho$. The logarithms are taken by the continuous functional calculus with Lean's `Real.log 0 = 0`, which gives the convention $0\log0=0$ on the kernel. The platform's `WildeQIT.QMemory.qRelEntropy` has the same shape in base 2 and is not reused, because the constants of the paper (Pinsker, the transportation cost constant $\alpha$) are in nats.
-- source:
--   Rouzé, Stilck França, Learning quantum many-body systems from a few copies, arXiv:2107.03333v4, App. A, p. 14

import Mathlib
import Definitions.Def_RouzeFranca_LearnGibbs_gibbs

open Matrix

namespace RouzeFranca.LearnGibbs

open Classical in
/-- The (Umegaki) relative entropy in nats,
`D(ρ‖σ) = tr[ρ(log ρ − log σ)]` if the support of `ρ` is contained in that of `σ`, and `+∞`
otherwise.

Rouzé, Stilck França, arXiv:2107.03333v4, App. A, p. 14: "D(ρ∥σ) = tr[ρ(log(ρ) − log(σ))]
whenever the support of ρ is contained in that of σ and +∞ otherwise".

**Formalization Note.** Valued in `EReal`, with `⊤` off support. The support condition is
`ker σ ⊆ ker ρ` (for positive semidefinite matrices, the support is the orthogonal complement of
the kernel). The logarithms are the continuous functional calculus `cfc Real.log`, with the
**natural** logarithm; Lean's `Real.log 0 = 0` gives the convention `0 log 0 = 0` on the kernel.
This has the shape of the platform's `WildeQIT.QMemory.qRelEntropy`, which uses base 2 and is
therefore not reused: the paper's Pinsker and transportation-cost constants are in nats. -/
noncomputable def relEnt {n : ℕ} (ρ σ : Mat n) : EReal :=
  if LinearMap.ker (Matrix.toLin' σ) ≤ LinearMap.ker (Matrix.toLin' ρ) then
    (((trace (ρ * cfc Real.log ρ)).re - (trace (ρ * cfc Real.log σ)).re : ℝ) : EReal)
  else ⊤

end RouzeFranca.LearnGibbs


