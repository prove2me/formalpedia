-- Prove2me | Definitions.Def_MayersQBC_expectedFidelity
-- name    : MayersQBC_expectedFidelity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:19.012738+00:00
-- url     : https://prove2.me/theorems/2d511231-af7f-4db2-83e5-a611f19ce501
-- title:
--   Expected fidelity $\mathbb E_\gamma F'(\gamma)$ of Bob's reduced states after commit′
-- statement:
--   Let $\Gamma$ be the finite set of classical transcripts $\gamma$ (the strings stored in the public register $H_S$ after Alice's modified commitment commit′), let $p(\gamma)$ be the probability of $\gamma$ when Alice commits to $0$ and $q(\gamma)$ its probability when she commits to $1$. For each $\gamma$ let $|\psi'_{0,\gamma}\rangle, |\psi'_{1,\gamma}\rangle$ be the pure states of Alice's side $A$ and Bob's side $B$ (in the paper $H_B \otimes H_{E,B}$) after commit′, and $\rho_B(\psi) = \operatorname{Tr}_A |\psi\rangle\langle\psi|$ Bob's reduced state. Define
--
--   $$
--   F'(\gamma) = \begin{cases} 0 & \text{if } q(\gamma) = 0 \ (\gamma \text{ determines the bit}),\\ F\big(\rho_B(\psi'_{0,\gamma}), \rho_B(\psi'_{1,\gamma})\big) & \text{otherwise,}\end{cases}
--   \qquad F(\rho,\sigma) = \Big(\operatorname{Tr}\sqrt{\sqrt\rho\,\sigma\sqrt\rho}\Big)^2,
--   $$
--
--   and the expected fidelity
--
--   $$
--   \mathbb E_\gamma F'(\gamma) = \sum_{\gamma \in \Gamma} p(\gamma)\, F'(\gamma).
--   $$
--
--   Security against Bob (the protocol is concealing) means that this quantity is arbitrarily close to $1$ for large security parameter; it is the hypothesis of the no-go theorem.
--
--   **Formalization Note** Alice's side is the first tensor factor, so Bob's reduced state is `traceLeft (pureDensity ψ)`. The fidelity is Jozsa's, the square of the published `rootFidelity`. "$\gamma$ determines $b$" is encoded as $q(\gamma) = 0$: such a transcript cannot occur when Alice commits to $1$.
-- source:
--   Mayers, Unconditionally secure quantum bit commitment is impossible, arXiv:quant-ph/9605044v2, section c, p.2 (definition of F(η)) and section e, second step, p.3 (F′(γ))

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
open QAlgorithms

namespace MayersQBC

open Classical in
/-- Mayers, *Unconditionally secure quantum bit commitment is impossible*,
arXiv:quant-ph/9605044v2, section c, p.2 ("Let us define F(η) = 0 if η determines a single value
of the bit b, otherwise let F(η) be the fidelity [9] between ρB(|ψ0,η⟩) and ρB(|ψ1,η⟩).") and
section e, second step, p.3 ("the expected value of the fidelity F′(γ) between the reduced density
matrices ρB(|ψ′b,γ⟩) for HB ⊗ HE,B in commit′"): the expected fidelity
`E_γ F′(γ) = Σ_γ p(γ) F′(γ)` of Bob's reduced states after commit′, where `p` is the law of the
classical transcript `γ` when Alice commits to `0`, and
`F′(γ) = 0` if `γ` determines the bit, else `F′(γ) = F(ρ_B(ψ′_{0,γ}), ρ_B(ψ′_{1,γ}))`.

**Formalization Note.** Alice's side `A` is the **first** tensor factor and
`QAlgorithms.traceLeft` traces it out, so `traceLeft (pureDensity ψ)` is Bob's reduced state
`ρ_B(ψ)`. The fidelity is Jozsa's [9], `F(ρ, σ) = (Tr √(√ρ σ √ρ))²`, i.e. the square of the
published `QAlgorithms.rootFidelity`. "`γ` determines `b`" is encoded as `q γ = 0`, where `q` is
the transcript law when Alice commits to `1`: such a `γ` can only occur under a commitment to `0`.
`F′(γ) = 0` there, as in section c. -/
noncomputable def expectedFidelity {Γ A B : Type} [Fintype Γ] [Fintype A] [Fintype B]
    [DecidableEq B] (p q : Γ → ℝ) (ψ0 ψ1 : Γ → EuclideanSpace ℂ (A × B)) : ℝ :=
  ∑ γ, p γ * (if q γ = 0 then 0 else
    rootFidelity (traceLeft (pureDensity (ψ0 γ))) (traceLeft (pureDensity (ψ1 γ))) ^ 2)

end MayersQBC


