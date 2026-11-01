-- Prove2me | Definitions.Def_MayersQBC_cheatProb
-- name    : MayersQBC_cheatProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:13.931069+00:00
-- url     : https://prove2.me/theorems/024b9d52-8a7a-4c58-8f28-cd25e6f1a709
-- title:
--   Alice's cheating probability: unveil′ returns 1 after commit′ with $b = 0$
-- statement:
--   In the attack, Alice runs commit′: she commits to $b = 0$ honestly except that she never sends a register away to the environment, so after the commitment the joint state on transcript $\gamma$ (probability $p(\gamma)$) is the pure state $|\psi'_{0,\gamma}\rangle$ of Alice's side $A$ and Bob's side $B$. In her modified unveil′ she applies a unitary $U_\gamma$ to her own side and then runs the honest unveil of the bit $1$. Writing $\Pi_\gamma$ for the effect ($0 \preceq \Pi_\gamma \preceq I$) "the honest unveil of $1$ returns $1$" on transcript $\gamma$, her success probability is
--
--   $$
--   \sum_{\gamma\in\Gamma} p(\gamma)\, \big\langle \psi'_{0,\gamma}\big|\, (U_\gamma \otimes I)^\dagger\, \Pi_\gamma\, (U_\gamma \otimes I)\, \big|\psi'_{0,\gamma}\big\rangle .
--   $$
--
--   This is the quantity the no-go theorem shows tends to $1$.
--
--   **Formalization Note** Alice's side is the first tensor factor and her operation is `Matrix.kronecker (U γ) 1`; the probability of an effect $M$ on a state $\rho$ is `effectProb M ρ` $= \operatorname{Re}\operatorname{Tr}(M\rho)$. Unitarity of $U_\gamma$ and the effect property of $\Pi_\gamma$ (Lean `acc γ`) are hypotheses of the theorems that use this definition.
-- source:
--   Mayers, Unconditionally secure quantum bit commitment is impossible, arXiv:quant-ph/9605044v2, section e, first step, p.3 (commit′) and third step, p.4 (unveil′)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
open QAlgorithms

namespace MayersQBC

/-- Mayers, *Unconditionally secure quantum bit commitment is impossible*,
arXiv:quant-ph/9605044v2, section e, first and third steps, pp.3–4 ("in the modified procedure
commit′, Alice chooses b = 0 and never sends a register away to the environment except when this
register contains a classical bit that she must transmit to Bob"; "Alice in unveil′ can transform
|ψ′0,γ⟩ into |ψ01⟩ … and then continue with the honest unveil"): the probability that Alice's
modified unveil′ returns `1` after commit′ with `b = 0`. On transcript `γ` (probability `p γ`)
the joint state is `ψ′_{0,γ}`; Alice applies the unitary `U γ` to her side and then runs the
honest unveil of `1`, whose outcome "returns 1" is the effect `acc γ`:
`Σ_γ p(γ) ⟨ψ′_{0,γ}| (U_γ ⊗ I)† acc_γ (U_γ ⊗ I) |ψ′_{0,γ}⟩`.

**Formalization Note.** Alice's side `A` is the **first** tensor factor, so her operation is
`Matrix.kronecker (U γ) 1`. The honest unveil of `1` (Alice's honest actions, the messages and
Bob's verdict) is represented by one effect `acc γ` on the post-commit system for each
transcript, since Bob holds `γ`; `effectProb M ρ = Re Tr(M ρ)`. Unitarity of `U γ` and the
effect property of `acc γ` are hypotheses of the statements that use this definition. -/
noncomputable def cheatProb {Γ A B : Type} [Fintype Γ] [Fintype A] [Fintype B] [DecidableEq B]
    (p : Γ → ℝ) (acc : Γ → Matrix (A × B) (A × B) ℂ) (U : Γ → Matrix A A ℂ)
    (ψ0 : Γ → EuclideanSpace ℂ (A × B)) : ℝ :=
  ∑ γ, p γ * effectProb (acc γ)
    (pureDensity (act (Matrix.kronecker (U γ) (1 : Matrix B B ℂ)) (ψ0 γ)))

end MayersQBC


