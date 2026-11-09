-- Prove2me | Definitions.Def_XorParallelRepetition_Exponential_BLR
-- name    : XorParallelRepetition_Exponential_BLR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:04:39.691349+00:00
-- url     : https://prove2.me/theorems/06f28e74-5880-4f78-8a44-7435f46f4daf
-- title:
--   §1.3.2 — the BLR transformation $\Psi\mapsto\Psi'$
-- statement:
--   Let $\Psi$ be a $k$-XOR game with question law $\mu$ and target $t$. The game $\Psi'$ has $2k$ players, labeled $i$ and $i'$ for each player $i$ of $\Psi$; the questions of both are in $\Sigma_i\times\mathbb F_p$ and their answers are in $\mathbb F_p$. The verifier proceeds as follows:
--
--   1. sample $x\sim\mu$, and sample $\gamma,\alpha_1,\dots,\alpha_k\in\mathbb F_p$ uniformly, all independently;
--   2. send $(x_i,\alpha_i)$ to player $i$ and $(x_i,\alpha_i+\gamma)$ to player $i'$;
--   3. accept exactly when
--
--   $$
--   \sum_{i}\bigl(f_{i'}(x_i,\alpha_i+\gamma)+f_i(x_i,\alpha_i)\bigr)=\gamma\,t(x).
--   $$
--
--   One $\gamma$ is shared by all pairs. The transformation keeps the repeated value from decreasing (Claim 4.2) and removes all commuting embeddings when $\operatorname{val}(\Psi)<1$ (Lemma 1.7).
--
--   **Formalization Note** $\Psi'$ is a generalized XOR game with players $\iota\times\mathrm{Bool}$, where $(i,\mathrm{false})$ is $i$ and $(i,\mathrm{true})$ is $i'$. Its law pairs the question tuple with the target $\gamma t(x)$, which is not sent to the players.
-- source:
--   Mark Braverman, Dor Minzer, STOC 2027 submission #195 (October 2026), §1.3.2, printed p. 6, PDF p. 6

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames

/-!
# The BLR transformation

Source: Braverman and Minzer, STOC 2027 submission #195, §1.3.2 (printed/PDF p. 6).
-/

namespace XorParallelRepetition.Exponential

universe u

variable {p : ℕ} {ι : Type}

namespace XorGame

/-- The challenge of `Ψ′` built from `x`, `γ` and `α`: the player `(i, false)`, written `i` in the
source, receives `(x_i, α_i)`, the player `(i, true)`, written `i′`, receives `(x_i, α_i + γ)`,
and the right hand side is `γ t(x)`. -/
def blrChallenge (Ψ : XorGame.{u} p ι) (x : ∀ i, Ψ.Q i) (γ : ZMod p) (α : ι → ZMod p) :
    (∀ s : ι × Bool, Ψ.Q s.1 × ZMod p) × ZMod p :=
  (fun s => (x s.1, if s.2 then α s.1 + γ else α s.1), γ * Ψ.t x)

/-- The game `Ψ′` of the BLR trick (§1.3.2), with `2k` players `i` and `i′` whose questions are in
`Σ_i × F_p`.  The verifier samples `x ∼ μ`, one `γ` shared by all pairs and `α₁, …, α_k`,
independently and uniformly in `F_p`, sends `(x_i, α_i)` to `i` and `(x_i, α_i + γ)` to `i′`, and
accepts exactly when the sum of the `2k` answers is `γ t(x)`.  The right hand side is the sampled
target of a generalized game, so it is not sent to the players. -/
noncomputable def blr [Fact p.Prime] [DecidableEq ι] [Fintype ι] (Ψ : XorGame.{u} p ι) :
    GeneralizedXorGame.{u} p (ι × Bool) where
  Q s := Ψ.Q s.1 × ZMod p
  μ := Ψ.μ.bind fun x =>
    (PMF.uniformOfFintype (ZMod p)).bind fun γ =>
      (PMF.uniformOfFintype (ι → ZMod p)).map fun α => Ψ.blrChallenge x γ α

end XorGame

end XorParallelRepetition.Exponential


