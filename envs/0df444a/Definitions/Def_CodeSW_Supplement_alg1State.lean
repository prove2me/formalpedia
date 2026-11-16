-- Prove2me | Definitions.Def_CodeSW_Supplement_alg1State
-- name    : CodeSW_Supplement_alg1State
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:49:08.881557+00:00
-- url     : https://prove2.me/theorems/42d8d37c-760a-4ab3-ba31-3a54b61999dc
-- title:
--   Algorithm 1 (quantum code Gibbs sampling): the exact classical–quantum law $\sigma_t$ and the averaged output $\rho_T=\mathbb E_\phi|\phi\rangle\langle\phi|$
-- statement:
--   Algorithm 1 takes a stabilizer matrix $g$, a classical transition matrix $Q$ on $\{0,1\}^{2n}$, an initial unit vector $|\phi_0\rangle$ and an initial classical state $x_0$. Each iteration (i) measures the stabilizers $P(g_1),\dots,P(g_c)$ on $|\phi\rangle$, giving a syndrome $s\in S_g$ and the post-measurement state $|\phi_s\rangle$, and (ii) samples $y\leftarrow Q(x,\cdot)$ and sets $|\phi\rangle\leftarrow P(y)E(s)|\phi_s\rangle$, $x\leftarrow y$. Here $E(s)=P(e_s)$ for a preimage $e_s$ of $s$ under $h=g\omega$.
--
--   The exact law of the process after $t$ iterations is recorded by the unnormalized classical–quantum state $\sigma_t$, where $\sigma_t(x)$ is the expectation of $\mathbf 1(x_t=x)\,|\phi_t\rangle\langle\phi_t|$:
--   $$\sigma_0(x)=\mathbf 1(x=x_0)\,|\phi_0\rangle\langle\phi_0|,\qquad \sigma_{t+1}(y)=\sum_x\sum_{s\in S_g}Q(x,y)\,U_{y,s}\,\Pi(g,s)\,\sigma_t(x)\,\Pi(g,s)\,U_{y,s}^\dagger,$$
--   with $U_{y,s}=P(y)E(s)$. The **averaged output** after $T$ iterations is $\rho_T=\mathbb E_\phi|\phi\rangle\langle\phi|=\sum_x\sigma_T(x)$.
--
--   This is the object whose limit Theorem 4 identifies with the Gibbs state.
--
--   **Formalization Note** Outcome $s$ occurs with probability $\operatorname{tr}(\Pi(g,s)\phi)$ and leaves the normalized state $\Pi(g,s)\phi\Pi(g,s)/\operatorname{tr}(\Pi(g,s)\phi)$, so averaging removes the normalization. The choice of preimages $s\mapsto e_s$ is a parameter; the page takes the lexicographically first one. The module also defines `alg1Output`, the sum $\sum_x\sigma_T(x)$.
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Algorithm 1 and Theorem 4, p.12; §2.1.1, p.11 (E(s))

import Definitions.Def_CodeSW_Supplement_pauli

set_option autoImplicit false

open Matrix

noncomputable section

namespace CodeSW.Supplement

/-- The exact law of **Algorithm 1 (quantum code Gibbs sampling)** after `t` iterations, as the
unnormalized classical–quantum state `σ_t : {0,1}^{2n} → operators`: `σ_t(x)` is the expectation of
`1(x_t = x) |ϕ_t⟩⟨ϕ_t|` over all measurement outcomes and classical samples
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, Algorithm 1, p.12).

Start: `|ϕ⟩ = |ϕ₀⟩`, `x = x₀`, so `σ_0(x) = 1(x = x₀) |ϕ₀⟩⟨ϕ₀|`. One iteration: (i) measure the
stabilizers on `|ϕ⟩`, giving the syndrome `s ∈ S_g` with probability `tr(Π(g,s)ϕ)` and the
post-measurement state `Π(g,s)|ϕ⟩/‖Π(g,s)|ϕ⟩‖`; (ii) sample `y ← Q(x, ·)` and set
`|ϕ⟩ ← P(y)E(s)|ϕ_s⟩`, `x ← y`. Hence
`σ_{t+1}(y) = ∑_x ∑_{s∈S_g} Q(x,y) · U Π(g,s) σ_t(x) Π(g,s) U†` with `U = P(y)E(s)`.

**Formalization Note** `E(s) = P(e s)`, where `e` is a choice of preimage of each syndrome under
`h = gω` (the page takes the lexicographically first one). Averaging the post-measurement state with
the outcome probability removes the normalization. `Q` is any real matrix on `{0,1}^{2n}`; the
theorem assumes it is stochastic. -/
def alg1State {n c : ℕ} (g : Matrix (Fin c) (Fin (n + n)) (ZMod 2))
    (Q : Matrix (Fin (n + n) → ZMod 2) (Fin (n + n) → ZMod 2) ℝ)
    (e : (Fin c → ZMod 2) → (Fin (n + n) → ZMod 2)) (x₀ : Fin (n + n) → ZMod 2)
    (ϕ₀ : (Fin n → ZMod 2) → ℂ) : ℕ → (Fin (n + n) → ZMod 2) → QOp n
  | 0 => fun x => if x = x₀ then Matrix.vecMulVec ϕ₀ (star ϕ₀) else 0
  | t + 1 => fun y => ∑ x, ∑ s ∈ syndromes g,
      ((Q x y : ℝ) : ℂ) • ((pauli y * pauli (e s)) * synProj g s * alg1State g Q e x₀ ϕ₀ t x *
        synProj g s * (pauli y * pauli (e s))ᴴ)

/-- The **averaged output** `ρ_T = E_ϕ |ϕ⟩⟨ϕ|` of Algorithm 1 after `T` iterations:
`ρ_T = ∑_x σ_T(x)` (arXiv:2510.08446, manuscript sha256 4e4abb5e…, Algorithm 1 and Theorem 4,
p.12). -/
def alg1Output {n c : ℕ} (g : Matrix (Fin c) (Fin (n + n)) (ZMod 2))
    (Q : Matrix (Fin (n + n) → ZMod 2) (Fin (n + n) → ZMod 2) ℝ)
    (e : (Fin c → ZMod 2) → (Fin (n + n) → ZMod 2)) (x₀ : Fin (n + n) → ZMod 2)
    (ϕ₀ : (Fin n → ZMod 2) → ℂ) (T : ℕ) : QOp n :=
  ∑ x, alg1State g Q e x₀ ϕ₀ T x

end CodeSW.Supplement


