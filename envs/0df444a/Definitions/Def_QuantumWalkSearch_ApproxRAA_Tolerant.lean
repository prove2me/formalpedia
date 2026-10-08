-- Prove2me | Definitions.Def_QuantumWalkSearch_ApproxRAA_Tolerant
-- name    : QuantumWalkSearch_ApproxRAA_Tolerant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:29.038222+00:00
-- url     : https://prove2.me/theorems/f4d21f0a-ef6a-4dae-9deb-2ee97d48026b
-- title:
--   Tolerant RAA(t_max, γ): the leftover states |ν⊥ᵢ⟩, the states |ψᵢ⟩ = Aᵢ|ν⊥_{i−1}⟩ and the success probability (p. 15)
-- statement:
--   This module defines the success probability of the procedure **Tolerant RAA**$(t_{\max},\gamma)$ of Magniez, Nayak, Roland and Santha:
--
--   1. sample a state $x$ from the stationary distribution; if $x\in M$, output it and stop;
--   2. prepare $|\pi\rangle|0^S\rangle$; for $i=1,2,\dots,t_{\max}$: apply Approximate RAA$(i,\gamma)$, i.e. $A_i$, and measure the first register according to $\Pi_M$; if successful, output the first register and stop;
--   3. otherwise output "No marked element".
--
--   The procedure uses $T=t_{\max}$ registers $K_1,\dots,K_{t_{\max}}$ and does not reset them between attempts. Its states are
--   $$
--   |\nu_0^\perp\rangle=|\varphi_0\rangle=|\pi\rangle|0^S\rangle,\qquad |\psi_i\rangle=A_i|\nu^\perp_{i-1}\rangle,\qquad |\nu_i^\perp\rangle=\frac{\Pi_{\tilde M^\perp}|\psi_i\rangle}{\|\Pi_{\tilde M^\perp}|\psi_i\rangle\|}\quad(i\ge1),
--   $$
--   where $|\nu_i^\perp\rangle$ is the post-measurement state after a failed measurement at attempt $i$. The measurement at attempt $i$ succeeds, given that the earlier ones failed, with probability $\sin^2\theta_i=\|\Pi_{\tilde M}|\psi_i\rangle\|^2$. The probability that Tolerant RAA ends with a marked element is
--   $$
--   p_M+(1-p_M)\Big(1-\prod_{i=1}^{t_{\max}}\big(1-\sin^2\theta_i\big)\Big),
--   $$
--   where $p_M=\|\Pi_M|\pi\rangle\|^2$ is the probability that step 1 samples a marked element.
--
--   **Formalization Note** In the paper $|\pi\rangle=\sum_x\sqrt{\pi_x}|x\rangle|p_x\rangle$, and measuring its first register samples from the stationary distribution $\pi$ (p. 11), so the classical sample of step 1 succeeds with probability $\sum_{x\in M}\pi_x=\|\Pi_M|\pi\rangle\|^2$; for a general state $|\pi\rangle$ that quantity is used. When $\Pi_{\tilde M^\perp}|\psi_i\rangle=0$ the attempt succeeds with probability $1$ and $|\nu^\perp_i\rangle$ is set to $0$; the product is then $0$ and later attempts do not matter. The formula for $|\psi_i\rangle$ gives $|\varphi_0\rangle$ at $i=0$.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 15 (Tolerant RAA(t_max, γ); ψᵢ, θᵢ, νᵢ, ν⊥ᵢ in the proof of Lemma 2), p. 11 (measuring |π⟩ samples π)

import Mathlib
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Setting
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Circuit

namespace QuantumWalkSearch.ApproxRAA

open Matrix

/-! # Tolerant RAA(t_max, γ) (p. 15) and its success probability

Tolerant RAA works on `H ⊗ [⊗_{i=1}^{T} K_i]` with `T = t_max` registers. After the classical
sample of steps 1–2 fails it prepares `|φ₀⟩ = |π⟩|0^S⟩`; attempt `i = 1, 2, …, t_max` applies
`A_i` (Approximate RAA(i, γ)) to the state left over by attempt `i − 1` and measures
`{Π_M̃, Id − Π_M̃}`. On failure the state collapses to the normalized `Π_{M̃⊥}` part; the
registers are not reset (proof of Lemma 2, p. 15). -/

variable {X : Type*} [Fintype X] [DecidableEq X] {κ : ℕ → Type*} [∀ i, Fintype (κ i)]
  [∀ i, DecidableEq (κ i)]

/-- The state `|ν⊥_i⟩` left over after `i` failed attempts: `|ν⊥_0⟩ = |φ₀⟩` and
`|ν⊥_{i+1}⟩ = Π_{M̃⊥} A_{i+1} |ν⊥_i⟩ / ‖Π_{M̃⊥} A_{i+1} |ν⊥_i⟩‖` (p. 15; `0` if that projection
vanishes, a case in which attempt `i + 1` succeeds with probability one). -/
noncomputable def leftover (M : Finset X) (z : ∀ i, κ i)
    (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (piState : EuclideanSpace ℂ (X × X))
    (T : ℕ) : ℕ → EuclideanSpace ℂ (X × X × Regs κ T)
  | 0 => initState z T piState
  | i + 1 =>
    normalize (act (unmarkedProj M)
      (act (approxRAA M z R T (i + 1)) (leftover M z R piState T i)))

/-- `|ψ_i⟩ = A_i |ν⊥_{i−1}⟩`, the state after Step 4 of attempt `i ≥ 1` (p. 15). For `i = 0`
the formula gives `|φ₀⟩`. -/
noncomputable def tolState (M : Finset X) (z : ∀ i, κ i)
    (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (piState : EuclideanSpace ℂ (X × X))
    (T i : ℕ) : EuclideanSpace ℂ (X × X × Regs κ T) :=
  act (approxRAA M z R T i) (leftover M z R piState T (i - 1))

/-- The probability that the measurement of Step 5 in attempt `i` succeeds, given that the
earlier attempts failed: `sin² θ_i = ‖Π_M̃ |ψ_i⟩‖²` (p. 15). -/
noncomputable def attemptProb (M : Finset X) (z : ∀ i, κ i)
    (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (piState : EuclideanSpace ℂ (X × X))
    (T i : ℕ) : ℝ :=
  ‖act (markedProj M) (tolState M z R piState T i)‖ ^ 2

/-- The probability that Tolerant RAA(t_max, γ) ends with a marked element, with `T = t_max`
registers. Steps 1–2 succeed with probability `p_M = ‖Π_M |π⟩‖²`; otherwise the attempts
`i = 1, …, t_max` run in turn and the algorithm fails only if all of them fail:
`p_M + (1 − p_M) · (1 − ∏_{i=1}^{t_max} (1 − sin² θ_i))`. -/
noncomputable def successProb (M : Finset X) (z : ∀ i, κ i)
    (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (piState : EuclideanSpace ℂ (X × X))
    (tmax : ℕ) : ℝ :=
  markedWeight M piState + (1 - markedWeight M piState) *
    (1 - ∏ i ∈ Finset.Icc 1 tmax, (1 - attemptProb M z R piState tmax i))

end QuantumWalkSearch.ApproxRAA


