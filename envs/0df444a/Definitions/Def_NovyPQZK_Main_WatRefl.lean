-- Prove2me | Definitions.Def_NovyPQZK_Main_WatRefl
-- name    : NovyPQZK_Main_WatRefl
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:35:01.036682+00:00
-- url     : https://prove2.me/theorems/94ac2ecc-9373-4a6a-937f-a61cd6973f6a
-- title:
--   Watrous single-reflection WatRefl (Procedure 1)
-- statement:
--   Let $\Delta = \{\Delta_1,\Delta_0\}$ be a **two-outcome projective measurement** on a register (two projectors with $\Delta_1 + \Delta_0 = 1$) and $\Gamma$ a projector on the same register. The procedure $\mathrm{WatRefl}^\Gamma_\Delta$ measures its input with $\Delta$ and, on outcome $0$, applies the reflection $2\Gamma - 1$ about the image of $\Gamma$. The outcome is not visible outside the procedure, so it is the channel
--
--   $$\mathrm{WatRefl}^\Gamma_\Delta(\sigma) = \Delta_1\sigma\Delta_1 + (2\Gamma-1)\,\Delta_0\sigma\Delta_0\,(2\Gamma-1).$$
--
--   It is one step of Watrous's rewinding without repetition; the inverter's searcher applies it once per round of interactive hashing.
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §3.2 p. 17, Procedure 1

import Mathlib
import Definitions.Def_NovyPQZK_Main_Fidelity

namespace NovyPQZK.Main

/-!
Dupuis, Ligez, Medhioub, Salvail, Thibodeau, arXiv:2610.33185 (sha256 857d8563…3257f), §3.2,
p. 17, Procedure 1: Watrous single-reflection.

For a two-outcome projective measurement `Δ = {Δ₁, Δ₀}` and a projector `Γ` on the same register,
`WatRefl^Γ_Δ` measures with `Δ` and, on outcome `0`, reflects about the image of `Γ`. The outcome
is not visible outside the procedure, so it acts as the channel
`σ ↦ Δ₁ σ Δ₁ + (2Γ − 1) Δ₀ σ Δ₀ (2Γ − 1)`.
-/

/-- `Δ = {Δ₁, Δ₀}` is a two-outcome projective measurement: two projectors summing to `1`
(they are then mutually orthogonal). -/
def IsTwoOutcomeMeas {ι : Type*} [Fintype ι] [DecidableEq ι] (Δ₁ Δ₀ : Matrix ι ι ℂ) : Prop :=
  IsProjector Δ₁ ∧ IsProjector Δ₀ ∧ Δ₁ + Δ₀ = 1

/-- Procedure 1 (p. 17): `WatRefl^Γ_Δ(σ) = Δ₁ σ Δ₁ + (2Γ − 1) Δ₀ σ Δ₀ (2Γ − 1)`. -/
def watRefl {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ Δ₁ Δ₀ σ : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  Δ₁ * σ * Δ₁ + (2 • Γ - 1) * Δ₀ * σ * Δ₀ * (2 • Γ - 1)

end NovyPQZK.Main


