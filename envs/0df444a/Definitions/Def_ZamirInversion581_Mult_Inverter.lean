-- Prove2me | Definitions.Def_ZamirInversion581_Mult_Inverter
-- name    : ZamirInversion581_Mult_Inverter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:28.14487+00:00
-- url     : https://prove2.me/theorems/ea8aabc6-3496-4f75-82aa-fbb9a6ccd0fb
-- title:
--   Inversion oracles and their average success on $\mathrm{GL}_m(F)$
-- statement:
--   An **inversion oracle** over a field $F$ is a family $I=(I_m)_{m\in\mathbb N}$ in which $I_m$ sends each $m\times m$ matrix to a probability distribution on $m\times m$ matrices. It is an arbitrary randomized map, and it may answer anything on a singular input. Each call uses fresh randomness.
--
--   The **average success** of $I$ in dimension $m$ is
--
--   $$
--   \Pr_{Y\sim\mathrm{GL}_m(F)}[I_m(Y)=Y^{-1}]=\frac1{|\mathrm{GL}_m(F)|}\sum_{Y\in\mathrm{GL}_m(F)}\Pr[I_m(Y)=Y^{-1}].
--   $$
--
--   This is the hypothesis of the main theorem and of the amplification lemma.
--
--   **Formalization Note** The average runs over the finite group $\mathrm{GL}_m(F)$ and $Y^{-1}$ is the group inverse, so Lean's convention $A^{-1}=0$ for singular $A$ does not enter this definition.
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.2, Theorem 1.1, success hypothesis; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform

set_option autoImplicit false

namespace ZamirInversion581.Mult

/-!
# Inversion oracles and their average success

Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256
175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.2, Theorem 1.1:
`Pr_{Y ∼ GL_m(F_q)}[I_m(Y) = Y⁻¹] ≥ ε`.

The oracle has no time structure of its own and may answer anything on a singular input. The average
is over the finite group `GL_m(F)`, with the inverse taken in that group: Lean's `A⁻¹ = 0` for a
singular `A` does not enter this definition.
-/

/-- A family of randomized maps, one in each dimension, from `m × m` matrices to distributions on
`m × m` matrices. Every call samples afresh. -/
abbrev InversionOracle (F : Type*) :=
  ∀ m : ℕ, Matrix (Fin m) (Fin m) F → PMF (Matrix (Fin m) (Fin m) F)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The average success `Pr_{Y ∼ GL_m(F)}[I_m(Y) = Y⁻¹]`: the mean over `Y ∈ GL_m(F)` of the
probability that `I m Y` equals the group inverse of `Y`. -/
noncomputable def inverterSuccess (I : InversionOracle F) (m : ℕ) : ℝ :=
  unifMean fun Y : Matrix.GeneralLinearGroup (Fin m) F =>
    (I m (Y : Matrix (Fin m) (Fin m) F)
      ((Y⁻¹ : Matrix.GeneralLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F)).toReal

end ZamirInversion581.Mult


