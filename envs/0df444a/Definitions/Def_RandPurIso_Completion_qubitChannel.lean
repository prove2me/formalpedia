-- Prove2me | Definitions.Def_RandPurIso_Completion_qubitChannel
-- name    : RandPurIso_Completion_qubitChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:28:18.615078+00:00
-- url     : https://prove2.me/theorems/db0f11f5-1edf-4de2-a24b-a52c83fc0d7c
-- title:
--   $\Phi_K$ on a qubit register with a designated $|\perp\rangle$
-- statement:
--   For $K:X\to Y$, encodings $e_X:X\to\{0,1\}^m$, $e_Y:Y\to\{0,1\}^m$ and a string $\perp$ outside the range of $e_Y$, let $\hat K=\sum_{x,y}K_{yx}|e_Y(y)\rangle\langle e_X(x)|$ (zero on strings that encode no $x$). The channel is
--   $$\rho\mapsto\hat K\rho\hat K^\dagger+\operatorname{Tr}\big((I-\hat K^\dagger\hat K)\rho\big)|\perp\rangle\langle\perp|,$$
--   which is $\Phi_K$ of Definition 3.4 in the convention "$|\perp\rangle\in B$", with inputs outside the encoded $X$ failing to $\perp$. It is the form in which circuits query $\Phi^V$, $\Phi^{\mathrm{ctrl}[V]}$ and $M^\Pi$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Definition 3.4, p. 18

import Mathlib
import Definitions.Def_RandPurIso_Completion_QInstr
open Matrix

namespace RandPurIso.Completion

open ShiShallow

/-- **`Φ_K` on a qubit register** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 3.4, p. 18, with "|⊥⟩ ∈ B").

For `K : X → Y`, injective encodings `eX : X → {0,1}^m`, `eY : Y → {0,1}^m` and a string `bot`
outside the range of `eY`, let `K̂ = Σ_{x,y} K_{yx} |eY y⟩⟨eX x|` (zero on strings that encode no
`x`). The channel is `ρ ↦ K̂ρK̂† + Tr((I − K̂†K̂)ρ) |bot⟩⟨bot|`, i.e. `Φ_K` with inputs outside the
encoded `X` failing to `⊥ = bot`.

**Formalization Note.** Injectivity of the encodings and `bot ∉ range eY` are properties of the
concrete encodings at each use, not hypotheses. -/
noncomputable def qubitChannel {X Y : Type} [Fintype X] [Fintype Y] {m : ℕ}
    (K : Matrix Y X ℂ) (eX : X → Bits m) (eY : Y → Bits m) (bot : Bits m)
    (ρ : Matrix (Bits m) (Bits m) ℂ) : Matrix (Bits m) (Bits m) ℂ :=
  let Kh : Matrix (Bits m) (Bits m) ℂ :=
    fun u v => ∑ y, ∑ x, if u = eY y ∧ v = eX x then K y x else 0
  Kh * ρ * Khᴴ + ((1 - Khᴴ * Kh) * ρ).trace • Matrix.single bot bot 1

end RandPurIso.Completion


