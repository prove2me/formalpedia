-- Prove2me | Definitions.Def_RandPurIso_Completion_coherentMeasU
-- name    : RandPurIso_Completion_coherentMeasU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:23.860893+00:00
-- url     : https://prove2.me/theorems/69a466de-b459-49a6-a9b8-97430793209d
-- title:
--   Coherent measurement $M^\Pi$: $U_\Pi=\Pi\otimes X+(I-\Pi)\otimes I$ (Definition 3.8)
-- statement:
--   For a projector $\Pi$ on a register $A$ and a qubit $C$, $M^\Pi$ is conjugation by the unitary
--   $$U_\Pi:=\Pi_A\otimes X_C+(I_A-\Pi_A)\otimes I_C .$$
--   With $C$ initialized to $|b\rangle$ it records $b\oplus1$ on the image of $\Pi$ and $b$ on its complement. The channel $M^\Pi$ is $\Phi_{U_\Pi}$ (no failure weight, since $U_\Pi$ is unitary).
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Definition 3.8, p. 19

import Mathlib
import Definitions.Def_ShiShallow_Core
open Matrix

namespace RandPurIso.Completion

/-- **Coherent two-outcome measurement** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 3.8, p. 19): for a projector `Π` on
`A` and a qubit `C`, `M^Π` is conjugation by `U_Π := Π_A ⊗ X_C + (I_A − Π_A) ⊗ I_C`.
This is the matrix `U_Π` on `A ⊗ C`; the channel `M^Π` is `contractionChannel U_Π` (whose `⊥`
weight vanishes since `U_Π` is unitary for a projector `Π`).

**Formalization Note.** The qubit `C` is `Bool`; `X_C` is `ShiShallow.xMat`. -/
noncomputable def coherentMeasU {X : Type} [Fintype X] [DecidableEq X] (P : Matrix X X ℂ) :
    Matrix (X × Bool) (X × Bool) ℂ :=
  Matrix.kronecker P ShiShallow.xMat + Matrix.kronecker (1 - P) 1

end RandPurIso.Completion


