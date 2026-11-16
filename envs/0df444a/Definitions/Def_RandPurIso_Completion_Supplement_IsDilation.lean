-- Prove2me | Definitions.Def_RandPurIso_Completion_Supplement_IsDilation
-- name    : RandPurIso_Completion_Supplement_IsDilation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:48:53.766123+00:00
-- url     : https://prove2.me/theorems/cc6ef1d0-9c56-40f1-961c-6e6d250c077b
-- title:
--   Isometry dilation of a channel, $\mathrm{Tr}_E(V\rho V^\dagger)=\Phi(\rho)$
-- statement:
--   Let $X$ and $E$ be finite-dimensional spaces. A matrix $V:X\to X\otimes E$ is an **isometry dilation** of a map $\Phi$ on operators on $X$ if
--
--   $$
--   V^\dagger V=I\qquad\text{and}\qquad \mathrm{Tr}_E\big(V\rho V^\dagger\big)=\Phi(\rho)\ \text{ for every }\rho .
--   $$
--
--   The environment register $E$ is discarded after the isometry is applied. The module also defines the partial trace $\mathrm{Tr}_E(V\rho V^\dagger)$ for $V:X\to Y\otimes E$, and the Kraus family $K_e=(I\otimes\langle e|)V$ of such a $V$.
--
--   Dilations are the second access model of §7: two queries to any fixed dilation implement a self-switch (Construction 1, Lemma 3.12) and recover the hidden string of Theorem 7.10.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, §3.2, Construction 1, p. 21; §7, pp. 49–50, 58

import Mathlib
open Matrix

namespace RandPurIso.Completion.Supplement

/-- `Tr_E(V ρ V†)`: apply `V : X → Y ⊗ E` and trace out the environment `E`. -/
def traceEnv {X Y E : Type} [Fintype X] [Fintype E] (V : Matrix (Y × E) X ℂ)
    (ρ : Matrix X X ℂ) : Matrix Y Y ℂ :=
  fun i j => ∑ e, (V * ρ * Vᴴ) (i, e) (j, e)

/-- **Isometry dilation of a channel** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §3.2, Construction 1, p. 21; §7, pp. 49–50, 58).

`V : X → X ⊗ E` (`E` a finite environment) is an isometry dilation of `Φ` when `V† V = 1` and
`Tr_E(V ρ V†) = Φ(ρ)` for every `ρ`. -/
def IsDilation {X E : Type} [Fintype X] [DecidableEq X] [Fintype E]
    (V : Matrix (X × E) X ℂ) (Φ : Matrix X X ℂ → Matrix X X ℂ) : Prop :=
  Vᴴ * V = 1 ∧ ∀ ρ : Matrix X X ℂ, traceEnv V ρ = Φ ρ

/-- The Kraus family `K_e = (I ⊗ ⟨e|) V` of an isometry `V : X → Y ⊗ E` (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, proof of Lemma 3.12,
p. 22: `V = Σ_a K_a ⊗ |φ_a⟩`). -/
def dilKraus {X Y E : Type} (V : Matrix (Y × E) X ℂ) (e : E) : Matrix Y X ℂ :=
  fun i j => V (i, e) j

end RandPurIso.Completion.Supplement


