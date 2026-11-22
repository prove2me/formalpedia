-- Prove2me | Definitions.Def_RandPurIso_Completion_Supplement_chanQubit
-- name    : RandPurIso_Completion_Supplement_chanQubit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:51:36.36114+00:00
-- url     : https://prove2.me/theorems/26420b9b-51d9-409e-ad8c-80531406a498
-- title:
--   A channel on a qubit register, with invalid strings failing to $\bot$
-- statement:
--   For a channel $\Phi$ on a finite space $X$, an injective encoding $e:X\to\{0,1\}^n$ and a string $\bot$ outside its range, let $E=\sum_x|e(x)\rangle\langle x|$. The qubit form of $\Phi$ is
--
--   $$
--   \rho\ \longmapsto\ E\,\Phi\big(E^\dagger\rho E\big)E^\dagger+\mathrm{Tr}\big((I-EE^\dagger)\rho\big)\,|\bot\rangle\langle\bot| .
--   $$
--
--   It applies $\Phi$ on the encoded subspace and maps every other string to $|\bot\rangle$, the convention of the base mission's `qubitChannel` (Definition 3.4) for a channel instead of a single operator. It is used to give circuits query access to the self-switch $\mathrm{Sw}[\mathcal C_z,\mathcal C_z]$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Definition 3.4, p. 18 (|⊥⟩ convention); Theorem 7.10, p. 58

import Mathlib
import Definitions.Def_ShiShallow_Core
open Matrix

namespace RandPurIso.Completion.Supplement

open ShiShallow

/-- **A channel on a qubit register**, in the convention of the base mission's `qubitChannel`
(Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 3.4, p. 18, "|⊥⟩ ∈ B"), for a channel instead of a single operator.

For `Φ : L(X) → L(X)`, an injective encoding `e : X → {0,1}^n` and a string `bot` outside its range,
with `E = Σ_x |e x⟩⟨x|`, the map is `ρ ↦ E Φ(E† ρ E) E† + Tr((I − E E†) ρ) |bot⟩⟨bot|`: `Φ` on the
encoded subspace, every other string failing to `⊥ = bot`.

**Formalization Note.** Injectivity of `e` and `bot ∉ range e` are properties of the concrete
encodings at each use. -/
noncomputable def chanQubit {X : Type} [Fintype X] {n : ℕ} (Φ : Matrix X X ℂ → Matrix X X ℂ)
    (e : X → Bits n) (bot : Bits n) (ρ : Matrix (Bits n) (Bits n) ℂ) : Matrix (Bits n) (Bits n) ℂ :=
  let E : Matrix (Bits n) X ℂ := fun u x => if u = e x then 1 else 0
  E * Φ (Eᴴ * ρ * E) * Eᴴ + ((1 - E * Eᴴ) * ρ).trace • Matrix.single bot bot 1

end RandPurIso.Completion.Supplement


