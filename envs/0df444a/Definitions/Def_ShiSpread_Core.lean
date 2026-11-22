-- Prove2me | Definitions.Def_ShiSpread_Core
-- name    : ShiSpread_Core
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-11T07:52:49.917305+00:00
-- url     : https://prove2.me/theorems/a0a8afe3-2b10-41d7-b907-4a78ac8bac22
-- title:
--   State extension along a wire embedding (definitions)
-- statement:
--   **State extension along a wire embedding.** Definitions only.
--
--   `ShiEmbed_Core` relabels circuit SYNTAX along an injection $e:\\mathrm{Fin}\\,m\\to\\mathrm{Fin}\\,n$ but says nothing semantic, because relating $\\mathrm{runLayered}(\\mathrm{embedCirc}\\,e\\,c)$ to $\\mathrm{runLayered}\\,c$ needs a map carrying an $m$-wire state to an $n$-wire state. This bundle supplies it: $\\mathrm{restrict}\\,e\\,y$ reads an $n$-wire basis string on the $m$ wires selected by $e$, and
--
--   $$\\mathrm{spread}\\,e\\,\\psi\\,(y)=\\begin{cases}\\psi(\\mathrm{restrict}\\,e\\,y) & \\text{if } y \\text{ vanishes off the image of } e,\\\\ 0 & \\text{otherwise.}\\end{cases}$$
--
--   For injective $e$ this is the amplitude array of $\\psi\\otimes|0\\dots0\\rangle$ written without a tensor-product API — the off-image vanishing condition encodes the tensor structure.
--
--   **Three qualifications that phrase hides.** It is that tensor only up to the wire PERMUTATION induced by $e$ (a literal $\\psi\\otimes|0\\dots0\\rangle$ puts $\\psi$ on wires $0\\dots m-1$; $\\mathrm{spread}$ puts it on $e\\,0\\dots e\\,(m-1)$). If $e$ is surjective — in particular whenever $m=n$ — no wire is off-image, the condition is vacuous, and there is no zero register at all. And for non-injective $e$ it is not the amplitude array of any $\\psi\\otimes|0\\dots0\\rangle$ whatsoever: $\\mathrm{restrict}\\,e\\,y$ is constant on the fibres of $e$, so $\\mathrm{spread}$ never reads components of $\\psi$ at strings differing within a fibre and those amplitudes are dropped — hence not injective and not norm-preserving. Downstream theorems must assume injectivity explicitly; the definition does not build it in.
--
--   **Nothing is proved here.** No round-trip law — and note such a law is not merely unproved but UNSTATEABLE with these definitions, since $\\mathrm{restrict}$ acts on basis strings while $\\mathrm{spread}\\,e\\,\\psi$ is an amplitude array and no pullback $\\mathcal{Q}(n)\\to\\mathcal{Q}(m)$ is defined. No linearity, injectivity or norm preservation. And not the semantic transport law $\\mathrm{runLayered}(\\mathrm{embedCirc}\\,e\\,c)(\\mathrm{spread}\\,e\\,\\psi)=\\mathrm{spread}\\,e\\,(\\mathrm{runLayered}\\,c\\,\\psi)$, which is the whole point of the construction and is submitted separately as a theorem.
--
--   The off-image wires are fixed to $|0\\rangle$, not left arbitrary and not traced out, so this models running a small circuit on a fresh zero-initialised register — the situation parallel composition and repetition need. It does not model an arbitrary environment, and nothing extends to mixed states.

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

State extension along a wire embedding -- DEFINITIONS ONLY.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiEmbed_Core

set_option autoImplicit false

/-!
# Extending a state along a wire embedding

`Def_ShiEmbed_Core` relabels circuit SYNTAX along an injection `e : Fin m → Fin n` but says
nothing about semantics, because relating `runLayered (embedCirc e he c)` to `runLayered c`
needs a map carrying an `m`-wire state to an `n`-wire state. This bundle supplies that map.

* `restrict e y` reads an `n`-wire basis string on the `m` wires selected by `e`.
* `spread e ψ` is the `n`-wire state equal to `ψ` on the image of `e` and `|0…0⟩` on every
  other wire: concretely, `spread e ψ y = ψ (restrict e y)` when `y` vanishes off the image of
  `e`, and `0` otherwise.

For INJECTIVE `e`, `spread e ψ` is the amplitude array of `ψ ⊗ |0…0⟩` written in the basis of
`n` wires, WITHOUT using a tensor-product API: the off-image vanishing condition encodes the
tensor structure. Three qualifications the phrase "`ψ ⊗ |0…0⟩`" hides:

* it is that tensor only up to the wire PERMUTATION induced by `e`. A literal `ψ ⊗ |0…0⟩` puts
  `ψ` on wires `0 … m-1`; `spread` puts it on `e 0 … e (m-1)`, so for non-monotone `e` it is a
  permuted tensor;
* if `e` is surjective (in particular whenever `m = n`), NO wire is off-image, the condition is
  vacuously true, `spread e ψ = ψ ∘ restrict e`, and there is no zero register at all -- the
  "`|0…0⟩` factor" is empty and the off-image condition degenerates to no condition;
* for non-injective `e` it is not the amplitude array of any `ψ ⊗ |0…0⟩` whatsoever (see the
  design notes).

## What is NOT here

DEFINITIONS ONLY, with one qualification: no `theorem` or `lemma` is declared, but
`instDecidableOffImage` is a proof-carrying declaration establishing decidability of `OffImage`
(resting on finiteness of `Fin m`), so the file is not literally free of proved content. It
exists only so the `if` in `spread` elaborates; since `spread` is `noncomputable` it buys no
executability. Nothing here proves

* any round-trip law. Note such a law is not merely unproved but UNSTATEABLE with these
  definitions: `restrict e : Bits n → Bits m` acts on basis STRINGS while `spread e ψ` is an
  amplitude ARRAY, and no pullback `QState n → QState m` is defined here, so there is nothing
  to compose `spread` with;
* that `spread` is linear, injective, or norm-preserving;
* the semantic transport law `runLayered (embedCirc e he c) (spread e ψ) = spread e (runLayered c ψ)`,
  which is the whole point of the construction and is submitted separately as a theorem;
* anything about `acceptProb` of an embedded circuit.

## Deliberate design choices, and their costs

* The off-image wires are fixed to `false` (i.e. `|0⟩`), not left arbitrary and not traced
  out. So `spread` models "run the small circuit on a fresh zero-initialised register",
  which is the situation parallel composition and repetition actually need. It does NOT model
  an arbitrary environment state, and nothing here extends to mixed states.
* The off-image condition is written `∀ i, e i ≠ k` rather than via `Finset.image`, to keep
  the definition free of `DecidableEq`/`Finset` machinery. It says exactly "`k` is not in the
  image of `e`".
* `spread` does not take the injectivity of `e` as an argument, and the definition is total
  for any `e`. But the failure for NON-injective `e` is worse than "not the intended
  construction", and it is located in `spread`, not in `restrict`: `restrict e y` discards the
  off-image coordinates of `y` for every `e`, injective or not, so that is not the issue.
  Rather, `restrict e y` is always constant on the fibres of `e`, so `spread e ψ` never reads
  the components of `ψ` at strings differing within a fibre -- those amplitudes are dropped
  outright. Hence for non-injective `e`, `spread` is not injective, is not norm-preserving, and
  `spread e ψ` is not the amplitude array of any `ψ ⊗ |0…0⟩`. Downstream theorems must assume
  injectivity explicitly.
* `Bits`, `QState` and the embedding maps are inherited from the imports, and nothing about
  THOSE is proved here (the decidability instance above concerns `e`, not them). That `Bits n`
  is `Fin n → Bool` and `QState m` is `Bits m → ℂ`, and hence the identification of `false`
  with `|0⟩` and the reason `spread` must be `noncomputable`, come from `Def_ShiShallow_Core`
  and are not established in this file.
-/

namespace ShiSpread

open ShiShallow

/-- Read an `n`-wire basis string on the `m` wires selected by `e`. -/
def restrict {m n : ℕ} (e : Fin m → Fin n) (y : Bits n) : Bits m := fun i => y (e i)

/-- `k` is not in the image of `e`, i.e. `k` is one of the wires the embedding does not use. -/
def OffImage {m n : ℕ} (e : Fin m → Fin n) (k : Fin n) : Prop := ∀ i : Fin m, e i ≠ k

instance instDecidableOffImage {m n : ℕ} (e : Fin m → Fin n) (k : Fin n) :
    Decidable (OffImage e k) := by
  unfold OffImage
  infer_instance

/-- Extend an `m`-wire state to `n` wires, placing `ψ` on the image of `e` and `|0…0⟩` on
every wire off the image. This is the amplitude array of `ψ ⊗ |0…0⟩` written without a
tensor-product API: the off-image vanishing condition IS the tensor structure. -/
noncomputable def spread {m n : ℕ} (e : Fin m → Fin n) (ψ : QState m) : QState n :=
  fun y => if (∀ k : Fin n, OffImage e k → y k = false) then ψ (restrict e y) else 0

end ShiSpread


