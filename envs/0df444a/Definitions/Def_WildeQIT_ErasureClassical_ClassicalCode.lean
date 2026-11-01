-- Prove2me | Definitions.Def_WildeQIT_ErasureClassical_ClassicalCode
-- name    : WildeQIT_ErasureClassical_ClassicalCode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:57.544241+00:00
-- url     : https://prove2.me/theorems/705c41bf-7a6f-4d01-b155-5a44829c8192
-- title:
--   Code for classical communication over $n$ uses of a quantum channel
-- statement:
--   Let $A'$ and $B$ be the input and output systems of a quantum channel, $n\in\mathbb N$ a number of channel uses, and $\{1,\dots,|\mathcal M|\}$ a set of messages. A **code for classical communication** consists of
--
--   1. for every message $m$, an encoding state $\rho^m_{A'^n}$ (a density operator on the $n$ input systems, possibly entangled across them), and
--   2. a decoding POVM $\{\Lambda_m\}$ on the $n$ output systems $B^n$: positive semidefinite operators with $\sum_m\Lambda_m=I$.
--
--   Alice sends $\rho^m_{A'^n}$ through $n$ independent uses of the channel, and Bob measures the output with $\{\Lambda_m\}$ to estimate the message. This is the most general protocol for classical communication over a quantum channel (Figure 20.3).
--
--   **Formalization Note** Messages are `Fin M`; the $n$-fold input and output systems are indexed by `Fin n → a` and `Fin n → b`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §20.2.1, pp. 561–562, Figure 20.3

import Definitions.Def_WildeQIT_IsDensityOperator
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §20.2.1, pp. 561–562
(a code for classical communication over `n` uses of a quantum channel, Figure 20.3).
-/

open scoped ComplexOrder

namespace WildeQIT.ErasureClassical

/-- **Code for classical communication over `n` channel uses** (Wilde, *From Classical to
Quantum Shannon Theory*, arXiv:1106.1445v8, §20.2.1, pp. 561–562): Alice "selects from a set of
messages `{1, …, |M|}`" and "prepares some state `ρᵐ_{A′ⁿ}` as input to the many independent
uses of the channel — the input systems are `n` copies of the channel input system `A′`"; "Bob
has some decoding POVM `{Λ_m}`" on the `n` channel outputs `Bⁿ`.

**Formalization Note.** Messages are `Fin M`. The `n`-fold input `A′ⁿ` is indexed by
`Fin n → a` and the `n`-fold output `Bⁿ` by `Fin n → b`. The encoding states `ρᵐ` are arbitrary
density operators on `A′ⁿ`, so they may be entangled across channel uses, as in the book. The
decoder is a POVM: positive semidefinite operators summing to the identity. -/
structure ClassicalCode (a b : Type) [Fintype a] [Fintype b] [DecidableEq b] (n M : ℕ) where
  /-- The encoding states `ρᵐ_{A′ⁿ}`. -/
  enc : Fin M → Matrix (Fin n → a) (Fin n → a) ℂ
  /-- Each encoding state is a density operator. -/
  enc_density : ∀ m, IsDensityOperator (enc m)
  /-- The decoding POVM `{Λ_m}` on `Bⁿ`. -/
  dec : Fin M → Matrix (Fin n → b) (Fin n → b) ℂ
  /-- Each POVM element is positive semidefinite. -/
  dec_psd : ∀ m, (dec m).PosSemidef
  /-- The POVM elements sum to the identity. -/
  dec_sum : ∑ m, dec m = 1

end WildeQIT.ErasureClassical


