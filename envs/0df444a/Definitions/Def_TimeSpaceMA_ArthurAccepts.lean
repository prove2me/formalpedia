-- Prove2me | Definitions.Def_TimeSpaceMA_ArthurAccepts
-- name    : TimeSpaceMA_ArthurAccepts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:56:59.443702+00:00
-- url     : https://prove2.me/theorems/0b5063fb-3c45-46d7-b91a-ffadb98de3e3
-- title:
--   Coin tape, input layouts, and Arthur's acceptance
-- statement:
--   The **coin tape** is the product of fair coins on $\{0,1\}^{\mathbb N}$.
--
--   Arthur starts on $(x,\pi)$ with $M[0]=|x|$, $M[1]=|\pi|$, $M[2+i]=x_i$, $M[2+|x|+i]=\pi_i$ and zero elsewhere. He **accepts** on a tape $\tau$ if he halts with $M[0]=1$; a run that does not halt does not accept.
--
--   Merlin starts on $x$ with $M[0]=|x|$, $M[1+i]=x_i$ and zero elsewhere. His output, read from his final memory, has length $M[0]$ and bits $\pi_i = (M[1+i]\neq 0)$.
--
--   These are the objects of Definition 2.1, the Merlin–Arthur protocol, as finite programs.
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Definition 2.1, pp.5–6

import Definitions.Def_TimeSpaceMA_RAM

open MeasureTheory

namespace TimeSpaceMA

/-- Fair coin tape: the product of uniform measures on `Bool` over `ℕ`. Arthur's coins are read from
it in order by the `coin` instruction. -/
noncomputable def coinTape : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure

/-- Arthur's start memory on `(x, π)`: `M[0] = n`, `M[1] = |π|`, `M[2+i] = x_i`, `M[2+n+i] = π_i`,
zero elsewhere. -/
def arthurMem (x π : List Bool) : ℕ → ℕ :=
  memOf ([x.length, π.length] ++ x.map Bool.toNat ++ π.map Bool.toNat)

/-- Merlin's start memory on `x`: `M[0] = n`, `M[1+i] = x_i`, zero elsewhere. -/
def merlinMem (x : List Bool) : ℕ → ℕ :=
  memOf (x.length :: x.map Bool.toNat)

/-- Merlin's output, read off his final memory: `|π| = M[0]` and `π_i = (M[1+i] ≠ 0)`. -/
def merlinOutput (mem : ℕ → ℕ) : List Bool :=
  (List.range (mem 0)).map fun i => mem (1 + i) != 0

/-- Arthur accepts `(x, π)` on tape `τ` (Williams, Xi, STOC 2027 submission, manuscript sha256
184c2f95…, Definition 2.1, pp.5–6): he halts with `M[0] = 1`. A run that does not halt, or halts with
another value, does not accept. -/
def ArthurAccepts (Arthur : Program) (x π : List Bool) (τ : ℕ → Bool) : Prop :=
  ∃ st, Arthur.RunsTo τ (arthurMem x π) st ∧ st.mem 0 = 1

end TimeSpaceMA


