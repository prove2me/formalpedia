-- Prove2me | Definitions.Def_HypRecov_encInit
-- name    : HypRecov_encInit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:37:01.149989+00:00
-- url     : https://prove2.me/theorems/2f78ea3f-b1a2-4446-83c7-dfbb6f50763a
-- title:
--   Inputs of the initializer, update, subtraction and decoding machines
-- statement:
--   The four machines of a linear sketch receive:
--
--   1. the **initializer**: the parameters $n,r,k,m$ and the list of coin values $\omega$;
--   2. the **update** machine: the parameters, the current state $s$, a fragment $A$ and an increment $\Delta$;
--   3. the **subtraction** machine: the parameters and two states $s,s'$;
--   4. the **decoder**: the parameters and one state $s$.
--
--   Here $m=\lceil 1/\eta\rceil$ stands for the failure budget $\eta$. Only the initializer reads the coins: the randomness the later machines need has to be carried in the state.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem 1.1, p.2 (PDF p.3); Algorithm 2, p.21 (PDF p.22)

import Mathlib
import Definitions.Def_HypRecov_encNat

namespace HypRecov

/-- **Inputs of the four machines of a linear sketch.** Zhang, Chen, Shen, *Hypergraph Recovery from
Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Theorem 1.1, p.2
(PDF p.3): "Preprocessing, per-fragment update and decoding"; Algorithm 2, p.21 and Theorem 9.1,
p.22 for the subtraction of two states.

`encInit n r k m ω`: the parameters and the coin values `ω` (a list of naturals). Only the
initializer reads coins.

**Formalization Note.** Every input carries the parameters `n, r, k, m` in binary, so one machine
serves all parameters; `m = ⌈1/η⌉₊` stands for the failure budget `η`. A state `s` is a bit string,
written with `encBits`. -/
def encInit (n r k m : ℕ) (ω : List ℕ) : List Bool :=
  encParams n r k m ++ (ω.flatMap (fun x => true :: encNat x) ++ [false])

/-- Input of the update machine: the parameters, the current state `s`, the fragment `A` and the
increment `Δ`. -/
def encUpd {n : ℕ} (r k m : ℕ) (s : List Bool) (A : Finset (Fin n)) (Δ : ℤ) : List Bool :=
  encParams n r k m ++ encBits s ++ encSet A ++ encInt Δ

/-- Input of the subtraction machine: the parameters and two states. -/
def encSub (n r k m : ℕ) (s s' : List Bool) : List Bool :=
  encParams n r k m ++ encBits s ++ encBits s'

/-- Input of the decoder: the parameters and one state. -/
def encDec (n r k m : ℕ) (s : List Bool) : List Bool :=
  encParams n r k m ++ encBits s

/-- The coin values as a list of naturals. -/
def coinList {N M : ℕ} (ω : Fin N → Fin M) : List ℕ := List.ofFn (fun i => (ω i).val)

end HypRecov


