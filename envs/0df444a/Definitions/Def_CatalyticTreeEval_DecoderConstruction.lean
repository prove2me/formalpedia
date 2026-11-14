-- Prove2me | Definitions.Def_CatalyticTreeEval_DecoderConstruction
-- name    : CatalyticTreeEval_DecoderConstruction
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T01:31:09.136399+00:00
-- url     : https://prove2.me/theorems/7eda949d-caf2-44ee-9a56-105267e29bd9
-- title:
--   Three-term local kernels for canonical decoders
-- statement:
--   The three local kernels take integer values and detect the residues minus two, minus one, zero and one. Their shifts are zero, one and two. They provide the per-prime building blocks of the canonical-sumset decoder, with cancellation established before reducing modulo the composite modulus.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Lemma 3.19 and Section 4.2.

import Definitions.Def_CatalyticTreeEval_Main_Decoder

set_option autoImplicit false

namespace CatalyticTreeEval.DecoderConstruction

/-- The three integer-valued local kernels in Henzinger--Pyne--Ragavan,
Lemma 3.19, equation (6)/(7). Integer values allow cancellation before reducing
modulo the product of the primes. -/
noncomputable def localTerm {R : Type} [Ring R] (c : Fin 3) (z : R) : ℤ := by
  classical
  exact match c.val with
  | 0 => -(if z = -2 then 1 else 0)
  | 1 => (if z = 0 then 1 else 0) + (if z = -1 then 1 else 0)
  | _ => -(if z = 1 then 1 else 0)

/-- Three shifts 0, 1, 2, with local kernel values reduced modulo the modulus. -/
noncomputable def primeDecoder (p : ℕ) : Main.Decoder p 3 where
  shift c := (c.val : ZMod p)
  term c z := (localTerm c z : ZMod p)

end CatalyticTreeEval.DecoderConstruction


