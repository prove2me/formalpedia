-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_P21RunStmt
-- name    : LinearSetReconciliation327_Main_P21RunStmt
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-21T09:36:15.819873+00:00
-- url     : https://prove2.me/theorems/02b893b9-f286-4ccc-843d-2f0a6197c59d
-- title:
--   Run-at-base layer for Proposition 2.1's decoder
-- statement:
--   **The run-at-base layer of Proposition 2.1's decoder.**
--
--   Proposition 2.1's decoder reads its payload from the *absolute* words $[0, L)$ with
--   $L = \lceil tw/8w\rceil$ and keeps its whole workspace at the fixed, `det`-derived addresses
--   $[0, \mathrm{decoderAllocEnd}(t))$. It therefore cannot be relocated: only its **payload** can be
--   moved. This definition is exactly that layer.
--
--   `pinsketchRunStmt t w β` is a straight-line statement that
--
--   1. copies the payload words $[\beta, \beta+L)$ down to $[0, L)$, where $L = \lceil tw/8w\rceil$ is
--      the number of words of a $t\times w$ syndrome;
--   2. erases the source block by copying the (zero) shadow block $[\beta+L, \beta+2L)$ over it, so the
--      caller's memory is left zero outside $[0, L)$;
--   3. clears all sixteen registers and loads $r_1 := L$, the decoder's canonical entry state;
--   4. runs the decoder core `positiveDecoderStmt` verbatim.
--
--   Its step count is
--
--   $$
--   \mathrm{layerCost}(t,w) \;=\; \mathrm{positiveDecoderBudget}(t,w) + 24\left\lceil \tfrac{t}{8}\right\rceil + 39 ,
--   $$
--
--   i.e. the decoder's own polynomial budget plus an overhead that is **linear** in the row weight $t$.
--
--   This is the vocabulary a block dispatcher needs when it runs many decoders back to back in one
--   memory: each invocation stages its payload at its own word base $\beta$ and reads the answer back
--   from the standard workspace. The companion theorem `pinsketch_decoding_at` gives the contract.
--
--   **Formalization Note** `layerCost` is stated with the exact `wordsOf (8w) (tw)` word count rather
--   than $\lceil t/8\rceil$ so that it is definitionally the step count the run actually pays;
--   `layerCopyRegs`/`layerDecoderRegs` are the register preambles of the two copy passes and of the
--   decoder entry state, and `runAtStmt` is the generic driver for an arbitrary decoder core.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), §2.2 (pinsketch syndromes and the decoder) and §2.1 (word-RAM model), Proposition 2.1 (decoding conjunct); extracted from the verified development `Solutions/Sol_p21_copyrun.lean`.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_DecoderProgram
/-! Run-layer vocabulary for Proposition 2.1's decoder: the `Stmt` that stages the payload of `y`
at an arbitrary word base `β`, copies it down to `0`, erases the source block, resets the registers
to the decoder's canonical entry state and then runs the decoder core `positiveDecoderStmt`
verbatim.

Extracted (byte-identically) from `Solutions/Sol_p21_copyrun.lean`, which carries the proofs.  Only
the definitions live here; every theorem about them is published separately, so that the statement
of `pinsketch_decoding_at` -- which names `pinsketchRunStmt` -- is expressible against platform
modules alone.

* `layerCopyRegs dst src L` -- the straight-line register preamble of one copy pass;
* `layerDecoderRegs L` -- the decoder's canonical entry registers, everything zero except `r1 = L`;
* `runAtStmt β L A` -- copy `[β, β+L)` to `[0, L)`, erase the source with the zero shadow block
  `[β+L, β+2L)`, zero the registers, load `r1 := L`, run `A`;
* `pinsketchRunStmt t w β` -- `runAtStmt` at the payload length `L = wordsOf (8w) (tw)`, wrapping
  `positiveDecoderStmt`;
* `layerCost t w` -- the layer's own step count, `positiveDecoderBudget t w + 24·L + 39` (see
  `layer_overhead_bound` in the solution file).
-/

set_option autoImplicit false

noncomputable section

namespace LinearSetReconciliation327.Main

/-- Straight-line register preamble for one `copyStmt` pass: counter `0` in `r0`, length in `r1`,
destination in `r2`, source in `r3`, step `1` in `r4`, and the scratch registers zeroed. -/
def layerCopyRegs (dst src L : ℕ) : List Instr :=
  [iImm r0 0, iImm r1 L, iImm r2 dst, iImm r3 src, iImm r4 1,
    iImm r10 0, iImm r12 0, iImm r13 0, iImm r15 0]

/-- The canonical entry registers of the decoder: everything zero except `r1 = L`. -/
def layerDecoderRegs (L : ℕ) : Fin 16 → ℕ := fun d => if d = r1 then L else 0

/-- Copy the payload block `[β, β+L)` to `[0, L)`, erase the source with the zero shadow block
`[β+L, β+2L)`, reset the registers to the canonical entry state, and run `Sdec`. -/
def runAtStmt (β L : ℕ) (Sdec : Stmt) : Stmt :=
  .seq (.code (layerCopyRegs 0 β L))
    (.seq copyStmt
      (.seq (.code (layerCopyRegs β (β + L) L))
        (.seq copyStmt
          (.seq (.code zeroRegsCode)
            (.seq (.code [iImm r1 L]) Sdec)))))

/-- The glued statement for Proposition 2.1: the payload is staged at `β` inside the decoder's own
scratch, is moved to `0`, the source is erased, and the decoder core runs verbatim. -/
def pinsketchRunStmt (t w β : ℕ) : Stmt :=
  runAtStmt β (wordsOf (8 * w) (t * w)) positiveDecoderStmt

/-- Total cost of the glued statement: the decoder budget plus the two copies and the preambles. -/
def layerCost (t w : ℕ) : ℕ :=
  9 + (12 * wordsOf (8 * w) (t * w) + 2 +
    (9 + (12 * wordsOf (8 * w) (t * w) + 2 + (16 + (1 + positiveDecoderBudget t w)))))

end LinearSetReconciliation327.Main


