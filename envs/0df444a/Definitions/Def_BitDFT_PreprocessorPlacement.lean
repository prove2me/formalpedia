-- Prove2me | Definitions.Def_BitDFT_PreprocessorPlacement
-- name    : BitDFT_PreprocessorPlacement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T17:10:22.433667+00:00
-- url     : https://prove2.me/theorems/b0638beb-e2f2-40ba-9c6b-92e94395bd33
-- title:
--   Preprocessing with reserved fresh child-machine banks
-- statement:
--   Lift the five-tape request preprocessor into any target alphabet, append r fresh tapes, and apply the fixed routing permutation. The resulting machine has 5+r tapes, with native input and output unchanged, three preprocessor workspace tapes after the r reserved child banks, and an explicit embedding of every original configuration.
-- source:
--   Actual preprocessing machine layout for the arbitrary Fourier-machine call.

import Definitions.Def_BitDFT_PreprocessorAlphabet
import Definitions.Def_BitDFT_TapeExtension
import Definitions.Def_BitDFT_TapePermutation
import Definitions.Def_BitDFT_CallerRouting

noncomputable section
namespace BitDFT.PreprocessorPlacement
open IntMul

abbrev extended (N : MultitapeTM) (r : ℕ) :=
  TapeExtension.machine (PreprocessorAlphabet.machine N) r

def routing (N : MultitapeTM) (r : ℕ) : Fin (extended N r).k ≃ Fin (extended N r).k :=
  CallerRouting.permutation r

theorem routing_input (N : MultitapeTM) (r : ℕ) :
    routing N r (extended N r).inTape = (extended N r).inTape :=
  CallerRouting.native_zero r

abbrev machine (N : MultitapeTM) (r : ℕ) :=
  TapePermutation.machine (extended N r) (routing N r) (routing_input N r)

def embed (N : MultitapeTM) (r : ℕ) (c : RewriteInput.machine.Cfg) : (machine N r).Cfg :=
  TapePermutation.embed (extended N r) (routing N r) (routing_input N r)
    (TapeExtension.embed (PreprocessorAlphabet.machine N) r
      (fun _ => N.tapeOf []) (fun _ => 0)
      (AlphabetEmbedding.embed (PreprocessorAlphabet.alphabetMap N) c))

end BitDFT.PreprocessorPlacement


