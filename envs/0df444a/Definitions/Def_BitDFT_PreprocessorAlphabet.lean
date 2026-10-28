-- Prove2me | Definitions.Def_BitDFT_PreprocessorAlphabet
-- name    : BitDFT_PreprocessorAlphabet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T16:48:58.947032+00:00
-- url     : https://prove2.me/theorems/7c7ed316-d7ab-4b24-9260-a574796fe366
-- title:
--   The request preprocessor over any target machine alphabet
-- statement:
--   The five symbols used by the request preprocessor map injectively to a target machine’s blank, marker, zero, one, and separator. Applying the exact-clock alphabet adapter produces the same five-tape preprocessing algorithm over the target alphabet, with unchanged state set and runtime.
-- source:
--   Concrete alphabet map from the proved request preprocessor to the alphabet of an arbitrary Fourier-machine caller.

import Definitions.Def_BitDFT_RewriteInput
import Definitions.Def_BitDFT_AlphabetEmbedding

noncomputable section
namespace BitDFT.PreprocessorAlphabet
open IntMul

def encode (N : MultitapeTM) : TapeCopy.Sym → N.Sym
  | .blank => N.blank
  | .start => N.startSym
  | .zero => N.zero
  | .one => N.one
  | .sep => N.sep

def alphabetMap (N : MultitapeTM) : AlphabetEmbedding.Map RewriteInput.machine N where
  encode :=
    { toFun := encode N
      inj' := by
        intro a b hab
        have hd := N.syms_distinct
        simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,not_or] at hd
        cases a <;> cases b <;> simp_all [encode] }
  blank := rfl
  marker := rfl
  zero := rfl
  one := rfl
  sep := rfl

abbrev machine (N : MultitapeTM) := AlphabetEmbedding.machine (alphabetMap N)

end BitDFT.PreprocessorAlphabet


