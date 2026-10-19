-- Prove2me | Definitions.Def_QAlgorithms_ClassicalStringListEncoding
-- name    : QAlgorithms_ClassicalStringListEncoding
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:29:46.915346+00:00
-- url     : https://prove2.me/theorems/9995f149-b90b-46c2-812b-b0239f3021e3
-- title:
--   Unary count prefix for a list of binary strings
-- statement:
--   For a list of binary strings, prefix their ordered concatenation with the unary encoding of the number of strings. That prefix consists of one true bit per string followed by one false bit. The encoding of the empty list is a single false bit. This is the unchanged reviewed Complexity.encStr routine used by public program serializers.
-- source:
--   Reviewed shared encoding convention, QAlgorithms.Complexity.encStr; used in the public program serialization interfaces for arXiv:2607.16541 and arXiv:2610.02145.

import Definitions.Def_QAlgorithms_ClassicalStringComputability

namespace QAlgorithms.Complexity

/-- Copied from `ShiBQP.encStr`: a list of binary strings, length-prefixed and concatenated. -/
def encStr (ls : List Str) : Str := encNat ls.length ++ ls.flatten

end QAlgorithms.Complexity


