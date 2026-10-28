-- Prove2me | Definitions.Def_BitDFT_RoutedCountedBlockFreshTapes
-- name    : BitDFT_RoutedCountedBlockFreshTapes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T06:33:23.251093+00:00
-- url     : https://prove2.me/theorems/87e019e1-9375-45a7-8cc9-9994086c97a2
-- title:
--   Run the counted serializer on fresh multiplier tapes
-- statement:
--   Given a tracked multiplier alphabet, extend its post-call tape bank with three tapes and run the counted-block serializer there. The product source remains on tape 1; output, countdown, and template are routed to the appended tapes. The cyclic tape permutation carries every pre-existing caller and multiplier work-tape record into unused extension slots, so the serializer can preserve the full returned frame.
-- source:
--   This finite controller composes the arbitrary-alphabet counted-block host with tape extension and the proved fresh-tape permutation. Its embedding gives the serializer the product frame and preserves caller data on all other original tapes.

import Definitions.Def_BitDFT_SerializerFreshTapeRouting
import Definitions.Def_BitDFT_CountedBlockOnMultiplierAlphabet
import Definitions.Def_IntMul_TrackedOutputShift

set_option autoImplicit false
noncomputable section
open IntMul

namespace BitDFT.RoutedCountedBlockFreshTapes

abbrev source (M : MultitapeTM) := TrackedOutputShift.machine M
abbrev host (M : MultitapeTM) := CountedBlockOnMultiplierAlphabet.machine (source M)
abbrev extension (M : MultitapeTM) :=
  TapeExtension.machine (host M) ((source M).k - 2)

/-- Serializer execution on the multiplier's alphabet, with the product source
    left on tape 1 and its output, countdown, and template moved to the three
    appended tapes. The rotation also parks the old middle tapes in the unused
    extension slots, preserving the entire prior caller and bank layout. -/
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM := by
  let r := (source M).k - 2
  let E := TapeExtension.machine (host M) r
  have hroute : SerializerFreshTapeRouting.routing r E.inTape = E.inTape := by
    change SerializerFreshTapeRouting.routing r ⟨0, by omega⟩ = ⟨0, by omega⟩
    exact SerializerFreshTapeRouting.routing_input r
  exact TapePermutation.machine E (SerializerFreshTapeRouting.routing r) hroute

def embed (M : MultitapeTM) (base : (host M).Cfg)
    (extraCells : Fin (extension M).k → ℕ → (source M).Sym)
    (extraHeads : Fin (extension M).k → ℕ)
    (c : (CountedBlockOnMultiplierAlphabet.storage (source M)).Cfg) : (machine M).Cfg := by
  let r := (source M).k - 2
  let E := TapeExtension.machine (host M) r
  let hroute : SerializerFreshTapeRouting.routing r E.inTape = E.inTape := by
    change SerializerFreshTapeRouting.routing r ⟨0, by omega⟩ = ⟨0, by omega⟩
    exact SerializerFreshTapeRouting.routing_input r
  exact TapePermutation.embed E (SerializerFreshTapeRouting.routing r) hroute
    (TapeExtension.embed (host M) r extraCells extraHeads
      (CountedBlockOnMultiplierAlphabet.embed (source M) base c))

end BitDFT.RoutedCountedBlockFreshTapes
end


