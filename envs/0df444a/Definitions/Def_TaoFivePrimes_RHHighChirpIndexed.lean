-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighChirpIndexed
-- name    : TaoFivePrimes_RHHighChirpIndexed
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T01:54:22.785903+00:00
-- url     : https://prove2.me/theorems/3494b1b3-a616-426d-bcc4-173a7172f822
-- title:
--   TaoFivePrimes_RHHighChirpIndexed
-- statement:
--   A kernel-checked certificate that the indexed chirp tree flattens to the exact previously published records; valid node sizes and lookup equality are proved. Data modules are split to respect the scanner budget.
-- source:
--   Ordinary indexed representation of the accepted Platt/Bluestein chirp data. Original mathematical attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham; Platt DOI10.1090/mcom/3198.

import Definitions.Def_TaoFivePrimes_RHHighChirpIndexedRight
set_option maxRecDepth 1000000
namespace RHHighChirpIndexed
noncomputable def tree : RHHighIndexedDataTree.Tree RHHighChirpCache.Record := RHHighIndexedDataTree.Tree.node 8192 left right
structure Certificate where
  data : RHHighIndexedDataTree.Tree RHHighChirpCache.Record
  valid : RHHighIndexedDataTree.valid data=true
  original : RHHighIndexedDataTree.flatten data=RHHighChirpCache.expected
noncomputable def certificate : Certificate := ⟨tree,by decide +kernel,by rfl⟩
noncomputable def lookup (j : Nat) : RHHighChirpCache.Record :=
  RHHighIndexedDataTree.get ⟨0,0,0,0⟩ certificate.data j
lemma lookup_eq (j : Nat) : lookup j=(RHHighChirpCache.expected[j]?).getD ⟨0,0,0,0⟩ := by
  unfold lookup
  rw [RHHighIndexedDataTree.get_sound _ _ certificate.valid,certificate.original]
end RHHighChirpIndexed
noncomputable def TaoFivePrimes_RHHighChirpIndexed : Nat := 16385


