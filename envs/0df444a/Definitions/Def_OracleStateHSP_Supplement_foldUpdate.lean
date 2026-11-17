-- Prove2me | Definitions.Def_OracleStateHSP_Supplement_foldUpdate
-- name    : OracleStateHSP_Supplement_foldUpdate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:09:38.423138+00:00
-- url     : https://prove2.me/theorems/dc7e6486-c970-48b0-adfa-3ecc60140868
-- title:
--   The data structure $S^\perp$ built by UPDATE in Algorithm 1
-- statement:
--   In Algorithm 1 the data structure $S^\perp$ starts empty, and each non-END output $s^\perp$ of the sampler is processed by $S^\perp \leftarrow \mathrm{UPDATE}(S^\perp, s^\perp)$; END outputs leave it unchanged. This definition computes the final $S^\perp$ from the list of sampler outputs and a given UPDATE routine. UPDATE is called exactly once per non-END output.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Algorithm 1, p.21

import Mathlib

namespace OracleStateHSP

namespace Supplement

/-- The data structure `S⊥` that Algorithm 1 (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, p.21) holds after the history `hist` of
HSP-SAMPLER outputs: starting from `S⊥ = ∅`, each non-END output `s⊥` is processed by
`S⊥ ← UPDATE(S⊥, s⊥)`, and END outputs leave `S⊥` unchanged.

**Formalization Note.** `UPDATE` is called exactly once per non-END output. -/
def foldUpdate {Gh : Type*} (upd : Finset Gh → Gh → Finset Gh) (hist : List (Option Gh)) :
    Finset Gh :=
  hist.foldl (fun S o => match o with
    | none => S
    | some s => upd S s) ∅

end Supplement

end OracleStateHSP


