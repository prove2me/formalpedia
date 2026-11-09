-- Prove2me | Definitions.Def_IntADSat_TopSep
-- name    : IntADSat_TopSep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:52:51.29656+00:00
-- url     : https://prove2.me/theorems/2097ec28-d40e-49cb-a2b5-f0e8362a042b
-- title:
--   Seed event: the $r+1$ largest degrees are separated by more than $g$
-- statement:
--   The seed event of Lemma B.6: the $r+1$ largest degrees of $G$ are pairwise separated by more than $g$, i.e. there is a listing of $r+1$ distinct vertices witnessing it (see `IsTopSepListing`).
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.6, p.17 (PDF 18)

import Mathlib
import Definitions.Def_IntADSat_IsTopSepListing

set_option autoImplicit false

namespace IntADSat

/-- The seed event of Lemma B.6 (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.17 (PDF 18)): the `r + 1` largest degrees of `G` are
pairwise separated by more than `g`, i.e. some listing `σ` satisfies `IsTopSepListing`. -/
def TopSep {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ σ : Fin (rP n + 1) ↪ Fin n, IsTopSepListing G σ

end IntADSat


