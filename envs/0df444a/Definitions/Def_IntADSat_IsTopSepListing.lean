-- Prove2me | Definitions.Def_IntADSat_IsTopSepListing
-- name    : IntADSat_IsTopSepListing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:28.73653+00:00
-- url     : https://prove2.me/theorems/3d747116-b87a-47ca-b867-b753a4307411
-- title:
--   Listing of the $r+1$ largest degrees, pairwise separated by more than $g$
-- statement:
--   Let $r,g$ be the parameters of display (B.1) at $n$. A listing $\sigma(0),\dots,\sigma(r)$ of $r+1$ distinct vertices of $G$ **witnesses that the $r+1$ largest degrees are pairwise separated by more than $g$** if
--
--   1. $\deg_G\sigma(j)+g<\deg_G\sigma(i)$ whenever $i<j$, and
--   2. every vertex outside the listing has degree at most $\deg_G\sigma(r)$.
--
--   Equivalently, with the degrees sorted as $d_{(1)}\ge d_{(2)}\ge\cdots$, one has $d_{(i)}-d_{(i+1)}>g$ for $1\le i\le r$; the listed vertices are those of the $r+1$ largest degrees, in decreasing order.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.6, p.17 (PDF 18)

import Mathlib
import Definitions.Def_IntADSat_deg
import Definitions.Def_IntADSat_rP
import Definitions.Def_IntADSat_gP

set_option autoImplicit false

namespace IntADSat

/-- A listing `σ(0), …, σ(r)` of `r + 1` distinct vertices witnessing that "the `r + 1` largest degrees
are pairwise separated by more than `g`" (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.6, p.17 (PDF 18)): the degrees of the listed
vertices decrease with consecutive (hence all pairwise) gaps larger than `g`, and every unlisted vertex
has degree at most that of `σ(r)`. Here `r`, `g` are the parameters of display (B.1) at `n`.

**Formalization Note** Equivalent to the sorted-degree form `d_(i) − d_(i+1) > g` for `1 ≤ i ≤ r`. -/
def IsTopSepListing {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Fin (rP n + 1) ↪ Fin n) : Prop :=
  (∀ i j : Fin (rP n + 1), i < j → deg G (σ j) + gP n < deg G (σ i)) ∧
    ∀ v : Fin n, v ∉ Set.range σ → deg G v ≤ deg G (σ (Fin.last (rP n)))

end IntADSat


