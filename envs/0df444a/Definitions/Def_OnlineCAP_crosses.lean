-- Prove2me | Definitions.Def_OnlineCAP_crosses
-- name    : OnlineCAP_crosses
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:33.340394+00:00
-- url     : https://prove2.me/theorems/ed9cb721-3b64-48ae-88a9-0f6e49d70f80
-- title:
--   A pair crosses a vertex set
-- statement:
--   An unordered pair $\ell=\{u,v\}$ of vertices **crosses** a vertex set $C$ when exactly one of its ends lies in $C$.
--
--   For edges this defines the edge cut $\delta_E(C)$, for links the set $\delta_L(C)$ of links covering the cut $C$ (§2). A loop $\{v,v\}$ crosses no set.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §2, p.9

import Mathlib

namespace OnlineCAP

/-- **A pair crosses a vertex set.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §2, p.9 (PDF p.9): "For a subset of vertices C ⊆ V, we
denote by δE(C) the set of edges in E with exactly one endpoint in C, and by δL(C) the set of
candidate links in L with exactly one endpoint in C. … A link ℓ ∈ L is said to cover or cross a cut
C if ℓ ∈ δL(C)."

The unordered pair `ℓ = {u, v}` crosses `C` when exactly one of its ends lies in `C`: some end is
in `C` and some end is not.

**Formalization Note.** Used both for edges of the base graph and for links. A loop `{v, v}`
crosses no set. -/
def crosses {V : Type} (ℓ : Sym2 V) (C : Finset V) : Prop :=
  (∃ v ∈ ℓ, v ∈ C) ∧ ∃ v ∈ ℓ, v ∉ C

end OnlineCAP


