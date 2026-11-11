-- Prove2me | Definitions.Def_GaussDiffSVP_isoTreeLaw
-- name    : GaussDiffSVP_isoTreeLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:02:08.976216+00:00
-- url     : https://prove2.me/theorems/06440122-903e-4136-8fee-a41e4814467e
-- title:
--   Balanced isolated tree of depth $t$
-- statement:
--   The law of the list produced by a node of a balanced isolated tree of depth $t$, leaves at level $t$ and root at level $0$. A leaf at offset $p$ has a given law. A node at level $j<t$ and offset $p$ draws a local shift $d$ from a law $\omega_j(p)$, builds its two children (level $j+1$) independently at offsets $f_L(p,d)$ and $f_R(p,d)$, and performs an isolated merge with the coin kernel of the children's level. The root law is the node of height $t$.
--
--   **Formalization Note** Defined by recursion on the height; levels are numbered from the root as in the paper.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Corollary 4.6, p.26; §4.2, pp.23–24; Algorithm 1, p.29

import Mathlib
import Definitions.Def_GaussDiffSVP_isoMergeLaw

namespace GaussDiffSVP

/-- The balanced isolated tree of depth `t` (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Corollary 4.6, p.26; §4.2, pp.23–24; Algorithm 1,
p.29), with leaves at level `t` and root at level `0`. `isoTreeLaw t … k p` is the law of the
list produced by a node of **height** `k` (level `t − k`) with prescribed offset `p`:

* height `0` (a leaf): the leaf law `leaf p`;
* height `k + 1` (level `j = t − (k + 1)`): draw the local shift `d ∼ ω j p`; build the two
  children (level `j + 1`) independently at offsets `fL p d` and `fR p d`; merge them with pair
  map `T` and the coin kernel `κ (j + 1) p d` of the children's level, keeping isolated edges.

The root list is `isoTreeLaw t … t p`.

**Formalization Note.** Levels are numbered from the root as in the paper ("Number levels from the
root, with leaves at level t", p.29); the kernel used to merge children at level `j` is indexed by
`j` (`c_j` "when its children are at level j", p.28) and the shift law by the parent's level. The
law is conditional on the prescribed offset (and the fixed public parameters). -/
noncomputable def isoTreeLaw {α O D : Type*} (t : ℕ) (T : α → α → α) (ω : ℕ → O → PMF D)
    (fL fR : O → D → O)
    (κ : ℕ → O → D → (lL : List α) → (lR : List α) → PMF (Fin lL.length × Fin lR.length → Bool))
    (leaf : O → PMF (List α)) : ℕ → O → PMF (List α)
  | 0 => leaf
  | k + 1 => fun p => (ω (t - (k + 1)) p).bind fun d =>
      isoMergeLaw (isoTreeLaw t T ω fL fR κ leaf k (fL p d))
        (isoTreeLaw t T ω fL fR κ leaf k (fR p d)) T (κ (t - k) p d)

end GaussDiffSVP


