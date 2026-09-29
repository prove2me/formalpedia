-- Prove2me | Definitions.Def_HypercubeLineVIST_patentParent
-- name    : HypercubeLineVIST_patentParent
-- status  : Definition
-- author  : @undercat
-- created : 2026-09-27T15:34:47.688795+00:00
-- url     : https://prove2.me/theorems/666060ee-4f77-4731-a686-0f524afd1a53
-- title:
--   Patent-based parent function for L(Q_n) VISTs (Sym2)
-- statement:
--   Parent function on Sym2 for the 2n-2 rooted vertex-independent spanning trees in the line graph of the hypercube.

import Definitions.Def_HypercubeLineVIST_sym2parent

open Classical

namespace HypercubeLineVISTSym2

/-! ## Patent-based parent function on Sym2 (public types only)

We define a parent function for each of the 2n-2 trees, indexed by `TreeIdx n`.
Tree `k` corresponds to `(d, s)`. The routing moves towards the target
endpoint by flipping a differing coordinate.
-/

/-- Target endpoint representative for tree `k`, given root representatives `(a, b)`.
    Returns `a` if s=0, `b` if s=1. -/
def patentTgtRep (n : Nat) (a b : Fin n → Bool)
    (k : TreeIdx n) : Fin n → Bool :=
  if treeEndpoint n k then b else a

/-- Via edge (as Sym2) for tree `k`, given root `(a,b)` and root dimension `d0`.
    `via = {tgt, flipAt tgt d}` where `d = dimExcept d0 (treeDimIdx k)`. -/
def patentViaSym2 (n : Nat) (hn : 2 ≤ n) (a b : Fin n → Bool) (d0 : Fin n)
    (k : TreeIdx n) : Sym2 (Fin n → Bool) :=
  let tgt := patentTgtRep n a b k
  let dim := dimExcept n d0 (treeDimIdx n hn k)
  Sym2.mk tgt (flipAt n tgt dim)

/-- One step: from `v` (with rep `(z, w)`), go to `{z, flipAt z c}`. -/
noncomputable def patentStepSym2 (n : Nat) (v : Sym2 (Fin n → Bool)) (c : Fin n) :
    Sym2 (Fin n → Bool) :=
  let p := sym2Rep n v
  Sym2.mk p.1 (flipAt n p.1 c)

/-- Parent function on Sym2 for tree `k`.
    - If `v = r`: parent is `r`.
    - If `v = via`: parent is `r`.
    - If first rep endpoint `z = tgt`: parent is `via`.
    - Else: flip a differing coordinate of `z` towards `tgt`. -/
noncomputable def patentParentSym2 (n : Nat) (hn : 2 ≤ n)
    (r : Sym2 (Fin n → Bool)) (a b : Fin n → Bool) (d0 : Fin n)
    (k : TreeIdx n) (v : Sym2 (Fin n → Bool)) : Sym2 (Fin n → Bool) :=
  let via := patentViaSym2 n hn a b d0 k
  if v = r then r
  else if v = via then r
  else
    let tgt := patentTgtRep n a b k
    let p := sym2Rep n v
    let z := p.1
    if h : z = tgt then via
    else patentStepSym2 n v (diffCoord n z tgt h)

end HypercubeLineVISTSym2


