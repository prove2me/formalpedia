-- Prove2me | Definitions.Def_MantriCVQ_Supplement_leafOracle
-- name    : MantriCVQ_Supplement_leafOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:06:29.80783+00:00
-- url     : https://prove2.me/theorems/76f2f1c3-8d81-4ed9-ad5b-1146575d1f29
-- title:
--   Oracle storing a leaf table at size $n$
-- statement:
--   Given an oracle $O_0$, a size $n$, a height $h$ and a leaf table $Y$, this is the oracle that answers $Y(w)$ at every leaf address $1^n0w$ of an instance of size $n$ and height $h$ and answers as $O_0$ on every other string. It is how Appendix B presents a protocol with the instance $Y$ as its input and every other oracle answer fixed.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §7.1, p. 37 (PDF p. 39); Appendix B.2, p. 49 (PDF p. 51)

import Mathlib
import Definitions.Def_MantriCVQ_patch
import Definitions.Def_MantriCVQ_Addr
import Definitions.Def_MantriCVQ_dimsRange

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ.Supplement

open MantriCVQ

/-- The oracle that stores the leaf table `Y` of an instance of size `n` and height `h` at the leaf
addresses `1^n 0 w` and answers as `O₀` on every other string (Mantri, arXiv:2610.37635 (PDF sha256
d1fab777…1d0b33), §7.1, p. 37 (PDF p. 39): "Its leaves occupy the addresses `1^n 0 w`"; Appendix B.2,
p. 49 (PDF p. 51): "the input of a protocol is a valid instance of size `n` and height `h`, given by its
leaf table `X`, and every other oracle answer is fixed").

**Formalization Note** The leaf table is indexed by flat leaf addresses (strings), as in the published
`MantriCVQ.leafTable`, and only its values at leaf addresses `w` of an instance of height `h` are
stored: `leafTable (leafOracle O₀ n h Y) n w = Y w` for those `w`. -/
def leafOracle (O₀ : Oracle) (n h : ℕ) (Y : Str → Bool) : Oracle :=
  patch O₀ ((Finset.univ : Finset (Addr (dimsRange n 0 h))).image
      fun a => unary n ++ false :: Addr.toStr _ a)
    (fun x => Y ((x : Str).drop (n + 1)))

end MantriCVQ.Supplement


