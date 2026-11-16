-- Prove2me | Definitions.Def_CountOrderings_NFree_Certificate
-- name    : CountOrderings_NFree_Certificate
-- status  : Definition
-- author  : @bersubs
-- created : 2026-11-15T16:10:10.701492+00:00
-- url     : https://prove2.me/theorems/d563d0fc-8016-4dad-8bd3-4d1df4dcd2b9
-- title:
--   Row-major certificates for N-free linear extensions
-- statement:
--   A ranking is encoded by its permutation matrix, written row by row. A word is an accepted certificate exactly when the input encodes an N-free poset of height three and the matrix encodes a linear extension of that poset.
-- source:
--   Arenas, Schild and Subercaseaux, Hardness of Counting Orderings: Taking Gadget Amplification to the Limit, STOC 2027 submission #1207, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1207.pdf, Appendix A.12, pp. 37–38 (PDF pp. 38–39), proof of Theorem 6.3

import Definitions.Def_CountOrderings_NFree_Encoding

namespace CountOrderings.NFree

/-- Encode a ranking by the row-major incidence matrix of its graph. The bit in row
`i` and column `j` records whether element `i` is assigned rank `j`. -/
def extensionCertificate {n : ℕ} {R : Fin n → Fin n → Prop} {hR : IsPartialOrderRel R}
    (e : RelPoset n R hR ≃ Fin (Fintype.card (RelPoset n R hR))) : List Bool :=
  List.ofFn fun k : Fin (n * Fintype.card (RelPoset n R hR)) =>
    let ij := (finProdFinEquiv (m := n) (n := Fintype.card (RelPoset n R hR))).symm k
    decide (e ij.1 = ij.2)

/-- An accepted certificate is exactly the incidence matrix of a linear extension
of the valid N-free poset of height three encoded by the input. -/
def IsLinExtCertificate (x w : List Bool) : Prop :=
  ∃ hx : ValidPosetCode x,
    IsNFree (decodePoset x hx) ∧ height (decodePoset x hx) = 3 ∧
      w ∈ extensionCertificate (hR := hx.2) '' FCP.Order.LinearExtensions (decodePoset x hx)

end CountOrderings.NFree


