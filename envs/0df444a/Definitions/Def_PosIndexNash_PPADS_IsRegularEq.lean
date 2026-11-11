-- Prove2me | Definitions.Def_PosIndexNash_PPADS_IsRegularEq
-- name    : PosIndexNash_PPADS_IsRegularEq
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:32:24.581169+00:00
-- url     : https://prove2.me/theorems/a8264460-2945-4d6e-9889-adb89c962d6b
-- title:
--   Regular equilibrium of a bimatrix game (p. 13)
-- statement:
--   Let $(x, y)$ be a pair of mixed strategies of the game $(A, B)$, with supports $I = \mathrm{supp}(x)$ and $J = \mathrm{supp}(y)$. It is **regular** (locally nondegenerate) when
--   $$|I| = |J|,\qquad \Delta(A_{I,J}) \ne 0,\qquad \Delta((B_{I,J})^\top) \ne 0,\qquad BR_1(y) \subseteq I,\qquad BR_2(x) \subseteq J,$$
--   that is, both bordered matrices of the Shapley index are nonsingular and no unused pure strategy is a best response. The index of a regular equilibrium is well defined even when the game is degenerate elsewhere.
--
--   **Formalization Note** The predicate states the regularity conditions only; it is used together with the public `QuasiStrictNE.IsNE`. Supports are enumerated increasingly, as in `shapleyIndex`.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 13, paragraph after Definition 2.3

import Mathlib
import Definitions.Def_QuasiStrictNE_supp
import Definitions.Def_QuasiStrictNE_BR1
import Definitions.Def_QuasiStrictNE_BR2
import Definitions.Def_PosIndexNash_PPADS_ShapleyIndex

namespace PosIndexNash.PPADS

/-- **Regular equilibrium** (Kontogiannis, Panageas, Pollatos, Yan, *Finding a Positive Index Nash
Equilibrium is PPADS-Complete*, arXiv:2609.23879, p. 13: "we call an equilibrium (x, y) regular
… if |I| = |J|, both bordered matrices in Definition 2.3 are nonsingular, and no unused pure
strategy is a best response").

With `I = supp(x)`, `J = supp(y)`: `|I| = |J| = k`, `Δ(A_{I,J}) ≠ 0`, `Δ((B_{I,J})ᵀ) ≠ 0`,
`BR1(y) ⊆ I` and `BR2(x) ⊆ J`.

**Formalization Note** This is the regularity condition only; it is used together with the public
`QuasiStrictNE.IsNE` (the equilibrium condition). Supports are enumerated increasingly, as in
`shapleyIndex`; nonsingularity of a bordered matrix does not depend on the ordering. -/
def IsRegularEq {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    Prop :=
  ∃ h : (QuasiStrictNE.supp y).card = (QuasiStrictNE.supp x).card,
    borderedDet (A.submatrix ((QuasiStrictNE.supp x).orderEmbOfFin rfl)
      ((QuasiStrictNE.supp y).orderEmbOfFin h)) ≠ 0 ∧
    borderedDet (B.submatrix ((QuasiStrictNE.supp x).orderEmbOfFin rfl)
      ((QuasiStrictNE.supp y).orderEmbOfFin h)).transpose ≠ 0 ∧
    QuasiStrictNE.BR1 A y ⊆ QuasiStrictNE.supp x ∧ QuasiStrictNE.BR2 B x ⊆ QuasiStrictNE.supp y

end PosIndexNash.PPADS


