-- Prove2me | Definitions.Def_KTUnitary_Synth_FNEXPpoly
-- name    : KTUnitary_Synth_FNEXPpoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:26:49.233742+00:00
-- url     : https://prove2.me/theorems/8b041534-5bdd-406b-995e-07cca551e895
-- title:
--   The class $\mathsf{FNEXP}^L[\mathrm{poly}]$ of relations
-- statement:
--   A relation $R$ is in $\mathsf{FNEXP}^L[\mathrm{poly}]$ if it is in $\mathsf{FNEXP}^L$ by a machine $M$ that, in addition, only queries $L$ on strings of length at most $q(|x|)$ for some polynomial $q$ (during the first $2^{p(|x|)}$ steps of every run on $(x,y)$).
--
--   It is the class of relations in the dichotomy of Lemma 7.4.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.2, p. 34

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_KTUnitary_Synth_queries

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

open Classical in
/-- **The class `FNEXP^L[poly]` of relations** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.2, p. 34): "`R` is in
`FNEXP^L[poly]` if there exists such an `M` that is additionally restricted to only query `L` on
strings of length at most `poly(|x|)`."

Here: as `FNEXP L`, with a further polynomial `q` such that every string queried by the run of
`M^L` on `tup [x, y]` within its `2^{p(|x|)}` steps has length at most `q(|x|)`. -/
def FNEXPpoly (L : Oracle) : Set (Set (Str × Str)) :=
  {R | ∃ (M : OTM) (p q : Polynomial ℕ),
    (∀ x y : Str, M.result L (tup [x, y]) (2 ^ p.eval x.length) = some (decide ((x, y) ∈ R))) ∧
    (∀ x y : Str, (x, y) ∈ R → y.length ≤ 2 ^ p.eval x.length) ∧
    ∀ x y : Str, ∀ s ∈ queries M L (tup [x, y]) (2 ^ p.eval x.length), s.length ≤ q.eval x.length}

end KTUnitary.Synth


