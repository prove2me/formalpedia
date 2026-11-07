-- Prove2me | Definitions.Def_KTUnitary_Synth_FNEXP
-- name    : KTUnitary_Synth_FNEXP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:24:36.965569+00:00
-- url     : https://prove2.me/theorems/5ad90440-6c1f-48a6-8075-8cf6cdcd1ae2
-- title:
--   The class $\mathsf{FNEXP}^L$ of relations
-- statement:
--   A relation $R\subseteq\{0,1\}^*\times\{0,1\}^*$ is in $\mathsf{FNEXP}^L$ if there are an $L$-oracle Turing machine $M$ and a polynomial $p$ such that, for all $x,y$, $M^L(x,y)$ halts within $2^{p(|x|)}$ steps and accepts exactly when $(x,y)\in R$, and $|y|\le 2^{p(|x|)}$ for every $(x,y)\in R$.
--
--   These are the $\mathsf{NEXP}$ search problems; the paper relates efficient unitary synthesis to oracles that answer them.
--
--   **Formalization Note** One polynomial bounds both time and witness length (the larger of two polynomials bounds both).
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.2, p. 34

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

open Classical in
/-- **The class `FNEXP^L` of relations** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.2, p. 34): "A relation
`R ⊆ {0,1}* × {0,1}*` is in `FNEXP^L` if there is an `L`-oracle Turing machine `M(x, y)` that runs in
time `2^{poly(|x|)}` and whose output indicates whether `(x, y) ∈ R`, and `|y| ≤ 2^{poly(|x|)}` for
every `(x, y) ∈ R`."

Here: one machine `M` and one polynomial `p` such that for all `x`, `y`, `M^L(tup [x, y])` halts within
`2^{p(|x|)}` steps with answer `(x, y) ∈ R`, and every `(x, y) ∈ R` has `|y| ≤ 2^{p(|x|)}`.

**Formalization Note** One polynomial bounds both the running time and the witness length; this
is no loss, since the larger of two polynomials bounds both. -/
def FNEXP (L : Oracle) : Set (Set (Str × Str)) :=
  {R | ∃ (M : OTM) (p : Polynomial ℕ),
    (∀ x y : Str, M.result L (tup [x, y]) (2 ^ p.eval x.length) = some (decide ((x, y) ∈ R))) ∧
    ∀ x y : Str, (x, y) ∈ R → y.length ≤ 2 ^ p.eval x.length}

end KTUnitary.Synth


