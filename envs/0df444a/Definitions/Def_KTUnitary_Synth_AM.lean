-- Prove2me | Definitions.Def_KTUnitary_Synth_AM
-- name    : KTUnitary_Synth_AM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:24:34.589347+00:00
-- url     : https://prove2.me/theorems/7ea71997-18af-4f75-960c-6087b97491b7
-- title:
--   The class $\mathsf{AM}^L$
-- statement:
--   A language $A$ is in $\mathsf{AM}^L$ (Babai's public-coin Arthur–Merlin class, relativized) if there are a deterministic $L$-oracle Turing machine $M$ and polynomials $p,r,m$ such that $M^L(x,c,y)$ halts within $p(|x|)$ steps for all coins $c\in\{0,1\}^{r(|x|)}$ and messages $y\in\{0,1\}^{m(|x|)}$, and
--   $$\Pr_c\big[\exists y:\ M^L(x,c,y)\text{ accepts}\big]\ \ge\ \tfrac23\text{ if }x\in A,\qquad\le\ \tfrac13\text{ if }x\notin A.$$
--
--   The hypothesis $\mathsf{AM}^L=\mathsf{NEXP}^L$ of the easy witness lemma (Lemma 7.7) is stated with this class.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Lemma 7.7, p. 37 (standard definition)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

open Classical in
/-- **The class `AM^L`** (used in Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Lemma 7.7, p. 37; Babai's public-coin Arthur–Merlin
class, standard definition). A language `A` is in `AM^L` if some deterministic `L`-oracle machine
`M` and polynomials `p`, `r`, `m` are such that `M^L(x, r', y)` halts within `p(|x|)` steps for all
`r'` of length `r(|x|)` and `y` of length `m(|x|)`, and the fraction of coin strings `r'` for which
some Merlin message `y` makes `M` accept is at least `2/3` if `x ∈ A` and at most `1/3` if `x ∉ A`.

**Formalization Note** `(x, r', y)` is passed as `tup [x, r', y]`. -/
def AM (L : Oracle) : Set (Set Str) :=
  {A | ∃ (M : OTM) (p r m : Polynomial ℕ), ∀ x : Str,
    (∀ (c : Bits (r.eval x.length)) (y : Bits (m.eval x.length)),
      M.result L (tup [x, List.ofFn c, List.ofFn y]) (p.eval x.length) ≠ none) ∧
    (x ∈ A → (2 / 3 : ℝ) ≤ ((Finset.univ.filter fun c : Bits (r.eval x.length) =>
        ∃ y : Bits (m.eval x.length),
          M.result L (tup [x, List.ofFn c, List.ofFn y]) (p.eval x.length) = some true).card : ℝ) /
        2 ^ r.eval x.length) ∧
    (x ∉ A → ((Finset.univ.filter fun c : Bits (r.eval x.length) =>
        ∃ y : Bits (m.eval x.length),
          M.result L (tup [x, List.ofFn c, List.ofFn y]) (p.eval x.length) = some true).card : ℝ) /
        2 ^ r.eval x.length ≤ 1 / 3)}

end KTUnitary.Synth


