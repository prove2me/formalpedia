-- Prove2me | Definitions.Def_KTUnitary_Synth_BPP
-- name    : KTUnitary_Synth_BPP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:24:27.407868+00:00
-- url     : https://prove2.me/theorems/030af1d9-0f9d-4e7e-bf81-17a8e70e83d0
-- title:
--   The class $\mathsf{BPP}^L$
-- statement:
--   A language $A$ is in $\mathsf{BPP}^L$ if there are a deterministic $L$-oracle Turing machine $M$ and polynomials $p,r$ such that for every input $x$ and every random string $w\in\{0,1\}^{r(|x|)}$ the run $M^L(x,w)$ halts within $p(|x|)$ steps, and
--   $$\Pr_w[M^L(x,w)\text{ accepts}]\ \ge\ \tfrac23\ \text{ if }x\in A,\qquad \le\ \tfrac13\ \text{ if }x\notin A.$$
--
--   The paper uses $\mathsf{BPP}^L$ without defining it; this is the standard bounded-error probabilistic polynomial time, relativized. It is the second alternative of the goal: $\mathsf{BPP}^L\neq\mathsf{NEXP}^L$.
--
--   **Formalization Note** The machine model is the same `OTM` as for every other class of the mission; $(x,w)$ is passed as `tup [x, w]`.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Corollaries 7.11 and 7.16, pp. 37, 39 (standard definition)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

open Classical in
/-- **The class `BPP^L`** (used in Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Corollaries 7.11 and 7.16, pp. 37 and 39; the paper does
not define it, and this is the standard definition). A language `A` is in `BPP^L` if some
deterministic `L`-oracle machine `M` and polynomials `p`, `r` are such that for every input `x`
and every random string `w` of length `r(|x|)`, `M^L(x, w)` halts within `p(|x|)` steps, and the
fraction of `w` on which it accepts is at least `2/3` if `x ∈ A` and at most `1/3` if `x ∉ A`.

**Formalization Note** The machine model is the published `QAdvFew.PoQOracle.OTM`, the same as
for every other class of this mission; `(x, w)` is passed as `tup [x, w]`. -/
def BPP (L : Oracle) : Set (Set Str) :=
  {A | ∃ (M : OTM) (p r : Polynomial ℕ), ∀ x : Str,
    (∀ w : Bits (r.eval x.length), M.result L (tup [x, List.ofFn w]) (p.eval x.length) ≠ none) ∧
    (x ∈ A → (2 / 3 : ℝ) ≤ ((Finset.univ.filter fun w : Bits (r.eval x.length) =>
        M.result L (tup [x, List.ofFn w]) (p.eval x.length) = some true).card : ℝ) /
        2 ^ r.eval x.length) ∧
    (x ∉ A → ((Finset.univ.filter fun w : Bits (r.eval x.length) =>
        M.result L (tup [x, List.ofFn w]) (p.eval x.length) = some true).card : ℝ) /
        2 ^ r.eval x.length ≤ 1 / 3)}

end KTUnitary.Synth


