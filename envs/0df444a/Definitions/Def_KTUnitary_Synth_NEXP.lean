-- Prove2me | Definitions.Def_KTUnitary_Synth_NEXP
-- name    : KTUnitary_Synth_NEXP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:24:21.733904+00:00
-- url     : https://prove2.me/theorems/9d3b2c4a-67b8-4e83-b053-3fa8d3e890bd
-- title:
--   The class $\mathsf{NEXP}^L$
-- statement:
--   A language $A$ is in $\mathsf{NEXP}^L$ if there are a deterministic $L$-oracle Turing machine $M$ and polynomials $p,q$ such that $M^L(x,w)$ halts within $2^{q(|x|)}$ steps for every $x,w$, and
--   $$x\in A\iff \exists w,\ |w|\le 2^{p(|x|)},\ M^L(x,w)\text{ accepts}.$$
--
--   This is the verifier form of nondeterministic exponential time, relativized; the paper uses it without defining it.
--
--   **Formalization Note** The time bound is exponential in $|x|$, not in $|(x,w)|$; a witness may be exponentially long.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Lemma 7.7, Corollaries 7.11, 7.16, pp. 37–39 (standard definition)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **The class `NEXP^L`** (used in Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Lemma 7.7, Corollaries 7.11 and 7.16, pp. 37–39;
standard definition, in verifier form): a language `A` is in `NEXP^L` if some deterministic
`L`-oracle machine `M` and polynomials `p`, `q` are such that `M^L(x, w)` halts within
`2^{q(|x|)}` steps for every `x` and `w`, and `x ∈ A` exactly when some witness `w` of length at most
`2^{p(|x|)}` makes `M^L(x, w)` accept.

**Formalization Note** The time bound is exponential in `|x|`, not in `|(x, w)|`; a witness may be
exponentially long. `(x, w)` is passed as `tup [x, w]`. -/
def NEXP (L : Oracle) : Set (Set Str) :=
  {A | ∃ (M : OTM) (p q : Polynomial ℕ),
    (∀ x w : Str, M.result L (tup [x, w]) (2 ^ q.eval x.length) ≠ none) ∧
    ∀ x : Str, x ∈ A ↔ ∃ w : Str, w.length ≤ 2 ^ p.eval x.length ∧
      M.result L (tup [x, w]) (2 ^ q.eval x.length) = some true}

end KTUnitary.Synth


