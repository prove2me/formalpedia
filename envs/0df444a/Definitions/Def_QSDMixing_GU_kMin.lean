-- Prove2me | Definitions.Def_QSDMixing_GU_kMin
-- name    : QSDMixing_GU_kMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:53:50.788348+00:00
-- url     : https://prove2.me/theorems/43eeede7-f6ad-4fe4-818a-b0d3649844f5
-- title:
--   Sample complexity $k_{\min}(\epsilon)$ with uniform prior
-- statement:
--   For a finite ensemble $(\rho_i)_{i\in I}$ with uniform prior, the sample complexity is
--
--   $$
--   k_{\min}(\epsilon)=\min\Big\{k\ge1:\ \exists\text{ a POVM }(M_i)\text{ on }k\text{ copies with }\frac1{|I|}\sum_i\mathrm{tr}(M_i\rho_i^{\otimes k})\ge1-\epsilon\Big\}.
--   $$
--
--   This is the least number of i.i.d. copies that gives average success at least $1-\epsilon$.
--
--   **Formalization Note** The value lies in $\mathbb N\cup\{\infty\}$ and is $\infty$ when no $k$ qualifies. A geometrically uniform ensemble has uniform prior by definition, so the general prior of (2) is not needed.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), eqs. (3)–(4), pp.3–4

import Mathlib
import Definitions.Def_GaussTesting_Ell2
import Definitions.Def_QSDMixing_GU_MixedState
import Definitions.Def_QSDMixing_GU_IsPOVM
import Definitions.Def_QSDMixing_GU_copyEffect

set_option autoImplicit false
open GaussTesting (Ell2)

namespace QSDMixing.GU

/-- The sample complexity `k_min(ε)` of a finite ensemble with uniform prior: the least number `k ≥ 1`
of i.i.d. copies for which some POVM reaches average success at least `1 - ε`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), eqs. (3)–(4), pp.3–4, at `p_i = 1/|I|` (the prior of a geometrically uniform ensemble, p.17).

**Formalization Note.** The value is in `ℕ∞`, and it is `⊤` when no `k` qualifies, not the junk `0` of
`sInf` on `ℕ`. "`max_Π … ≥ 1 - ε`" is written "`∃ Π`, `… ≥ 1 - ε`", which does not assume the maximum is
attained. Minima range over `k ≥ 1`, the paper's `ℕ` in (52). -/
noncomputable def kMin {ι I : Type} [Fintype I] (e : I → MixedState ι) (ε : ℝ) : ℕ∞ :=
  sInf {K : ℕ∞ | ∃ k : ℕ, 1 ≤ k ∧ K = k ∧
    ∃ M : I → Ell2 (Fin k → ι) →L[ℂ] Ell2 (Fin k → ι), IsPOVM M ∧
      1 - ε ≤ (1 / (Fintype.card I : ℝ)) * ∑ i, copyEffect (e i) k (M i)}

end QSDMixing.GU


