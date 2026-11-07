-- Prove2me | Definitions.Def_QSDMixing_GU_kWc
-- name    : QSDMixing_GU_kWc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:53:51.481127+00:00
-- url     : https://prove2.me/theorems/70028bb1-bd70-4082-8e25-439023655ace
-- title:
--   Worst-case sample complexity $k_{\mathrm{wc}}(\epsilon)$
-- statement:
--   For a finite ensemble $(\rho_i)_{i\in I}$, the worst-case sample complexity is
--
--   $$
--   k_{\mathrm{wc}}(\epsilon)=\min\Big\{k\ge1:\ \exists\text{ a POVM }(M_i)\text{ on }k\text{ copies with }\mathrm{tr}(M_i\rho_i^{\otimes k})\ge1-\epsilon\text{ for every }i\Big\}.
--   $$
--
--   Unlike $k_{\min}$, it requires every label to be identified with high probability.
--
--   **Formalization Note** The value lies in $\mathbb N\cup\{\infty\}$ and is $\infty$ when no $k$ qualifies.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), eqs. (34)–(35), p.12

import Mathlib
import Definitions.Def_GaussTesting_Ell2
import Definitions.Def_QSDMixing_GU_MixedState
import Definitions.Def_QSDMixing_GU_IsPOVM
import Definitions.Def_QSDMixing_GU_copyEffect

set_option autoImplicit false
open GaussTesting (Ell2)

namespace QSDMixing.GU

/-- The worst-case sample complexity `k_wc(ε)`: the least `k ≥ 1` for which some POVM on `k` copies has
every conditional success at least `1 - ε`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), eqs. (34)–(35), p.12.

**Formalization Note.** `max_M min_i … ≥ 1 - ε` is written "`∃ M, ∀ i, … ≥ 1 - ε`". The value is in `ℕ∞`
and is `⊤` when no `k` qualifies. -/
noncomputable def kWc {ι I : Type} [Fintype I] (e : I → MixedState ι) (ε : ℝ) : ℕ∞ :=
  sInf {K : ℕ∞ | ∃ k : ℕ, 1 ≤ k ∧ K = k ∧
    ∃ M : I → Ell2 (Fin k → ι) →L[ℂ] Ell2 (Fin k → ι), IsPOVM M ∧
      ∀ i, 1 - ε ≤ copyEffect (e i) k (M i)}

end QSDMixing.GU


