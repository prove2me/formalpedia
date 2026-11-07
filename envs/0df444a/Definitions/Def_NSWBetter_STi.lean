-- Prove2me | Definitions.Def_NSWBetter_STi
-- name    : NSWBetter_STi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:16.926264+00:00
-- url     : https://prove2.me/theorems/c6f04b54-43b9-461c-b638-3eab6507cbef
-- title:
--   $\mathrm{ST}(x,i)=\mathbb E[\ln v_i(X_i)]$
-- statement:
--   $\mathrm{ST}(x,i)=\mathbb E[\ln v_i(X_i)]=\sum_M D(M)\ln v_i(X_i(M))$, the expected log utility of agent $i$ after ST rounding with scheme $D$; it is $-\infty$ if some matching of positive probability gives $i$ value $0$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 4, p.17 (definition of ST(x, i))

import Mathlib
import Definitions.Def_HayashiHoeffding_elog
import Definitions.Def_NSWBetter_bundleOf

namespace NSWBetter

/-- **Expected log utility of one agent under ST rounding.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 4, p.17: "we define ST(x, i) to be the value E[ln(vi(Xi))]".

`STi v D i = Σ_M D(M) · HayashiHoeffding.elog(v_i(X_i(M)))` in `EReal`: `−∞` if a matching of positive probability leaves `i` with value `0`. -/
noncomputable def STi {n m : ℕ} (v : Fin n → Fin m → ℝ) (D : Finset (Fin n × Fin m × Fin m) → ℝ)
    (i : Fin n) : EReal :=
  ∑ M, ((D M : ℝ) : EReal) * HayashiHoeffding.elog (∑ g ∈ bundleOf M i, v i g)

end NSWBetter


