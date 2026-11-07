-- Prove2me | Definitions.Def_KServerConj_rowReplace
-- name    : KServerConj_rowReplace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:34.949216+00:00
-- url     : https://prove2.me/theorems/ee63e818-1d7e-42f6-adfd-6b3d24fb44df
-- title:
--   Row replacement $q'_x=(\delta_x,\hat q_x)$ and the fresh row $\delta_x=\xi_{t,x}z^{d(r,x)}$, equations (11)–(12)
-- statement:
--   With $k=m+1$ and columns $q_x=(a_x,\hat q_x)$, the **row replacement** by a row $(\delta_x)_{x\in M}$ produces the columns
--
--   $$q'_x=(\delta_x,\hat q_x):$$
--
--   the first row of the column matrix is replaced by $(\delta_x)_x$ and the other rows are kept. At the $t$-th request $r=r_t$ the paper uses the fresh row
--
--   $$\delta_x=\xi_{t,x}\,z^{d(r,x)},$$
--
--   whose valuation is $\nu(\delta_x)=d(r,x)$ and whose coefficients are variables not used before time $t$.
--
--   **Formalization Note** The first coordinate is index $0$ of `Fin (m+1)`; $\hat q_x$ is the tail of $q_x$.
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §2.3, equations (11)–(12), p.7 (pdf p.8)

import Mathlib
import Definitions.Def_KServerConj_K

namespace KServerConj

/-- **The row replacement** (12) of Coester, Koutsoupias, Zbysiński, *The k-server conjecture is
true*, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §2.3, printed p.7 (PDF p.8):
"Write q_x = (a_x, q̂_x), with a_x ∈ K and q̂_x ∈ K^{k−1}. […] replace the columns by
q′_x = (δ_x, q̂_x). (12) Equivalently, replace the first row of the entire column matrix by
(δ_x)_{x∈M} and leave the other rows unchanged."

**Formalization Note.** Here `k = m + 1`, the first coordinate is `0 : Fin (m+1)`, and
`q̂_x = Fin.tail (q x)`. -/
noncomputable def rowReplace {m : ℕ} {M : Type*} (q : M → Fin (m + 1) → K (m + 1) M)
    (δ : M → K (m + 1) M) : M → Fin (m + 1) → K (m + 1) M :=
  fun x => Fin.cons (δ x) (Fin.tail (q x))

/-- **The fresh first row** (11), §2.3, printed p.7 (PDF p.8): "For request number t, set
δ_x = ξ_{t,x} z^{d(r,x)} for every x ∈ M", where `r = r t` is the `t`-th request. -/
noncomputable def freshRow {m : ℕ} {M : Type*} [PseudoMetricSpace M] (r : ℕ → M) (t : ℕ) :
    M → K (m + 1) M :=
  fun x => coef (Sum.inr (t, x)) * zp (dist (r t) x)

end KServerConj


