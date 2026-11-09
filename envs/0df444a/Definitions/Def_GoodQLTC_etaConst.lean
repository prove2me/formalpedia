-- Prove2me | Definitions.Def_GoodQLTC_etaConst
-- name    : GoodQLTC_etaConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:49:21.537233+00:00
-- url     : https://prove2.me/theorems/2aa00bf3-285f-47b9-8b19-491f2ac4ca6f
-- title:
--   Constants $\kappa$, $b_{j\ell}$, $L$, $\eta$, $\alpha_j$ of §8
-- statement:
--   $\kappa=\min\{\kappa_{r,u}:1\le r\le t,\ 0\le u<r\}$; for $1\le j<t$, $0\le\ell\le j$,
--   $$
--   b_{j\ell}=c_{j\ell}(t-\ell)\binom{t-\ell}{j-\ell}(j-\ell)!\Big(\frac{\tau}{\kappa}\Big)^{j-\ell+1},\qquad L=\max_{1\le j<t}\sum_{\ell=0}^jb_{j\ell},\qquad \eta=\frac1{2C_{\mathrm{mix}}L},
--   $$
--   and $\alpha_j=\min\Big\{\frac1{\mathrm{sym}_j(n_1,\dots,n_t)},\ \frac{\eta\,\mathrm{sym}_{j+1}(n_1,\dots,n_t)}{2\,\mathrm{sym}_j(n_1,\dots,n_t)}\Big\}$.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §8, p.25 (PDF p.28) and Theorem 8.2, p.25

import Mathlib
import Definitions.Def_GoodQLTC_esym
import Definitions.Def_GoodQLTC_kappa
import Definitions.Def_GoodQLTC_faceWalk

namespace GoodQLTC

/-- `κ := min{κ_{r,u} : 1 ≤ r ≤ t, 0 ≤ u < r}` (arXiv:2609.20780, §8, p.25). **Formalization
Note.** A `min`-fold starting from `ρ = κ_{1,0}`, which is one of the values. -/
noncomputable def kappaMin (t : ℕ) (ρ τ : ℝ) : ℝ :=
  ((Finset.Icc 1 t ×ˢ Finset.range t).filter fun ru : ℕ × ℕ => ru.2 < ru.1).fold min ρ
    fun ru => kappa ρ τ ru.1 ru.2

/-- `b_{jℓ} := c_{jℓ} (t − ℓ) binom(t − ℓ, j − ℓ) (j − ℓ)! (τ/κ)^{j−ℓ+1}` (arXiv:2609.20780,
§8, p.25), for `1 ≤ j < t`, `0 ≤ ℓ ≤ j`. -/
noncomputable def bConst (t : ℕ) (ρ τ : ℝ) (j ℓ : ℕ) : ℝ :=
  (cConst j ℓ : ℝ) * ((t : ℝ) - ℓ) * (Nat.choose (t - ℓ) (j - ℓ) : ℝ) * ((j - ℓ).factorial : ℝ) *
    (τ / kappaMin t ρ τ) ^ (j - ℓ + 1)

/-- `L := max_{1≤j<t} ∑_{ℓ=0}^{j} b_{jℓ}` (arXiv:2609.20780, §8, p.25). **Formalization Note.**
A `max`-fold starting from `0` (all sums are positive). -/
noncomputable def LConst (t : ℕ) (ρ τ : ℝ) : ℝ :=
  (Finset.Ico 1 t).fold max 0 fun j => ∑ ℓ ∈ Finset.range (j + 1), bConst t ρ τ j ℓ

/-- `η := 1/(2 C_mix L)`, Gay–Jeronimo, arXiv:2609.20780 (held version), §8, p.25, with `C_mix`
from the proof of Theorem 7.1 (p.24). -/
noncomputable def etaConst (t : ℕ) (ρ τ : ℝ) : ℝ :=
  1 / (2 * Cmix t τ * LConst t ρ τ)

/-- `α_j := min{1/sym_j(n_1,…,n_t), η sym_{j+1}(n_1,…,n_t)/(2 sym_j(n_1,…,n_t))}`
(arXiv:2609.20780, Theorem 8.2, p.25). -/
noncomputable def alphaConst {t : ℕ} (n : Fin t → ℕ) (ρ τ : ℝ) (j : ℕ) : ℝ :=
  min (1 / esym (fun i => (n i : ℝ)) j)
    (etaConst t ρ τ * esym (fun i => (n i : ℝ)) (j + 1) / (2 * esym (fun i => (n i : ℝ)) j))

end GoodQLTC


