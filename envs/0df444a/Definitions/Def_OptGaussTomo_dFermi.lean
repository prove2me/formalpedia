-- Prove2me | Definitions.Def_OptGaussTomo_dFermi
-- name    : OptGaussTomo_dFermi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:05:37.092199+00:00
-- url     : https://prove2.me/theorems/37adf645-254e-4cee-ac1a-268f30579aa0
-- title:
--   The dimensions $d_{n,m}$ of eq. (C.6)
-- statement:
--   For $n,m\in\mathbb N$,
--
--   $$
--   d_{n,m}=\prod_{1\le j<k\le m}\frac{2m+n-(j+k)}{2m-(j+k)} . \tag{C.6}
--   $$
--
--   By Lemma C.4 this is the dimension of the span $\mathcal V^\pm_{n,m}$ of the $n$-fold tensor powers of even (or odd) pure fermionic Gaussian states, and ratios $d_{n,m}/d_{k,m}$ govern the fidelity of the Gaussian Hayashi measurement.
--
--   **Formalization Note** Computed in the real numbers (no natural-number subtraction); every denominator is at least $1$. For $m\le1$ the product is empty and $d_{n,m}=1$.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Lemma C.4 p.37 (pdf p.37), eq. (C.6)

import Mathlib

namespace OptGaussTomo

/-!
# The dimensions `d_{n,m}` of the fermionic Hayashi spaces, eq. (C.6)

Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of bosonic and
fermionic Gaussian states*, arXiv:2607.11847 (held version, sha256 0f7548a2…), Lemma C.4, p.37,
eq. (C.6): `d_{n,m} = ∏_{1≤j<k≤m} (2m + n − (j + k)) / (2m − (j + k))`.

**Formalization Note.** The product runs over pairs `1 ≤ j < k ≤ m` (1-based, as in the source)
and is computed in `ℝ`, so there is no natural-number subtraction; every denominator is
`2m − (j + k) ≥ 1`. For `m ≤ 1` the product is empty and `d_{n,m} = 1`.
-/

/-- `d_{n,m} = ∏_{1≤j<k≤m} (2m + n − (j+k)) / (2m − (j+k))` (C.6). -/
noncomputable def dFermi (n m : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter (fun p => p.1 < p.2),
    ((2 * m + n : ℝ) - (p.1 + p.2)) / ((2 * m : ℝ) - (p.1 + p.2))

end OptGaussTomo


