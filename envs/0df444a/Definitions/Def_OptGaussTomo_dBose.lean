-- Prove2me | Definitions.Def_OptGaussTomo_dBose
-- name    : OptGaussTomo_dBose
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:05:38.308462+00:00
-- url     : https://prove2.me/theorems/7ec2d8e4-eed9-4ee6-b17e-0cab8761db23
-- title:
--   The formal degrees $d_{n,m}$ of eq. (D.12)
-- statement:
--   For $n,m\in\mathbb N$,
--
--   $$
--   d_{n,m}=\Big(\prod_{1\le i<j\le m}(j-i)\Big)\Big(\prod_{1\le i\le j\le m}\big(n-(i+j)\big)\Big), \tag{D.12}
--   $$
--
--   the formal degree of the irreducible representation of the metaplectic group carried by the span of $n$ copies of the pure mean-zero Gaussian states, valid for $n\ge2m+1$. Only ratios $d_{n,m}/d_{n',m}$ enter the mission, in which the first product cancels.
--
--   **Formalization Note** Computed in the real numbers. The formula is the paper's for $n\ge2m+1$, where every factor is positive, and is used only there.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Lemma D.5 p.46 (pdf p.46), eq. (D.12)

import Mathlib

namespace OptGaussTomo

/-!
# The formal degrees `d_{n,m}` of the bosonic Hayashi representations, eq. (D.12)

Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of bosonic and
fermionic Gaussian states*, arXiv:2607.11847 (held version, sha256 0f7548a2…), Lemma D.5, p.46,
eq. (D.12): `d_{n,m} = (∏_{i<j} (j − i)) (∏_{1≤i≤j≤m} (n − (i + j)))` for `n ≥ 2m + 1`.

**Formalization Note.** Both products run over `1 ≤ i, j ≤ m` (1-based, as in the source; the
first over `i < j`, the second over `i ≤ j`) and are computed in `ℝ`, so there is no
natural-number subtraction. The formula is the source's only for `n ≥ 2m + 1`, where every factor
is positive; it is used only there (Lemma D.16 evaluates it at `n + 2m + 1` and `n + 2m + 1 + k`).
Only ratios `d_{n,m}/d_{n',m}` enter the statements, in which the first product cancels.
-/

/-- `d_{n,m} = (∏_{1≤i<j≤m} (j − i)) · ∏_{1≤i≤j≤m} (n − (i + j))` (D.12). -/
noncomputable def dBose (n m : ℕ) : ℝ :=
  (∏ p ∈ (Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter (fun p => p.1 < p.2),
      ((p.2 : ℝ) - p.1)) *
    ∏ p ∈ (Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter (fun p => p.1 ≤ p.2),
      ((n : ℝ) - (p.1 + p.2))

end OptGaussTomo


