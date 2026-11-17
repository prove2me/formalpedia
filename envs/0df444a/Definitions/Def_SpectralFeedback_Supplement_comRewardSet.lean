-- Prove2me | Definitions.Def_SpectralFeedback_Supplement_comRewardSet
-- name    : SpectralFeedback_Supplement_comRewardSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:55:30.783018+00:00
-- url     : https://prove2.me/theorems/9b427e7f-b9fd-436c-80c7-055a05a5c215
-- title:
--   Rewards of pairwise commuting decompositions, $G^{\mathrm{com}}_{m,s}$
-- statement:
--   For $R\succeq0$ in $\mathbb C^{d\times d}$, a reward function $F$ on $\mathbb R^s$ and $m\ge1$, the **commuting achievable rewards** are
--
--   $$
--   \Bigl\{\sum_{h=1}^m f_{F,s}(A_h)\;:\;A_h\succeq0,\ A_hA_{h'}=A_{h'}A_h\ \text{for all }h,h',\ \sum_hA_h=R\Bigr\},
--   $$
--
--   where $f_{F,s}(A)=F(\lambda_1(A),\dots,\lambda_s(A))$ is the published spectral reward. With $F=\chi_s$, the paper's $G^{\mathrm{com}}_{m,s}(R)$ is the maximum of this set. Theorem G.8 compares it with the unrestricted value $G_{m,s}(R)$.
--
--   **Formalization Note** The conventions are those of the published `rewardSet`: complex positive semidefinite atoms, no rank constraint, zero atoms allowed. In addition, the atoms (the Gram atoms, not the physical POVM effects) commute pairwise. "$G^{\mathrm{com}}_{m,s}(R)=v$" is written `IsGreatest (comRewardSet s F m R) v`.
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), Theorem G.8, p.103 (PDF p.105)

import Mathlib
import Definitions.Def_SpectralFeedback_rewardSet

open scoped ComplexOrder

namespace SpectralFeedback

namespace Supplement

/-- **The achievable rewards of a pairwise commuting `m`-atom decomposition** (Qi, *Spectral
Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination*, manuscript
(Nov. 2026), Theorem G.8, p.103 (PDF p.105): "Let `G^com_{m,s}` restrict the atoms to be pairwise
commuting"):
`{ ∑_h f_{F,s}(A_h) | A_h ⪰ 0, A_h A_{h′} = A_{h′} A_h for all h, h′, ∑_h A_h = R }`.

The paper's `G^com_{m,s}(R)` is the maximum of this set (with `F = χ_s`); "`G^com = v`" is
`IsGreatest (comRewardSet s F m R) v`.

**Formalization Note** Same conventions as the published `rewardSet` (complex PSD atoms, no rank
constraint, zero atoms allowed), plus pairwise commutation of the atoms themselves (the Gram atoms,
not the physical POVM effects). -/
def comRewardSet {d : ℕ} (s : ℕ) (F : (Fin s → ℝ) → ℝ) (m : ℕ) (R : Matrix (Fin d) (Fin d) ℂ) :
    Set ℝ :=
  {v | ∃ A : Fin m → Matrix (Fin d) (Fin d) ℂ,
    (∀ h, (A h).PosSemidef) ∧ (∀ h h', A h * A h' = A h' * A h) ∧ ∑ h, A h = R ∧
      v = ∑ h, reward s F (A h)}

end Supplement

end SpectralFeedback


