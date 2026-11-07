-- Prove2me | Definitions.Def_HeilmanMax3Cut_Mbil
-- name    : HeilmanMax3Cut_Mbil
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:59.711935+00:00
-- url     : https://prove2.me/theorems/0956dd49-33e1-449e-99b3-e4c3216cff80
-- title:
--   The bilinear minimum $M_m$
-- statement:
--   For $m\ge2$ and $\sigma>0$, $M_m$ is the infimum of $Q^{(m)}_\sigma(A,B)$ over pairs of partitions $A,B$ of $\mathbb R^m$ into three measurable sets satisfying $\gamma_m(A_i)=\gamma_m(B_i)$ for $i=1,2,3$.
--
--   **Formalization Note** Partitions are almost-everywhere partitions: measurable cells such that almost every point lies in exactly one cell. Null modifications change neither $\gamma_m(A_i)$ nor $Q$, so this is the paper's infimum. For $\sigma>0$ all values are nonnegative, so the real infimum is genuine.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Section 7, p.21

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HeilmanMax3Cut_Qstab
open MeasureTheory OAI.GaussianPropeller

namespace HeilmanMax3Cut

/-- **The bilinear minimum `M_m`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Section 7, p.21: "For `m ≥ 2`, let `M_m` be the infimum
of `Q_σ^{(m)}(A, B)` over pairs of partitions satisfying `γ_m(Aᵢ) = γ_m(Bᵢ)` for `i = 1, 2, 3`."

**Formalization Note.** Partitions are `IsPartition` (measurable cells, `γ_m`-almost every point in
exactly one cell), from the reused block `OAI.GaussianPropeller`. Changing a cell on a null set
changes neither `γ_m(Aᵢ)` nor `Q_σ^{(m)}(A, B)` (for `|σ| < 1`, `T_σ 1_B` does not see null
modifications of `B`), so the infimum equals the paper's infimum over exact partitions. For
`σ > 0` every value is `≥ 0` and the set is nonempty, so the real `sInf` is the true infimum. -/
noncomputable def Mbil (m : ℕ) (σ : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ A B : Fin 3 → Set (Space m), IsPartition A ∧ IsPartition B ∧
    (∀ i, gaussian m (A i) = gaussian m (B i)) ∧ Qstab m σ A B = v}

end HeilmanMax3Cut


