-- Prove2me | Definitions.Def_OnlineShadow_LogRate_numberOp
-- name    : OnlineShadow_LogRate_numberOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:06:01.953411+00:00
-- url     : https://prove2.me/theorems/cc1dd97b-ed82-419a-ad57-f6a5b983d84e
-- title:
--   Number operator $\mathsf N=\sum_i Q_i$
-- statement:
--   With $Q_i=1-P_i$ and $P_i=|\psi\rangle\langle\psi|$ on slot $i$, the **number operator** on $(\mathcal H\otimes\mathcal R)^{\otimes n}$ is
--   $$\mathsf N=\sum_{i=1}^nQ_i .$$
--   It counts the copies that are not in the purification $|\psi\rangle$: on the component $|\phi_S\rangle$ of the excitation decomposition it acts as multiplication by $|S|$.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), §3, p. 8

import Mathlib
import Definitions.Def_OnlineShadow_LogRate_slotProj

namespace OnlineShadow.LogRate

/-- The **number operator** `N ≜ ∑ᵢ Qᵢ` with `Qᵢ = 1 − Pᵢ` (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), §3, p.8): it counts the copies that
are not in the purification `|ψ⟩`. -/
def numberOp {d r : ℕ} (ψ : Fin d × Fin r → ℂ) (n : ℕ) :
    Matrix (Fin n → Fin d × Fin r) (Fin n → Fin d × Fin r) ℂ :=
  ∑ i : Fin n, (1 - slotProj ψ n i)

end OnlineShadow.LogRate


