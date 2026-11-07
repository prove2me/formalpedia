-- Prove2me | Definitions.Def_OnlineShadow_LogRate_slotProj
-- name    : OnlineShadow_LogRate_slotProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:04:18.256439+00:00
-- url     : https://prove2.me/theorems/0589dc9a-b006-45da-a7d9-d2ddf8defe4e
-- title:
--   Projector $P_i=|\psi\rangle\langle\psi|$ on slot $i$
-- statement:
--   Let $\psi$ be the purification of the unknown state, a unit vector on $\mathcal H\otimes\mathcal R$, and $P=|\psi\rangle\langle\psi|$. For a slot $i$ of $n$ copies, $P_i$ is $P$ acting on the $i$-th copy of $(\mathcal H\otimes\mathcal R)^{\otimes n}$, and $Q_i=1-P_i$.
--
--   These projectors define the excitation decomposition: a copy in slot $i$ is "excited" when it lies in the range of $Q_i$.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), §3, p. 8

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_copyOp

namespace OnlineShadow.LogRate

/-- The projector `Pᵢ`: `P = |ψ⟩⟨ψ|` acting on slot `i` of `(H ⊗ R)^{⊗n}`
(Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), §3, p.8: "`P = |ψ⟩⟨ψ|`, `Q = 1 − P`"). Here `ψ` is the purification of the unknown state, a unit
vector on `H ⊗ R`, written as a function on `Fin d × Fin r`; `Pᵢ` is the published
`OptimalSpectrum.Entangled.copyOp i P` (slots numbered from `0`). -/
def slotProj {d r : ℕ} (ψ : Fin d × Fin r → ℂ) (n : ℕ) (i : Fin n) :
    Matrix (Fin n → Fin d × Fin r) (Fin n → Fin d × Fin r) ℂ :=
  OptimalSpectrum.Entangled.copyOp i (fun x y => ψ x * star (ψ y))

end OnlineShadow.LogRate


