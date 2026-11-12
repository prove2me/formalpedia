-- Prove2me | Definitions.Def_TorchFire_OSS_Theta
-- name    : TorchFire_OSS_Theta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:35:15.378518+00:00
-- url     : https://prove2.me/theorems/30e766fa-38b5-427f-ad74-7fb1c3d11859
-- title:
--   The projectors of Lemma 4.8 and the public coset test of Remark 4.9
-- statement:
--   For a key $y$ of Construction 4.2: the coset projector $\Theta_y=\sum_{u\in W_y}|u\rangle\langle u|$, the dual projector $Q_y=\sum_{v\in S_y^\perp}|v\rangle\langle v|$, $Q'_y=H^{\otimes k}Q_yH^{\otimes k}$, and $\Pi_y=Q'_y\Theta_y$ (Lemma 4.8).
--
--   The **public coset test** (Remark 4.9, used by $\mathrm{TF.Ver}$ on every anchor component) measures $\{\Theta_y,I-\Theta_y\}$ with the predicate $1[P^{-1}(y,u)\ne\perp]$, applies $H^{\otimes k}$ on acceptance, and measures $\{Q_y,I-Q_y\}$ with $D(y,\cdot)$; it accepts iff both outcomes are $1$. The module defines its accepting Kraus operator, computed from the oracles $P^{-1}$ and $D$.
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Lemma 4.8 p.21; Remark 4.9 p.21; Construction 7.4 step 4 (i) p.53

import Mathlib
import Definitions.Def_TorchFire_OSS_OneSample
import Definitions.Def_TorchFire_Model_basisMat

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model

namespace TorchFire.OSS

variable {lam : ℕ}

/-- **The coset membership projector** `Θ_y = Σ_{u ∈ W_y} |u⟩⟨u|` (Lemma 4.8, p.21;
Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held
version sha256 4e43d2f2…afd593). -/
noncomputable def Theta (ω : OneSample lam) (y : Bits (r lam)) :
    Matrix (Bits (k lam)) (Bits (k lam)) ℂ :=
  by classical exact Matrix.diagonal fun u => if InCoset ω y u then 1 else 0

/-- **The dual membership projector** `Q_y = Σ_{v ∈ S_y^⊥} |v⟩⟨v|` (Lemma 4.8, p.21), with
`S_y^⊥ = {v : vᵀ A_y = 0}`. -/
noncomputable def Qproj (ω : OneSample lam) (y : Bits (r lam)) :
    Matrix (Bits (k lam)) (Bits (k lam)) ℂ :=
  by classical exact Matrix.diagonal fun v => if Matrix.vecMul v (Amat ω y) = 0 then 1 else 0

/-- `Q′_y = H^{⊗k} Q_y H^{⊗k}` (Lemma 4.8, p.21). -/
noncomputable def Qprime (ω : OneSample lam) (y : Bits (r lam)) :
    Matrix (Bits (k lam)) (Bits (k lam)) ℂ :=
  hadamard (k lam) * Qproj ω y * hadamard (k lam)

/-- `Π_y := Q′_y Θ_y` (11), p.21. -/
noncomputable def PiY (ω : OneSample lam) (y : Bits (r lam)) :
    Matrix (Bits (k lam)) (Bits (k lam)) ℂ :=
  Qprime ω y * Theta ω y

/-- **The accepting Kraus operator of the public coset test** (Remark 4.9, p.21; the anchor test of
Construction 7.4, step 4 (i), p.53): measure `{Θ_y, I − Θ_y}` using the predicate
`1[P⁻¹(y, u) ≠ ⊥]`; on acceptance apply `H^{⊗k}` and measure `{Q_y, I − Q_y}` using `D(y, ·)`;
accept iff both outcomes are `1`. The membership projector here is computed from the oracle
`P⁻¹`, the dual one from `D`; the accepting effect of the test is `Kᴴ K`. -/
noncomputable def cosetTestKraus (ω : OneSample lam) (y : Bits (r lam)) :
    Matrix (Bits (k lam)) (Bits (k lam)) ℂ :=
  by classical exact
  Matrix.diagonal (fun v => if D ω (y, v) = 1 then 1 else 0) * hadamard (k lam) *
    Matrix.diagonal (fun u => if (Pinv ω (y, u)).isSome then 1 else 0)

end TorchFire.OSS


