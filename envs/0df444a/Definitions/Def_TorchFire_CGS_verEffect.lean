-- Prove2me | Definitions.Def_TorchFire_CGS_verEffect
-- name    : TorchFire_CGS_verEffect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:42:10.719502+00:00
-- url     : https://prove2.me/theorems/0df2a9ad-7743-4de2-9bcf-784595e74520
-- title:
--   The CGS verification effect $B$ derived from $\mathrm{Fire.Hash}$ and $\mathrm{Fire.Ver}$
-- statement:
--   **$\mathrm{Fire.Ver}^O(pk,s,F)$** (Construction 4.22 (4), with $\mathrm{Fire.Hash}$, Remark 4.21): reject unless $s=pk$; otherwise sample $z\leftarrow Z$ uniformly; measure $Y$ (outcome $y$), initialize $Z$ to $|z\rangle$ and the auxiliary registers to zero, apply $\mathrm{Fire.Tag}^O$, measure $R_0,R_1$, query $N(z,(y,\tau_0,\tau_1))$ to obtain $\eta$, and return $V(z,\eta)$ ($V$ returns $0$ on $\eta=\perp$).
--
--   The accepting effect of this procedure is
--   $$B=|Z|^{-1}\sum_z\sum_yP_yJ_z^\dagger\,\mathrm{Tag}^\dagger\,\Pi^{\mathrm{acc}}_z\,\mathrm{Tag}\,J_zP_y,$$
--   with $P_y$ the projector onto $Y=y$, $J_z$ the attachment of $|z\rangle$ and the zero workspace, and $\Pi^{\mathrm{acc}}_z$ the diagonal projector onto the measured values on which the final classical step accepts. This is the operator $B$ of Remark 4.26 (31), derived from the procedure rather than postulated.
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Construction 4.22 (4) p.28; Remark 4.21 p.28; Remark 4.26 (31) p.29

import Mathlib
import Definitions.Def_TorchFire_CGS_tag
import Definitions.Def_TorchFire_Model_traceDist

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS

namespace TorchFire.CGS

variable {mu : ℕ}

/-- The final classical step of `Fire.Ver` (Construction 4.22 (4), p.28, with `Fire.Hash`, Remark
4.21, p.28): from the measured `y, R_0, R_1` form the tag, query `N(z, (y, τ_0, τ_1))` to obtain `η`
(⊥ on a malformed tag) and return `V(z, η)`; `V` returns `0` on the malformed input `η = ⊥`. -/
noncomputable def verBit (ω : Sample mu) (z : Bits (ell mu)) (p : TagIn mu) : Bool :=
  match Nh ω (z, p) with
  | some η => decide (Vh ω (z, η) = 1)
  | none => false

/-- Attaching the request `|z⟩_Z` and the zero tag workspace to a flame: `|y, u⟩ ↦ |y, u, z, 0⟩`. -/
def attachZ (z : Bits (ell mu)) : Matrix (TagSpace mu) (KReg mu) ℂ :=
  basisMat fun f => (f, z, tagWs0)

/-- **The verification effect `B` of CGS fire** (Construction 4.22 (4), p.28; Remark 4.26 (31),
p.29), derived from the procedure: sample `z ← Z` uniformly; `Fire.Hash^O(F, z)` measures `Y`
(outcome `y`), initializes `Z` to `|z⟩` and the auxiliary registers to zero, applies `Fire.Tag^O`,
measures `R_0, R_1`, and queries `N`; then `V(z, η)` is returned. The accepting effect is

  `B = |Z|⁻¹ Σ_z Σ_y P_y J_z† Tag† Π^{acc}_z Tag J_z P_y`,

with `P_y` the projector onto `Y = y`, `J_z` the attachment, and `Π^{acc}_z` the diagonal projector
onto the basis values `(y, R_0, R_1)` on which the classical final step accepts.

(Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held
version sha256 4e43d2f2…afd593.) -/
noncomputable def verEffect (ω : Sample mu) : Matrix (KReg mu) (KReg mu) ℂ :=
  ((Fintype.card (Bits (ell mu)) : ℂ))⁻¹ •
    ∑ z : Bits (ell mu), ∑ y : Bits (r mu),
      let Py : Matrix (KReg mu) (KReg mu) ℂ :=
        Matrix.diagonal fun f => if f.1 = y then 1 else 0
      let Pacc : Matrix (TagSpace mu) (TagSpace mu) ℂ :=
        Matrix.diagonal fun s => if verBit ω z (tagOf s) then 1 else 0
      Py * (attachZ z)ᴴ * (tag ω)ᴴ * Pacc * tag ω * attachZ z * Py

/-- **`Fire.Ver^O(pk, s, ·)`'s effect** (Construction 4.22 (4)): reject unless `s = pk`. -/
noncomputable def verEffectKey (ω : Sample mu) (pk s : Bits (hl mu)) :
    Matrix (KReg mu) (KReg mu) ℂ :=
  if s = pk then verEffect ω else 0

end TorchFire.CGS


