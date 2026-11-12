-- Prove2me | Definitions.Def_TorchFire_CGS_cloneChan
-- name    : TorchFire_CGS_cloneChan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:42:51.917078+00:00
-- url     : https://prove2.me/theorems/57665e7a-f02b-4ba3-9050-f19711cd7de0
-- title:
--   The CGS flame $|K\rangle$ (23) and $\mathrm{Fire.Clone}$ with $\tilde U^O_G=(\mathrm{Fire.Tag}^O)^\dagger U_{O_2}\mathrm{Fire.Tag}^O$ (28), (96)
-- statement:
--   1. **The CGS flame** prepared by $\mathrm{Fire.Gen}^G$ (23): Construction 4.6 with $Y$ left unmeasured, its queries answered through $G$; the workspace returns to zero and the flame is the state of $YU$, $|K\rangle=2^{-r/2}\sum_y|y\rangle|W_y\rangle$.
--   2. **$\mathrm{Fire.Clone}^O(pk,s,F)$** (Construction 4.22 (5), (28), App. A.2 (96)): prepare a new flame on fresh registers by the circuit of Construction 4.6, with each of its two $G$-queries (forward $P$, then inverse $P^{-1}$) replaced by the public procedure $\tilde U^O_G=(\mathrm{Fire.Tag}^O)^\dagger U_{O_2}\mathrm{Fire.Tag}^O$: encode the call into a fresh query register $Z$, apply $\mathrm{Fire.Tag}^O$ to $FZ$ and fresh auxiliary registers, query $O_2$ on $(Z,(Y,R_0,R_1))$ into the answer register, apply $(\mathrm{Fire.Tag}^O)^\dagger$, and uncompute $Z$. The original flame register is returned as $F_0$ and the new one as $F_1$; all other workspace is discarded. On malformed input ($s\ne pk$) two zero registers are returned.
--
--   **Formalization Note** Because $G\circ\mathrm{enc}$ is $P$ and $P^{-1}$ by (22), $\mathrm{Fire.Gen}^G$ is the same unitary as Construction 4.6. The answer register of each $O_2$ call is $G$'s full answer with its ⊥ flag; the new $Y'U'$ and $X'$ are its forward and inverse slots.
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), (23) p.27; Construction 4.22 (3), (5) pp.28–29; (28) p.29; App. A.2 (96) p.81

import Mathlib
import Definitions.Def_TorchFire_CGS_tag
import Definitions.Def_TorchFire_OSS_prepCircuit
import Definitions.Def_TorchFire_Model_traceDist

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS

namespace TorchFire.CGS

variable {mu : ℕ}

/-- **The CGS flame `|K⟩⟨K|`** (23), p.27, prepared by `Fire.Gen^G`: Construction 4.6 with `Y` left
unmeasured and its `P, P⁻¹` queries answered through `G` (by (22), `G(enc(forward, x)) = P(x)` and
`G(enc(inverse, y, u)) = P⁻¹(y, u)`, so the circuit is the same unitary). The workspace `X` returns to
zero and is discarded; the flame is the state of `YU`. -/
noncomputable def flame (ω : Sample mu) : Matrix (KReg mu) (KReg mu) ℂ := prepYU ω.1

/-- The registers of `Fire.Clone^O`: the input flame `F = YU`; for each of the two `G`-calls of
Construction 4.6 a fresh query register `Z` and tag workspace; and the two answer registers `C_1`,
`C_2` of `O_2` (⊥ flag and `G`'s answer slots). The new flame `Y′U′` is the forward slot of `C_1`, and
the new `X′` is the inverse slot of `C_2`. -/
abbrev CloneSpace (mu : ℕ) : Type :=
  KReg mu × (Bits (ell mu) × TagWs mu) × (Bits (ell mu) × TagWs mu) × (ZMod 2 × GAns mu) ×
    (ZMod 2 × GAns mu)

instance (mu : ℕ) : Fintype (CloneSpace mu) := inferInstance
instance (mu : ℕ) : DecidableEq (CloneSpace mu) := inferInstance

/-- `Fire.Tag^O` applied to `F Z_i (aux)_i` inside the clone registers (call `i ∈ {1, 2}`). -/
noncomputable def tagCall (ω : Sample mu) (i : Fin 2) : Matrix (CloneSpace mu) (CloneSpace mu) ℂ :=
  liftOn (fun s : CloneSpace mu =>
      if i = 0 then ((s.1, s.2.1.1, s.2.1.2), (s.2.2.1, s.2.2.2)) else
        ((s.1, s.2.2.1.1, s.2.2.1.2), (s.2.1, s.2.2.2)))
    (tag ω)

/-- **The unitary of `Fire.Clone^O`** (Construction 4.22 (5), pp.28–29; (28) and App. A.2 (96),
p.81): Construction 4.6 on fresh registers, with each `G`-query replaced by
`Ũ^O_G = (Fire.Tag^O)† U_{O_2} Fire.Tag^O`:

1. `H^{⊗n}` on `X′`;
2. forward call: compute `Z_1 = enc(forward, x′)`; `Fire.Tag^O` on `F Z_1 (aux)_1`; query `O_2` on
   `(Z_1, (Y, R_0, R_1))` into `C_1`; `(Fire.Tag^O)†`; uncompute `Z_1`;
3. inverse call: compute `Z_2 = enc(inverse, y′, u′)`; `Fire.Tag^O`; query `O_2` into `C_2`
   (whose inverse slot is `X′`); `(Fire.Tag^O)†`; uncompute `Z_2`. -/
noncomputable def cloneU (ω : Sample mu) : Matrix (CloneSpace mu) (CloneSpace mu) ℂ :=
  let h := hadOn fun s : CloneSpace mu =>
    (s.2.2.2.2.2.2.1, (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2.1, s.2.2.2.2.2.2.2))
  let z1 := basisMat fun s : CloneSpace mu =>
    (s.1, (s.2.1.1 + enc (.forward s.2.2.2.2.2.2.1), s.2.1.2), s.2.2)
  let o1 := basisMat fun s : CloneSpace mu =>
    (s.1, s.2.1, s.2.2.1,
      s.2.2.2.1 + encBot (O2 ω (s.2.1.1, (s.1.1, s.2.1.2.1.2.2, s.2.1.2.2.2.2))), s.2.2.2.2)
  let z2 := basisMat fun s : CloneSpace mu =>
    (s.1, s.2.1, (s.2.2.1.1 + enc (.inverse s.2.2.2.1.2.1.1 s.2.2.2.1.2.1.2), s.2.2.1.2), s.2.2.2)
  let o2 := basisMat fun s : CloneSpace mu =>
    (s.1, s.2.1, s.2.2.1, s.2.2.2.1,
      s.2.2.2.2 + encBot (O2 ω (s.2.2.1.1, (s.1.1, s.2.2.1.2.1.2.2, s.2.2.1.2.2.2.2))))
  let T1 := tagCall ω 0
  let T2 := tagCall ω 1
  z2 * T2ᴴ * o2 * T2 * z2 * z1 * T1ᴴ * o1 * T1 * z1 * h

/-- The zero state of the clone workspace. -/
def cloneWs0 : (Bits (ell mu) × TagWs mu) × (Bits (ell mu) × TagWs mu) × (ZMod 2 × GAns mu) ×
    (ZMod 2 × GAns mu) := ((0, tagWs0), (0, tagWs0), 0, 0)

/-- **`Fire.Clone^O(pk, s, F)` with `s = pk`** as a channel `F ↦ F_0 F_1` (Construction 4.22 (5)):
the input flame and the fresh zero registers go through `cloneU`; the original flame register is
returned as `F_0`, the newly prepared flame `Y′U′` as `F_1`; all remaining workspace is discarded. -/
noncomputable def cloneChan (ω : Sample mu) (ρ : Matrix (KReg mu) (KReg mu) ℂ) :
    Matrix (KReg mu × KReg mu) (KReg mu × KReg mu) ℂ :=
  let E : Matrix (CloneSpace mu) (KReg mu) ℂ := basisMat fun f => (f, cloneWs0)
  traceOutVia
    (fun p : (KReg mu × KReg mu) ×
        ((Bits (ell mu) × TagWs mu) × (Bits (ell mu) × TagWs mu) ×
          (ZMod 2 × Bits (n mu) × ZMod 2) × (ZMod 2 × GAns mu)) =>
      (p.1.1, p.2.1, p.2.2.1, (p.2.2.2.1.1, p.1.2, p.2.2.2.1.2), p.2.2.2.2))
    (conjMat (cloneU ω) (conjMat E ρ))

/-- **`Fire.Clone^O(pk, s, F)`** (Construction 4.22 (5)): on malformed input (`s ≠ pk`) it returns
two zero registers of the prescribed flame size. -/
noncomputable def cloneKey (ω : Sample mu) (pk s : Bits (hl mu))
    (ρ : Matrix (KReg mu) (KReg mu) ℂ) : Matrix (KReg mu × KReg mu) (KReg mu × KReg mu) ℂ :=
  if s = pk then cloneChan ω ρ else Matrix.trace ρ • ketbra (ket (0, 0))

end TorchFire.CGS


