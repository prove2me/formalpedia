-- Prove2me | Definitions.Def_TorchFire_CGS_tag
-- name    : TorchFire_CGS_tag
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:39:46.029804+00:00
-- url     : https://prove2.me/theorems/0f1899d0-27a7-40a0-8e17-43713fbe2fd0
-- title:
--   The coherent tag circuit $\mathrm{Fire.Tag}^O=T^O_1T^O_0$ (95)
-- statement:
--   **The coherent tag circuit** (App. A.1, (95)). The flame register is $F=YU$; $Z$ holds the query; for $b\in\{0,1\}$, $E_b,\Sigma_b,R_b$ are the signing workspace, the signature and the response. For each $b$ (first $b=0$, then $b=1$):
--
--   1. apply $\hat U^O_b=\sum_y|y\rangle\langle y|_Y\otimes U^O_{y,b}$ to $YUE_b\Sigma_b$ (sign $b$ coherently, without measuring $Y$);
--   2. apply $U_{O_b}$, which reads $(Y,\Sigma_b,Z)$ and writes the response into $R_b$ (a failed signature $|\perp\rangle$ is a malformed input, answered $\perp$);
--   3. apply $(\hat U^O_b)^\dagger$.
--
--   So $T^O_b=(\hat U^O_b)^\dagger U_{O_b}\hat U^O_b$ and $\mathrm{Fire.Tag}^O=T^O_1T^O_0$. The tag is held in $(Y,R_0,R_1)$, and the auxiliary registers are retained so that $(\mathrm{Fire.Tag}^O)^\dagger$ can be applied later.
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), App. A.1, (95), pp.80–81

import Mathlib
import Definitions.Def_TorchFire_CGS_Sample

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS

namespace TorchFire.CGS

/-- The flame register `F = YU` of CGS fire: a verification-key register `Y` (`r` qubits) and a
coset register `U` (`k` qubits) (p.27, (23)). -/
abbrev KReg (mu : ℕ) : Type := Bits (r mu) × Bits (k mu)

/-- The auxiliary registers `E_b, Σ_b, R_b` of one half of the tag circuit (App. A.1, p.80): the
signing workspace, the signature, and the oracle response (with its ⊥ flag). -/
abbrev TagHalf (mu : ℕ) : Type := SignWs mu × Sig mu × (ZMod 2 × Bits (hl mu))

/-- The auxiliary registers of `Fire.Tag^O`: `(E_0, Σ_0, R_0)` and `(E_1, Σ_1, R_1)`. -/
abbrev TagWs (mu : ℕ) : Type := TagHalf mu × TagHalf mu

/-- The registers `Y U Z E_0 Σ_0 R_0 E_1 Σ_1 R_1` of `Fire.Tag^O` (`Z` holds the query). -/
abbrev TagSpace (mu : ℕ) : Type := KReg mu × Bits (ell mu) × TagWs mu

instance (mu : ℕ) : Fintype (KReg mu) := inferInstance
instance (mu : ℕ) : DecidableEq (KReg mu) := inferInstance
instance (mu : ℕ) : Fintype (TagHalf mu) := inferInstance
instance (mu : ℕ) : DecidableEq (TagHalf mu) := inferInstance
instance (mu : ℕ) : Fintype (TagWs mu) := inferInstance
instance (mu : ℕ) : DecidableEq (TagWs mu) := inferInstance
instance (mu : ℕ) : Fintype (TagSpace mu) := inferInstance
instance (mu : ℕ) : DecidableEq (TagSpace mu) := inferInstance

variable {mu : ℕ}

/-- The zero state of the tag workspace (all records `0`, `Σ_b = |⊥⟩`, `R_b = 0`). -/
def tagWs0 : TagWs mu := ((0, none, 0), (0, none, 0))

/-- The selected half `(E_b, Σ_b, R_b)`. -/
def half (b : ZMod 2) (w : TagWs mu) : TagHalf mu := if b = 0 then w.1 else w.2

/-- Write back the selected half. -/
def setHalf (b : ZMod 2) (w : TagWs mu) (x : TagHalf mu) : TagWs mu :=
  if b = 0 then (x, w.2) else (w.1, x)

/-- `Û^O_b` applied to `Y U E_b Σ_b` inside the tag registers (App. A.1, p.80). -/
noncomputable def hatU (ω : Sample mu) (b : ZMod 2) : Matrix (TagSpace mu) (TagSpace mu) ℂ :=
  liftOn (fun s : TagSpace mu =>
      ((s.1.1, (s.1.2, (half b s.2.2).1, (half b s.2.2).2.1)),
        (s.2.1, (half b s.2.2).2.2, half (1 - b) s.2.2)))
    (signUY ω.1 b)

/-- `U_{O_b}` on `Y Σ_b Z R_b` (App. A.1, p.80): it uses `(Y, Σ_b, Z)` as input and XORs the response
`O_b(y, σ_b, z)` into `R_b`; a failed signature `Σ_b = |⊥⟩` is a malformed input, answered `⊥`. -/
noncomputable def queryOb (ω : Sample mu) (b : ZMod 2) : Matrix (TagSpace mu) (TagSpace mu) ℂ :=
  basisMat fun s : TagSpace mu =>
    let h := half b s.2.2
    let ans : Option (Bits (hl mu)) :=
      match h.2.1 with
      | some u => Ob ω b (s.1.1, u, s.2.1)
      | none => none
    (s.1, s.2.1, setHalf b s.2.2 (h.1, h.2.1, h.2.2 + encBot ans))

/-- `T^O_b = (Û^O_b)† U_{O_b} Û^O_b` (95), p.81. -/
noncomputable def tagHalfOp (ω : Sample mu) (b : ZMod 2) : Matrix (TagSpace mu) (TagSpace mu) ℂ :=
  (hatU ω b)ᴴ * queryOb ω b * hatU ω b

/-- **The coherent tag circuit `Fire.Tag^O = T^O_1 T^O_0`** (95), App. A.1, pp.80–81
(Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held
version sha256 4e43d2f2…afd593). For each `b = 0, 1`: sign `b` coherently with the flame's coset
register, controlled on the unmeasured key register `Y` (`Û^O_b`); query `O_b` on `(Y, Σ_b, Z)` into
`R_b`; uncompute the signature. The tag is held in `(Y, R_0, R_1)`. Only the public oracles `D`
(inside the signer), `O_0`, `O_1` are used. -/
noncomputable def tag (ω : Sample mu) : Matrix (TagSpace mu) (TagSpace mu) ℂ :=
  tagHalfOp ω 1 * tagHalfOp ω 0

/-- The tag `(Y, R_0, R_1)` held in the tag registers. -/
def tagOf (s : TagSpace mu) : TagIn mu := (s.1.1, s.2.2.1.2.2, s.2.2.2.2.2)

end TorchFire.CGS


