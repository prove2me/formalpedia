-- Prove2me | Definitions.Def_PreprocOWS_Supplement_prgAdv
-- name    : PreprocOWS_Supplement_prgAdv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:11:18.732208+00:00
-- url     : https://prove2.me/theorems/adb9bd20-8b24-423c-8aa6-7f8ab48cd6bd
-- title:
--   Distinguishing advantage of a PRG adversary with advice $|\varphi_R\rangle$
-- statement:
--   For a PRG adversary with run $A_R$ and measurement $\Pi$, advice $|\varphi\rangle$ on $S$ qubits and challenge $y\in\{0,1\}^m$, the acceptance probability is
--   $$
--   \langle\varphi,0^w|\langle y|\,A_R^\dagger\Pi A_R\,|y\rangle|\varphi,0^w\rangle .
--   $$
--   The **distinguishing advantage** for the oracle $R$ is
--   $$
--   \Big|\,\mathbb E_{x}\,\langle\varphi,0^w|\langle R(x)|A_R^\dagger\Pi A_R|R(x)\rangle|\varphi,0^w\rangle-\mathbb E_{r}\,\langle\varphi,0^w|\langle r|A_R^\dagger\Pi A_R|r\rangle|\varphi,0^w\rangle\Big| ,
--   $$
--   with $x$ uniform on $[N]$ (challenge bit $b=0$) and $r$ uniform on $[M]=\{0,1\}^m$ ($b=1$).
--
--   **Formalization Note** The quadratic form is taken as its real part.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Definition 8.1, p.30 (PDF p.33); §8.1, p.31 (PDF p.34)

import Mathlib
import Definitions.Def_PreprocOWS_Supplement_PRGAlg
open Matrix

namespace PreprocOWS.Supplement

open PreprocOWS

/-- The initial state `|φ⟩|y⟩|0^w⟩` of a PRG adversary with advice `φ` and challenge `y`
(arXiv:2610.02101, §8.1, p.31, PDF p.34). -/
def prgInput {S m w : ℕ} (φ : Fin (2 ^ S) → ℂ) (y : Fin m → Bool) : ΩP S m w → ℂ :=
  fun s => if s.2.1 = y ∧ s.2.2 = wsZero w then φ s.1 else 0

/-- The **acceptance probability** `⟨φ, 0^w| ⟨y| A_R† Π A_R |y⟩ |φ, 0^w⟩` of a PRG adversary on
challenge `y` (arXiv:2610.02101, §8.1, p.31, PDF p.34), as the real part of the quadratic form. -/
noncomputable def prgAcc {S T N m w : ℕ} (A : PRGAlg S T N m w) (R : PRGOracle N m)
    (φ : Fin (2 ^ S) → ℂ) (y : Fin m → Bool) : ℝ :=
  let v := prgRun A R *ᵥ prgInput (w := w) φ y
  (star v ⬝ᵥ (A.meas *ᵥ v)).re

/-- The **distinguishing advantage** of a PRG adversary with advice `φ` for the oracle `R`
(arXiv:2610.02101, Definition 8.1, p.30 and §8.1, p.31, PDF pp.33–34):
`| E_x ⟨φ,0^w|⟨R(x)| A_R†ΠA_R |R(x)⟩|φ,0^w⟩ − E_r ⟨φ,0^w|⟨r| A_R†ΠA_R |r⟩|φ,0^w⟩ |`,
with `x` uniform on `[N]` (challenge `b = 0`) and `r` uniform on `[M] = {0,1}^m` (challenge `b = 1`). -/
noncomputable def prgAdv {S T N m w : ℕ} (A : PRGAlg S T N m w) (R : PRGOracle N m)
    (φ : Fin (2 ^ S) → ℂ) : ℝ :=
  |avg (fun x : Fin N => prgAcc A R φ (R x)) - avg (fun r : Fin m → Bool => prgAcc A R φ r)|

end PreprocOWS.Supplement


