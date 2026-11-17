-- Prove2me | Definitions.Def_QuantumPRC_Supplement_QECC
-- name    : QuantumPRC_Supplement_QECC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:33:44.418876+00:00
-- url     : https://prove2.me/theorems/2a1f46a2-bda8-4476-b321-c419ef02af5f
-- title:
--   Quantum error-correcting codes for $t$-local noise (Definition 3.9)
-- statement:
--   Let $n,m$ be lengths. A **quantum error-correcting code** from $n$ to $m$ qubits is given by matrices $V_\lambda$ (from $n(\lambda)$ to $m(\lambda)$ qubits) and maps $\mathrm{Dec}_\lambda$ from $m(\lambda)$ qubits back to $n(\lambda)$ qubits. Following Definition 3.9 of the paper, it is a **QECC for $t$-local noise** if
--
--   1. $V_\lambda$ is an isometry, $V_\lambda^\dagger V_\lambda=I$, so $\mathrm{Enc}_\lambda(\rho)=V_\lambda\rho V_\lambda^\dagger$;
--   2. $\mathrm{Enc}$ and $\mathrm{Dec}$ are QPT algorithms: one polynomial-time machine prints, from $1^\lambda$, a quantum circuit whose channel is exactly $\mathrm{Enc}_\lambda$, and another one a circuit whose channel is exactly $\mathrm{Dec}_\lambda$;
--   3. for every $t$-local noise family $\mathcal E=\{\mathcal E_\lambda\}$ on $m(\lambda)$ qubits (Definition 3.7) there is a negligible $\nu$ with
--
--   $$
--   \big\|\mathrm{Dec}_\lambda\circ\mathcal E_\lambda\circ\mathrm{Enc}_\lambda-\mathrm{id}_{n(\lambda)}\big\|_\diamond\le\nu(\lambda)\qquad\text{for all }\lambda. \tag{23}
--   $$
--
--   This is the inner code of Construction 5.1.
--
--   **Formalization Note** One pair $(\mathrm{Enc},\mathrm{Dec})$ must work for every $t$-local family, with the negligible function chosen after the family. Circuits are those of the base mission (`QuantumPRC.Circuit`, Clifford+T gates, printed by a polynomial-time Turing machine).
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Definition 3.9 and Eq. (23), p.18; Construction 5.1, p.28

import Mathlib
import Definitions.Def_QuantumPRC_IsLocalNoise
import Definitions.Def_QuantumPRC_OCirc

open Matrix

namespace QuantumPRC.Supplement

/-- **Quantum error-correcting code from `n` to `m` qubits** (the data of Definition 3.9).
Hsieh, Yamada, *Quantum Pseudorandom Error-Correcting Codes*, arXiv:2609.38986 (version of
October 29, 2026, sha256 6901b59d…), Definition 3.9, p.18: "Let `n, m : ℕ → ℕ` be polynomials. […] A
quantum error-correcting code (QECC) for `E` is a pair of QPT algorithms `(Enc, Dec)`, where
`Enc_λ := Enc(1^λ, ·)` maps `n(λ)` qubits to `m(λ)` qubits, and `Dec_λ := Dec(1^λ, ·)` maps `m(λ)`
qubits to `n(λ)` qubits, such that `‖Dec_λ ∘ E_λ ∘ Enc_λ − id_{n(λ)}‖⋄ ≤ negl(λ)` (23) […]. In addition,
we require that `Enc_λ` is a QPT-implementable isometry."

`iso λ` is the matrix of the isometry `Enc_λ` and `dec λ` is the map `Dec_λ`. The conditions are
the predicates `IsIsometry`, `Implementable` and `Corrects`. -/
structure QECC (n m : ℕ → ℕ) where
  iso : ∀ lam, Matrix (Bits (m lam)) (Bits (n lam)) ℂ
  dec : ∀ lam, Superop (Bits (m lam)) (Bits (n lam))

namespace QECC

variable {n m : ℕ → ℕ} (Q : QECC n m)

/-- `Enc_λ` is an isometry: `V_λ† V_λ = I`. -/
def IsIsometry : Prop := ∀ lam, (Q.iso lam)ᴴ * Q.iso lam = 1

/-- `Enc` and `Dec` are QPT algorithms: one polynomial-time machine prints from `1^λ` a circuit whose
channel is exactly `ρ ↦ V_λ ρ V_λ†`, and another one prints a circuit whose channel is exactly
`Dec_λ` (machine model of `QuantumPRC.OCirc`). -/
def Implementable : Prop :=
  ∃ (encC : ∀ lam, Circuit (n lam) (m lam)) (decC : ∀ lam, Circuit (m lam) (n lam)),
    (∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧
      ∀ lam, f (unary lam) = (encC lam).encode) ∧
    (∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧
      ∀ lam, f (unary lam) = (decC lam).encode) ∧
    (∀ lam, (encC lam).channel = conjMap (Q.iso lam)) ∧
    (∀ lam, (decC lam).channel = Q.dec lam)

/-- **Correction condition (23)** for the noise family `E` on `m(λ)` qubits:
`‖Dec_λ ∘ E_λ ∘ Enc_λ − id‖⋄ ≤ negl(λ)`. -/
def Corrects (E : ∀ lam, WildeQIT.QChannel (Bits (m lam)) (Bits (m lam))) : Prop :=
  ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
    diamondDist (fun ρ => Q.dec lam ((E lam).apply (conjMap (Q.iso lam) ρ))) id ≤ ν lam

/-- **A QECC for `t`-local noise** (Definition 3.9 with Definition 3.7, as used in Construction 5.1,
p.28: "a QECC for `t`-local noise that encodes `nL` qubits into `ℓ` qubits"): `Enc` is an isometry,
both algorithms are QPT, and (23) holds for every `t`-local noise family on `m(λ)` qubits.

**Formalization Note.** One pair `(Enc, Dec)` serves every `t`-local family, and the negligible
function is chosen after the family (`∃ negl` after `∀ E`), as in Definition 3.9, which fixes `E`
first. -/
def IsQECCFor (t : ℕ → ℕ) : Prop :=
  Q.IsIsometry ∧ Q.Implementable ∧
    ∀ E : ∀ lam, WildeQIT.QChannel (Bits (m lam)) (Bits (m lam)), IsLocalNoise t m E → Q.Corrects E

end QECC

end QuantumPRC.Supplement


