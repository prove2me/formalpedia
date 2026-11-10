-- Prove2me | Definitions.Def_OptGaussTomo_stdPurification
-- name    : OptGaussTomo_stdPurification
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:05:44.883282+00:00
-- url     : https://prove2.me/theorems/00605a3c-a327-4128-a817-eedf95f5d310
-- title:
--   The doubled fermionic system and the standard purification $|\psi^{\mathrm{std}}_\rho\rangle$
-- statement:
--   To purify an $m$-mode fermionic state, the system $\mathcal H_m$ and a copy $\tilde{\mathcal H}_m$ are identified with $2m$ qubits, the first $m$ qubits being the system; the doubled Majorana operators are then $\tilde c_j=c_j\otimes I$ and $\tilde c_{2m+j}=P\otimes c_j$ ($j\le 2m$). On $\tilde{\mathcal H}_m$ the basis $|\tilde x\rangle=(-1)^{\gamma(x)}|x\rangle$ is used, where $\gamma(x)=0$ if $|x|\equiv0,1\pmod 4$ and $\gamma(x)=1$ if $|x|\equiv2,3\pmod4$ ($|x|$ the Hamming weight); $T|x\rangle=|\tilde x\rangle$. The **standard purification** of a state $\rho$ is
--
--   $$
--   |\psi^{\mathrm{std}}_\rho\rangle=(\sqrt\rho\otimes I)\sum_{x\in\{0,1\}^m}(-1)^{\gamma(x)}|xx\rangle ,
--   $$
--
--   whose coefficient on $|x\,y\rangle$ is $(\sqrt\rho)_{xy}(-1)^{\gamma(y)}$. $A\otimes B$ denotes the corresponding operator on $2m$ qubits.
--
--   **Formalization Note** $\sqrt\rho$ is the continuous-functional-calculus square root (the positive square root for positive $\rho$).
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), §C.2 p.34 (pdf p.34)

import Mathlib
import Definitions.Def_FermiCap_Gaussian_Majorana

open FermiCap.Gaussian (Qubits Op)
open scoped MatrixOrder

noncomputable section

namespace OptGaussTomo

/-!
# The doubled fermionic system `H_m ⊗ H̃_m ≅ H_{2m}` and the standard purification

Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of bosonic and
fermionic Gaussian states*, arXiv:2607.11847 (held version, sha256 0f7548a2…), §C.2, p.34: "we
take `H̃_m = H_m`, so that `H_m ⊗ H̃_m ≅ (ℂ²)^{⊗m} ⊗ (ℂ²)^{⊗m} ≅ (ℂ²)^{⊗2m} ≅ H_{2m}` … the
Majorana operators of the doubled system … take the form `c̃_j = c_j ⊗ I` for `j ∈ [2m]`,
`c̃_{2m+j} = P ⊗ c_j` for `j ∈ [2m]`. We will now choose the following basis on `H̃_m`,
`|x̃⟩ = (−1)^{γ(x)} |x⟩`, where `γ(x) = 0` if `|x| ≡ 0 or 1 (mod 4)`, `1` if `|x| ≡ 2 or 3 (mod 4)`.
Let `T` be the map that implements the change of basis, `T|x⟩ = |x̃⟩`. … the standard purification
of a state `ρ ∈ S(H_m)` is given by `|ψ^std_ρ⟩ = (√ρ ⊗ I)(∑_x |x x̃⟩) = (√ρ ⊗ I)(∑_x (−1)^{γ(x)} |xx⟩)`."

**Formalization Note.** A basis label `a : Qubits (2m)` of `2m` qubits is split as
`(fstQ a, sndQ a)`: the first `m` qubits are the system `H_m`, the last `m` the purifier `H̃_m`.
With the Jordan–Wigner Majorana operators on `2m` qubits this is exactly the identification
`c̃_j = c_j ⊗ I`, `c̃_{2m+j} = P ⊗ c_j` of the source. `kronQ A B` is `A ⊗ B` in this
identification. `basisChangeT m` is the diagonal sign matrix `T`. `√ρ` is the continuous
functional calculus square root `CFC.sqrt` (for a positive semidefinite `ρ` it is the unique
positive semidefinite square root). The coefficient of `|x y⟩` in `ψ^std_ρ` is
`(√ρ)_{x y} (−1)^{γ(y)}`.
-/

/-- The system part (first `m` qubits) of a `2m`-qubit basis label. -/
def fstQ {m : ℕ} (a : Qubits (2 * m)) : Qubits m := fun k => a ⟨k.val, by omega⟩

/-- The purifier part (last `m` qubits) of a `2m`-qubit basis label. -/
def sndQ {m : ℕ} (a : Qubits (2 * m)) : Qubits m := fun k => a ⟨k.val + m, by omega⟩

/-- `A ⊗ B` on `H_m ⊗ H̃_m ≅ H_{2m}`. -/
def kronQ {m : ℕ} (A B : Op m) : Op (2 * m) :=
  fun a b => A (fstQ a) (fstQ b) * B (sndQ a) (sndQ b)

/-- The sign `(−1)^{γ(x)}`: `−1` iff the Hamming weight `|x| ≡ 2, 3 (mod 4)`. -/
def gammaSign {m : ℕ} (x : Qubits m) : ℂ :=
  if (∑ k, (x k : ℕ)) % 4 = 2 ∨ (∑ k, (x k : ℕ)) % 4 = 3 then -1 else 1

/-- The change of basis `T|x⟩ = (−1)^{γ(x)}|x⟩`. -/
def basisChangeT (m : ℕ) : Op m := Matrix.diagonal gammaSign

/-- The standard purification `|ψ^std_ρ⟩ = (√ρ ⊗ I) ∑_x (−1)^{γ(x)} |xx⟩ ∈ H_{2m}`. -/
def stdPurification {m : ℕ} (ρ : Op m) : Qubits (2 * m) → ℂ :=
  fun a => CFC.sqrt ρ (fstQ a) (sndQ a) * gammaSign (sndQ a)

end OptGaussTomo


