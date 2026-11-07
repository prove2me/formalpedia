-- Prove2me | Definitions.Def_QPACLarge_Wmap
-- name    : QPACLarge_Wmap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:07:21.540073+00:00
-- url     : https://prove2.me/theorems/c8a8e5a4-af84-456d-8ad6-aba84eaeeb9e
-- title:
--   The isometry $W|\ell\rangle=H^{\otimes r}|J(\ell)\rangle$
-- statement:
--   The linear map $W$ from the label space (basis $\{|\ell\rangle : \ell \in \{\bot\} \cup \{0,1\}^n\}$) to the seed space (basis $\{|a\rangle : a \in A\}$) is defined on basis vectors by
--   $$
--   W|\ell\rangle = H^{\otimes r}|J(\ell)\rangle ,
--   $$
--   where $H$ is the one-qubit Hadamard gate and $H^{\otimes r}$ acts on the $r$ seed coordinates. Thus the amplitude of $|a\rangle$ in $W v$ is $\sum_\ell (H^{\otimes r})_{a, J(\ell)}\, v(\ell)$, with $(H^{\otimes r})_{a,y} = \prod_c H_{a_c, y_c}$ and $H_{b,b'} = (-1)^{bb'}/\sqrt2$.
--
--   **Formalization Note** Vectors are amplitude functions; the Hadamard entries are the published `hMat`.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 3.2.1, p.23

import Mathlib
import Definitions.Def_QPACLarge_Jmap
import Definitions.Def_QAlgorithms_Defs_Complexity

namespace QPACLarge

open QAlgorithms QAlgorithms.Complexity

/-- **The isometry `W|ℓ⟩ ≜ H^{⊗r}|J(ℓ)⟩`.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 3.2.1, p.23: "Writing `|ℓ⟩` for the encoded state of an index
`ℓ ∈ {⊥} ∪ {0,1}ⁿ`, we define `W|ℓ⟩ ≜ H^{⊗r}|J(ℓ)⟩`."

`Wmap v` is the image of the vector `v = Σ_ℓ v(ℓ)|ℓ⟩` of the label space: its amplitude at the seed
`a` is `Σ_ℓ (H^{⊗r})_{a, J(ℓ)} v(ℓ)`, where `(H^{⊗r})_{a,y}` is the product over the `r` seed
coordinates of the Hadamard entries `H_{a_c, y_c}` (the published `hMat`,
`H_{b,b'} = (−1)^{bb'}/√2`).

**Formalization Note.** Vectors are amplitude functions; `W` is extended linearly from the basis
`{|ℓ⟩}`. -/
noncomputable def Wmap {n : ℕ} (v : Option (Qubits n) → ℂ) (a : Seed n) : ℂ :=
  ∑ ℓ : Option (Qubits n),
    (hMat a.1 (Jmap n ℓ).1 * (∏ i : Fin n, hMat (a.2.1 i) ((Jmap n ℓ).2.1 i)) *
      ∏ p : {p : Fin n × Fin n // p.1 < p.2}, hMat (a.2.2 p) ((Jmap n ℓ).2.2 p)) * v ℓ

end QPACLarge


