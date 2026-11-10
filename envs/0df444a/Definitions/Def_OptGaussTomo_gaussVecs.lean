-- Prove2me | Definitions.Def_OptGaussTomo_gaussVecs
-- name    : OptGaussTomo_gaussVecs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:05:56.870339+00:00
-- url     : https://prove2.me/theorems/c836edc8-498c-4909-a0c1-fb3ef5378fac
-- title:
--   Pure fermionic Gaussian state vectors $\mathcal G^\pm_m$ and reference vectors
-- statement:
--   For $s\in\{+,-\}$, $\mathcal G^s_m$ is the set of unit vectors $\phi\in(\mathbb C^2)^{\otimes m}$ such that $|\phi\rangle\langle\phi|$ is a fermionic Gaussian state and $P\phi=s\,\phi$, where $P=Z_1\cdots Z_m$ is the parity operator: the even ($+$) and odd ($-$) pure Gaussian states. $\mathcal G_m=\mathcal G^+_m\cup\mathcal G^-_m$ is the set of all pure Gaussian states (each has definite parity). The reference vectors are $\psi^+=|0\cdots0\rangle$ and $\psi^-=|10\cdots0\rangle$; every element of $\mathcal G^\pm_m$ is $U\psi^\pm$ for a Gaussian unitary $U$, up to a phase.
--
--   **Formalization Note** Vectors rather than rays are used; all quantities in the mission are phase invariant. The paper fixes highest-weight vectors as references (p.33); since Gaussian unitaries act transitively on $\mathcal G^\pm_m$, any reference gives the same invariant measure. The odd reference needs $m\ge1$, which every statement using it assumes.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), §C.1 p.33 (pdf p.33), definition of G_m, G±_m

import Mathlib
import Definitions.Def_FermiCap_Gaussian_States

open FermiCap.Gaussian (Qubits Op parity IsEvenGaussian)

namespace OptGaussTomo

/-!
# Pure fermionic Gaussian state vectors of a given parity, `G^±_m`

Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of bosonic and
fermionic Gaussian states*, arXiv:2607.11847 (held version, sha256 0f7548a2…), §C.1, p.33: "A
pure state in `H_m` is Gaussian if it is the nondegenerate ground state of a quadratic
Hamiltonian of the form (C.2). We write `G_m` for the set of pure Gaussian states, and `G⁺_m` and
`G⁻_m` for the subsets of even- and odd-parity Gaussian states, respectively." The parity operator
is `P ↦ Z₁Z₂⋯Z_m` (p.33).

`gaussVecs m true` is `G⁺_m` and `gaussVecs m false` is `G⁻_m`, as sets of unit vectors in
`ℂ^{Qubits m}`; `gaussRef m s` is a reference vector of `G^s_m`.

**Formalization Note.** A unit vector `ϕ` is a pure Gaussian state iff `|ϕ⟩⟨ϕ|` is an even
Gaussian state in the sense of the published `FermiCap.Gaussian.IsEvenGaussian` (see
`OptGaussTomo.fermiGauss`); a rank-one even Gaussian state is a Gaussian unitary applied to a
basis state, i.e. a nondegenerate ground state of (C.2). Vectors (not rays) are used: `ϕ` and
`e^{iθ}ϕ` are both members, and every quantity in this mission is phase invariant. Every pure
Gaussian state has a definite parity, so `G_m = G⁺_m ∪ G⁻_m`. The reference vectors are the basis
states `|0…0⟩` (even) and `|10…0⟩` (odd; first qubit occupied); both are Gaussian (ground states of
`∑_j ±N_j`). The source instead fixes highest-weight vectors `|ψ^±_m⟩` (p.33); since the Gaussian
unitaries act transitively on `G^±_m`, any reference gives the same invariant measure. The odd
reference needs `m ≥ 1`, which every statement using it assumes.
-/

/-- The basis vector `|x⟩` of `ℂ^{Qubits m}`. -/
def basisVec {m : ℕ} (x : Qubits m) : Qubits m → ℂ := Pi.single x 1

/-- The pure Gaussian state vectors of parity `s` (`true`: even, `false`: odd). -/
def gaussVecs (m : ℕ) (s : Bool) : Set (Qubits m → ℂ) :=
  {ϕ | star ϕ ⬝ᵥ ϕ = 1 ∧ IsEvenGaussian (Matrix.vecMulVec ϕ (star ϕ)) ∧
    (parity m).mulVec ϕ = (if s then (1 : ℂ) else -1) • ϕ}

/-- Reference vectors: `|0…0⟩` for `s = true`, `|10…0⟩` for `s = false`. -/
def gaussRef (m : ℕ) (s : Bool) : Qubits m → ℂ :=
  if s then basisVec (fun _ => 0) else basisVec (fun k => if k.val = 0 then 1 else 0)

end OptGaussTomo


