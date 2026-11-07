-- Prove2me | Definitions.Def_QuantumLTF_Membership_memOracle
-- name    : QuantumLTF_Membership_memOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:37:36.666187+00:00
-- url     : https://prove2.me/theorems/62963a60-72c3-4230-af61-086d65e53ccc
-- title:
--   The coherent membership oracle $O_{f_{w,\theta}}$
-- statement:
--   For a $\pm1$-valued $f$, write $\bar f=(1-f)/2\in\{0,1\}$. The coherent membership oracle of $f_{w,\theta}$ is the unitary
--   $$O_{f_{w,\theta}}:\ |y\rangle|b\rangle\longmapsto|y\rangle|b\oplus\bar f_{w,\theta}(y)\rangle,$$
--   where $y$ is an address of format $(\ell,f)$ and $b$ a bit. It is the only way a circuit in this mission accesses the target.
--
--   **Formalization Note** The first $n\ell$ wires are the address and the last wire is the target. The matrix is a permutation matrix whose column $z$ is the image of $|z\rangle$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Eq. (1), p. 4 (PDF p. 5); p. 24 (PDF p. 25)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_addrOf

namespace QuantumLTF.Membership

open QAlgorithms

/-- **The coherent membership oracle `O_f`.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Eq. (1), p. 4 (PDF p. 5), and p. 24 (PDF p. 25):
`O_f : |y⟩|b⟩ ↦ |y⟩|b ⊕ f̄(y)⟩` with `f̄ := (1 − f)/2 ∈ {0, 1}`, here for `f = f_{w,θ}`.

**Formalization Note.** Wires `0, …, n*ℓ−1` are the address, read by `addrOf n ℓ f`, and the last
wire is the target. A permutation matrix; column `z` is the image of `|z⟩`. `f̄` is `1` exactly when
`f = −1`. -/
noncomputable def memOracle (n ℓ f : ℕ) (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) :
    Matrix (Qubits (n * ℓ + 1)) (Qubits (n * ℓ + 1)) ℂ :=
  Matrix.of fun y z =>
    if y = Fin.snoc (α := fun _ => Bool) (Fin.init z)
        (xor (z (Fin.last _)) (decide (ltf w θ (addrOf n ℓ f (Fin.init z)) = -1)))
    then 1 else 0

end QuantumLTF.Membership


