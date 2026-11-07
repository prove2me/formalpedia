-- Prove2me | Definitions.Def_QuantumLTF_Membership_addrOf
-- name    : QuantumLTF_Membership_addrOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:35:25.858446+00:00
-- url     : https://prove2.me/theorems/6d71ecb7-81d7-4211-804c-4f23373fa680
-- title:
--   The point of $\mathbb R^n$ denoted by an address string
-- statement:
--   An address string $y$ of $n\ell$ bits denotes the point of $\mathbb R^n$ whose coordinate $i$ is $\mathrm{fp}_{\ell,f}$ of sub-register $i$ of $y$. The membership oracle is addressed through this map.
--
--   **Formalization Note** The map is fixed and $(\ell,f)$ is the only freedom. A free map from strings to $\mathbb R^n$ would provide arbitrary real query points at no gate cost.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Eq. (40), p. 24 (PDF p. 25)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_splitReg

namespace QuantumLTF.Membership

open QAlgorithms

/-- **The point of `Rⁿ` an address string denotes.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Eq. (40), p. 24 (PDF p. 25): the query
address register holds a point `y` in reversible fixed-point arithmetic. Coordinate `i` of `addrOf n ℓ f y`
is `fpVal ℓ f` of wires `i * ℓ, …, i * ℓ + ℓ − 1`.

**Formalization Note.** The address map is fixed, and `(ℓ, f)` is the only freedom. A free map from
strings to `Rⁿ` would buy arbitrary real points at unit cost. -/
noncomputable def addrOf (n ℓ f : ℕ) (y : Qubits (n * ℓ)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => fpVal ℓ f (splitReg n ℓ y i)

end QuantumLTF.Membership


