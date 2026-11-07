-- Prove2me | Definitions.Def_QuantumLTF_Membership_readFp
-- name    : QuantumLTF_Membership_readFp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:33:27.656005+00:00
-- url     : https://prove2.me/theorems/6fde932d-4429-41ed-ba7c-fff6304bffc2
-- title:
--   The fixed-point number on designated output wires
-- statement:
--   Given an ordered tuple $e$ of $\ell$ distinct wires of an $m$-wire register and a measured string $z$, the read-out is $\mathrm{fp}_{\ell,f}$ of the bits of $z$ on the wires $e_0,\dots,e_{\ell-1}$.
--
--   **Formalization Note** Outputs are read through this map and not by a free decoding function, which would hide classical work outside the gate count.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, p. 33 (PDF p. 34)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_fpVal

namespace QuantumLTF.Membership

open QAlgorithms

/-- **The fixed-point number on designated output wires.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, p. 33 (PDF p. 34): the output
hypothesis is represented by fixed-point numbers. `readFp e f z` is `fpVal ℓ f` of the bits of the
measured string `z` on the wires `e 0, …, e (ℓ−1)` (`e 0` most significant).

**Formalization Note.** Outputs are read by this map and not by a free decoding function, since a free
decoder would hide classical work outside `gateCount`. -/
noncomputable def readFp {ℓ m : ℕ} (e : Fin ℓ ↪ Fin m) (f : ℕ) (z : Qubits m) : ℝ :=
  fpVal ℓ f (z ∘ e)

end QuantumLTF.Membership


