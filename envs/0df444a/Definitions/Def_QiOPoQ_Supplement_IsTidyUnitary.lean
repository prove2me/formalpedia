-- Prove2me | Definitions.Def_QiOPoQ_Supplement_IsTidyUnitary
-- name    : QiOPoQ_Supplement_IsTidyUnitary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:04:34.560838+00:00
-- url     : https://prove2.me/theorems/fac9faea-3d2c-4db6-9e6f-5e25a4bd8f4c
-- title:
--   Tidy unitary circuit families
-- statement:
--   A family is tidy unitary if it is polynomial-size and unitary, every member has $n_{\mathrm{in}}=n_{\mathrm{out}}$ and $n_{\mathrm{anc}}=n_{\mathrm{junk}}$, and for one negligible $\mu$
--
--   $$\big\|(I_{\mathrm{in,anc}}-I_{\mathrm{in}}\otimes|0^{n_{\mathrm{anc}}}\rangle\langle0^{n_{\mathrm{anc}}}|_{\mathrm{anc}})\cdot U_{C_\lambda}\cdot(I_{\mathrm{in}}\otimes|0^{n_{\mathrm{anc}}}\rangle_{\mathrm{anc}})\big\|\le\mu(\lambda)$$
--
--   in operator norm: the circuit returns its ancillas to zero on every input, up to negligible error.
--
--   **Formalization Note** $\mathcal C^{\mathrm{tidy}}_{\mathrm{unitary}}$ is read as the tidy subclass of $\mathcal C_{\mathrm{unitary}}$, as its notation (parallel to $\mathcal C^{\mathrm{anc\text{-}free}}$) and name say, so the unitary condition is part of membership.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §3.1, p.13

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QiOPoQ_chan
import Definitions.Def_QiOPoQ_Supplement_opNorm
import Definitions.Def_QiOPoQ_Supplement_IsUnitaryFam

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAdvFew.PoQOracle

variable {G : GateSet}

/-- `I_in ⊗ |0^{n_anc}⟩⟨0^{n_anc}|_anc`: the projector onto the ancilla register being zero. -/
noncomputable def ancZeroProj (C : Circ G) :
    Matrix (Fin (C.nin + C.nanc) → Bool) (Fin (C.nin + C.nanc) → Bool) ℂ :=
  Matrix.of fun y y' => if y = y' ∧ ∀ j : Fin C.nanc, y (Fin.natAdd C.nin j) = false then 1 else 0

/-- The leakage operator `(I_{in,anc} − I_in ⊗ |0^{n_anc}⟩⟨0^{n_anc}|_anc) · U_C ·
(I_in ⊗ |0^{n_anc}⟩_anc)`. -/
noncomputable def tidyLeak (C : Circ G) :
    Matrix (Fin (C.nin + C.nanc) → Bool) (Fin C.nin → Bool) ℂ :=
  (1 - ancZeroProj C) * circUnitary C * inMat C

/-- **Tidy unitary circuits (§3.1).** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum
Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…),
§3.1, p.13: "We say that C is a tidy unitary circuit if n_in = n_out and n_anc = n_junk, and it
returns its ancilla register to |0^{n_anc}⟩ on every input, up to negligible error. Formally,
∥(I_{in,anc} − I_in ⊗ |0^{n_anc}⟩⟨0^{n_anc}|_anc) · U_C · (I_in ⊗ |0^{n_anc}⟩_anc)∥ ≤ negl(λ),
Here the norm is the operator norm. We write C^{tidy}_{unitary} for the class of such circuits."

A family is tidy unitary if it is polynomial-size and unitary (`IsUnitaryFam`), every member has
`n_in = n_out` and `n_anc = n_junk = n_in + n_anc − n_out`, and for one negligible `μ` the leakage
operator of `C_λ` has operator norm at most `μ(λ)`.

**Formalization Note.** `C^{tidy}_{unitary}` is read, as its notation and name say, as the tidy
subclass of `C_unitary` (parallel to `C^{anc-free}` for the ancilla-free subclass, p.14), so the
unitary condition of §3.1 is part of membership. -/
def IsTidyUnitary (Cf : ℕ → Circ G) : Prop :=
  PolySize Cf ∧ IsUnitaryFam Cf ∧ (∀ n, (Cf n).nin = (Cf n).out.length) ∧
    (∀ n, (Cf n).nanc = (Cf n).nin + (Cf n).nanc - (Cf n).out.length) ∧
    ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n, opNorm (tidyLeak (Cf n)) ≤ μ n

end QiOPoQ.Supplement


