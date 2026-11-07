-- Prove2me | Definitions.Def_CompNonlocal_Certificate_prepared
-- name    : CompNonlocal_Certificate_prepared
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:23.200177+00:00
-- url     : https://prove2.me/theorems/7626a391-de94-4f7d-a815-3415b0643766
-- title:
--   The prepared state of the §8.1 receiver
-- statement:
--   The receiver of the ASP built from a certificate, on message $x$: prepares $\psi^-_{AQ}=(|01\rangle-|10\rangle)/\sqrt2$, applies Alice's honest circuit $U_{A,x}$ to $A$ and fresh ancillas, leaves $Q$ untouched, and measures every register other than $Q$, obtaining the complete record $z$. This is the unnormalized state $\tilde\zeta_{x,z}$ of $Q$ jointly with the record $z$; its trace is $\Pr[z\mid x]$.
--
--   **Formalization Note** $\tilde\zeta_{x,z}=|\varphi_z\rangle\langle\varphi_z|$ with $\varphi_z(s)=\sum_q\psi^-(q,s)\,\langle z|U_A|x,q,0\rangle$; meaningful when Alice's circuit reads her qubit.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §8.1, p.35

import Mathlib
import Definitions.Def_CompNonlocal_Certificate
import Definitions.Def_CompNonlocal_singletAmp

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The unnormalized prepared state of the receiver of the §8.1 construction. Głuch, Morimae, *From
Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027
submission, sha256 e245edd7…), §8.1, p.35: "ASP.Rec(msg_S). Given msg_S = x: 1. Prepare a singlet
ψ⁻_{AQ} := (|01⟩ − |10⟩)/√2. 2. Apply U_{A,x} to A and fresh clean ancillas, leaving Q untouched.
3. Measure every register other than Q in the computational basis. Let a be the complete
measurement record and set msg_R := a. Output (msg_R, ζ), where ζ is the prepared state in register
Q."

**Formalization Note** For the record `z` (the outcome of every wire of Alice's honest circuit, whose
first quantum-input wire holds `A`), the unnormalized state of `Q` is `|φ_z⟩⟨φ_z|` with
`φ_z(s) = Σ_q ψ⁻(q, s) · ⟨z| U_A |x, q, 0⟩`; its trace is `Pr[record z | x]`. The singlet's first
factor is `A`, its second `Q`. The construction requires Alice's honest circuit to read her qubit,
i.e. `1 ≤ (c.A κ).nq`; the statements using it assume this. -/
noncomputable def Certificate.prepared (c : Certificate) (κ : ℕ) (x : Str)
    (z : Bits (c.A κ).width) : Matrix Bool Bool ℂ :=
  Matrix.of fun s s' =>
    ∑ q : Bool, ∑ q' : Bool,
      singletAmp (q, s) * star (singletAmp (q', s')) *
        (c.A κ).unitary z ((c.A κ).feed x (fun _ : Fin 1 => q)) *
        star ((c.A κ).unitary z ((c.A κ).feed x (fun _ : Fin 1 => q')))

end CompNonlocal


