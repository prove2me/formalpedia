-- Prove2me | Definitions.Def_CompNonlocal_Certificate_acc
-- name    : CompNonlocal_Certificate_acc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:04.856103+00:00
-- url     : https://prove2.me/theorems/7c643034-e825-41b6-9d11-bb15527414b2
-- title:
--   Acceptance probability of the single-copy game
-- statement:
--   For players $A',B'$ and a two-qubit state $\omega$:
--   $$\mathrm{acc}_\kappa(A',B',\omega)=\sum_{o=(x,y)}\sum_{a,b}\operatorname{Tr}\big((A'^{\,x}_a\otimes B'^{\,y}_b)\,\omega\big)\cdot\Pr[o,\ \mathrm{Val}\text{ accepts }(a,b,x,y)],$$
--   the probability that the verifier accepts when Alice and Bob act on the two halves of **one** copy of $\omega$ ("with their correlations retained"). For the honest players on $\rho(u)$ this is $h_u$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definitions 9, 11, pp.24–25

import Mathlib
import Definitions.Def_CompNonlocal_Certificate
import Definitions.Def_CompNonlocal_ICirc_qubitEffect

set_option autoImplicit false

open scoped Kronecker

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The acceptance probability of the single-copy certification game. Głuch, Morimae, *From
Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027
submission, sha256 e245edd7…), Definition 9, pp.24–25 with `k = 1` and Definition 11, p.25: the
verifier generates `(x, y, td)`, sends `x` to Alice and `y` to Bob; Alice runs `A'` on `x` and her
qubit, Bob runs `B'` on `y` and his qubit, both qubits being the two halves of one copy of the
two-qubit state `ω` ("with their correlations retained", p.7); the verifier runs `Val` on the
answers, the questions and `td`, and the game accepts when Val accepts.

**Formalization Note** `acc c κ A' B' ω = Σ_{o, a, b} Re Tr((A^x_a ⊗ B^y_b) ω) · Pr[o, Val accepts a, b]`,
with `x ++ y = o`, `A^x_a`, `B^y_b` the players' qubit effects (Alice's qubit the first tensor
factor), and the verifier's part `valAccept`. -/
noncomputable def Certificate.acc (c : Certificate) (κ : ℕ) (A' B' : Family)
    (ω : Matrix (Bool × Bool) (Bool × Bool) ℂ) : ℝ :=
  ∑ o : Bits (c.Qg κ).outC.length, ∑ a : Bits (A' κ).outC.length,
    ∑ b : Bits (B' κ).outC.length,
      ((((A' κ).qubitEffect ((List.ofFn o).take (c.lx κ)) (fun t => decide (t = List.ofFn a))) ⊗ₖ
          ((B' κ).qubitEffect ((List.ofFn o).drop (c.lx κ)) (fun t => decide (t = List.ofFn b)))) *
          ω).trace.re *
        c.valAccept κ (List.ofFn a) (List.ofFn b) (List.ofFn o)

end CompNonlocal


