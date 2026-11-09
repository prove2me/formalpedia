-- Prove2me | Definitions.Def_DepthOneQExp_cnotPerm
-- name    : DepthOneQExp_cnotPerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:45:21.903216+00:00
-- url     : https://prove2.me/theorems/e49a8d3e-4949-48f7-951f-042438131f33
-- title:
--   $\mathrm{CNOT}_{a,b}$ (control $a$, target $b$) as a permutation of $\{0,1\}^n$
-- statement:
--   The gate $\mathrm{CNOT}_{a,b}$ on an $n$-qubit register is controlled by qubit $a$ and acts on qubit $b$ (Notations, p.6). As a permutation of the computational basis it adds bit $a$ into bit $b$:
--   $$
--   \mathrm{CNOT}_{a,b}:\ x \mapsto x + x_a\, e_b \pmod 2 .
--   $$
--   Its matrix is $P_{\mathrm{CNOT}_{a,b}}$.
--
--   **Formalization Note** Qubit indices are 0-based and taken mod $n$ ("periodic condition", Theorem 2.2). When $a\equiv b \pmod n$ there is no such gate and the permutation is the identity; this junk value is never used, since every gate of the mission has $a\not\equiv b$.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Notations, p.6; Theorem 2.2, p.7

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_bit

namespace DepthOneQExp

/-- The gate `CNOT_{a,b}` on an `n`-qubit register, controlled by qubit `a` and acting on qubit `b`
(Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group and
applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Notations, p.6: "CNOT_{a,b}
refers to the CNOT gate controlled by qubit a and acting on qubit b"), as the permutation
`x ↦ x + x_a e_b` of the computational basis `{0,1}ⁿ` (add bit `a` into bit `b`, mod 2).

**Formalization Note** 0-based qubit indices taken mod `n` ("the indices are taken with periodic
condition", Theorem 2.2, p.7); the paper's qubit `p` is index `p − 1`. When `a ≡ b (mod n)` there is
no CNOT gate and the permutation is the identity (a junk value: every use in the mission has
`a ≢ b`). The matrix of the gate is `permToMatrix (cnotPerm n a b)`. -/
def cnotPerm (n a b : ℕ) : Equiv.Perm (MITMSynthesis.Q n) :=
  Function.Involutive.toPerm
    (fun x k => if (k : ℕ) = b % n ∧ a % n ≠ b % n then x k + bit x a else x k) (by
      intro x
      have key : ∀ y : MITMSynthesis.Q n, (∀ k : Fin n, (k : ℕ) = a % n → y k = x k) →
          bit y a = bit x a := by
        intro y hy
        unfold bit
        split_ifs with h
        · exact hy _ rfl
        · rfl
      have hbit := key (fun k => if (k : ℕ) = b % n ∧ a % n ≠ b % n then x k + bit x a else x k)
        (by
          intro k hk
          rw [if_neg]
          rintro ⟨h1, h2⟩
          exact h2 (hk.symm.trans h1))
      funext k
      by_cases hk : (k : ℕ) = b % n ∧ a % n ≠ b % n
      · simp only [if_pos hk]
        rw [hbit]
        generalize x k = c
        generalize bit x a = d
        revert c d
        decide
      · simp [hk])

end DepthOneQExp


