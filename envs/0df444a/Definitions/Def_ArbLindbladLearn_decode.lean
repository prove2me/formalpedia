-- Prove2me | Definitions.Def_ArbLindbladLearn_decode
-- name    : ArbLindbladLearn_decode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:54.288074+00:00
-- url     : https://prove2.me/theorems/be3461e4-8b29-41f7-a6e6-0815c8a436b6
-- title:
--   Output of the learner: sparse coefficient estimates
-- statement:
--   The learner outputs "the list of nonzero estimates together with their labels". At the halt pointer: the counts $K_H,K_D$, then $K_H$ Hamiltonian records ($n$ letters and one real value) and $K_D$ dissipative records (two labels and a complex value as two reals). The estimate $\hat h_a$ (resp. $\hat\gamma_{ab}$) is the sum of the values of the valid records naming $a$ (resp. $(a,b)$); records naming the identity are ignored and unnamed labels get $0$.
--
--   **Formalization Note** A sparse output is necessary: writing all $4^n-1+(4^n-1)^2$ estimates would take exponential time.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), proof of Corollary 4.7, p.34

import Mathlib
import Definitions.Def_ArbLindbladLearn_MState
import Definitions.Def_ArbLindbladLearn_Coeffs

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- Decode a Pauli label from `n` integer cells at `r` (letters `0 = I, 1 = X, 2 = Y, 3 = Z`); an
out-of-range letter makes the label invalid. -/
def parseLabel (n : ℕ) (mem : ℤ → ℤ) (r : ℤ) : Option (Pauli n) :=
  if ∀ i : Fin n, 0 ≤ mem (r + i) ∧ mem (r + i) ≤ 3 then
    some fun i => ⟨(mem (r + i)).toNat % 4, Nat.mod_lt _ (by norm_num)⟩
  else none

/-- The coefficient estimates output by a halted learner (Corollary 4.7, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…),
p.34: "The output is the list of nonzero estimates together with their labels").

Layout at the halt pointer `p`: integer cells `p`, `p + 1` hold the record counts `K_H`, `K_D`.
Hamiltonian record `j < K_H` starts at `r = p + 2 + j(n + 1)`: a label in the integer cells
`r, …, r + n − 1` and its value in the real cell `r + n`. Dissipative record `k < K_D` starts at
`r = p + 2 + K_H(n + 1) + k(2n + 2)`: labels `a` and `b` in the integer cells `r, …, r + 2n − 1`
and the value `Re + i·Im` in the real cells `r + 2n`, `r + 2n + 1`. The estimate of a label (or an
ordered pair) is the sum of the values of the valid records naming it; records naming the identity
are ignored, and unnamed labels get `0`. A machine that has not halted outputs `0`.

**Formalization Note** The output is sparse because writing all `4ⁿ − 1 + (4ⁿ − 1)²` estimates
would take exponential time. -/
def decode (n : ℕ) (s : MState) : Coeffs n :=
  match s.output with
  | none => ⟨fun _ => 0, fun _ _ => 0⟩
  | some p =>
    let KH : ℕ := (s.intMem p).toNat
    let KD : ℕ := (s.intMem (p + 1)).toNat
    let hBase : ℕ → ℤ := fun j => p + 2 + (j : ℤ) * (n + 1)
    let dBase : ℕ → ℤ := fun k => p + 2 + (KH : ℤ) * (n + 1) + (k : ℤ) * (2 * n + 2)
    { h := fun a => by
        classical
        exact ∑ j ∈ Finset.range KH,
          if parseLabel n s.intMem (hBase j) = some a ∧ a ≠ 0 then s.core.mem (hBase j + n)
          else 0
      γ := fun a b => by
        classical
        exact ∑ k ∈ Finset.range KD,
          if parseLabel n s.intMem (dBase k) = some a ∧
              parseLabel n s.intMem (dBase k + n) = some b ∧ a ≠ 0 ∧ b ≠ 0 then
            ⟨s.core.mem (dBase k + 2 * n), s.core.mem (dBase k + 2 * n + 1)⟩
          else 0 }

end ArbLindbladLearn


