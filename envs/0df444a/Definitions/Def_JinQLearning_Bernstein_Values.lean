-- Prove2me | Definitions.Def_JinQLearning_Bernstein_Values
-- name    : JinQLearning_Bernstein_Values
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:33:25.293993+00:00
-- url     : https://prove2.me/theorems/bfd475b3-ead1-4ddb-8cf4-c8307fae7453
-- title:
--   Constructed policy and optimal Bellman values
-- statement:
--   For a deterministic Markov policy, the remaining-length recursion adds the present reward to the transition expectation of the next-stage value. The public value at stage h uses H-h remaining steps. Optimal values use the same backward recursion with a maximum over the nonempty finite action type. Policy Q and optimal Q add the current reward to the respective next-stage expectation. The terminal stage H, corresponding to the paper's H+1, has value zero. These are constructed functions, not arbitrary functions equipped with assumed Bellman identities. Finite maxima have nonempty bounded domains; values at out-of-range natural stages are also zero and are never used as decision stages.
-- source:
--   Jin, Allen-Zhu, Bubeck & Jordan, Is Q-learning Provably Efficient?, arXiv:1807.03765v1, pp. 4–5, equation (2.1).

import Definitions.Def_JinQLearning_Bernstein_Model

open scoped BigOperators
noncomputable section

namespace JinQLearning.Bernstein

variable {S A H : ℕ} [NeZero A]

/-- Maximum over the nonempty finite action space. -/
def actionMax (f : Fin A → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty f

/-- Remaining-length recursion; the branch h ≥ H is terminal. -/
def policyValueAux (M : Model S A H) (π : Policy S A H) : ℕ → ℕ → Fin S → ℝ
  | 0, _, _ => 0
  | n + 1, h, x => if hh : h < H then
      reward M ⟨h, hh⟩ x (π ⟨h, hh⟩ x) +
        expectation M ⟨h, hh⟩ x (π ⟨h, hh⟩ x) (policyValueAux M π n (h + 1))
    else 0

def policyValue (M : Model S A H) (π : Policy S A H) (h : ℕ) : Fin S → ℝ :=
  policyValueAux M π (H - h) h

def policyQ (M : Model S A H) (π : Policy S A H) (h : Fin H) (x : Fin S) (a : Fin A) : ℝ :=
  reward M h x a + expectation M h x a (policyValue M π (h.val + 1))

def optimalValueAux (M : Model S A H) : ℕ → ℕ → Fin S → ℝ
  | 0, _, _ => 0
  | n + 1, h, x => if hh : h < H then
      actionMax (fun a => reward M ⟨h, hh⟩ x a +
        expectation M ⟨h, hh⟩ x a (optimalValueAux M n (h + 1)))
    else 0

def optimalValue (M : Model S A H) (h : ℕ) : Fin S → ℝ :=
  optimalValueAux M (H - h) h

def optimalQ (M : Model S A H) (h : Fin H) (x : Fin S) (a : Fin A) : ℝ :=
  reward M h x a + expectation M h x a (optimalValue M (h.val + 1))

end JinQLearning.Bernstein


