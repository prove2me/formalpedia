-- Prove2me | Definitions.Def_mme_stothers_phi125_profile_data
-- name    : mme_stothers_phi125_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T23:49:02.693573+00:00
-- url     : https://prove2.me/theorems/d146921f-db88-4805-93f6-4ba4a5519bfd
-- title:
--   Exact and marginal finite profiles for the phi_125 laser extraction
-- statement:
--   The six summands of the Davie–Stothers constituent φ₁₂₅ are labelled by the first square-factor grades (004), (013), (022), (103), (112), and (121). For nonnegative integers α, β, γ with α+β+γ=N, the symmetric length-2N profile assigns multiplicities (α,β,γ,γ,β,α). Its three projected grade histograms are exactly (N,N,0,0,0), (α+γ,2β,α+γ,0,0), and (0,α,β+γ,β+γ,α). This definition introduces exact six-label words, the ambient family defined only by those marginals, and triples of exact words with the cyclic vertex ordering used by type-2 hashing. It is the finite combinatorial model underlying Lemma 5.1(ii), and its cyclic data can be reused by later type-2 extraction lemmas.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 5.1(ii), printed pp. 364–365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic

open BigOperators

namespace MME.StothersFourth.Phi125

set_option autoImplicit false

/-- The six ordered square-constituent summands of `phi_125`, encoded by
the grade of the first square factor.  The opposite square factor is then
forced because the total fourth-power grade is `(1,2,5)`. -/
def pattern : Fin 6 → Fin 3 → Fin 5
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 4
  | 1, 0 => 0
  | 1, 1 => 1
  | 1, 2 => 3
  | 2, 0 => 0
  | 2, 1 => 2
  | 2, 2 => 2
  | 3, 0 => 1
  | 3, 1 => 0
  | 3, 2 => 3
  | 4, 0 => 1
  | 4, 1 => 1
  | 4, 2 => 2
  | 5, 0 => 1
  | 5, 1 => 2
  | 5, 2 => 1

/-- The symmetric profile `(alpha,beta,gamma,gamma,beta,alpha)` on the
six displayed summands. -/
def profileMultiplicity (alpha beta gamma : ℕ) : Fin 6 → ℕ
  | 0 => alpha
  | 1 => beta
  | 2 => gamma
  | 3 => gamma
  | 4 => beta
  | 5 => alpha

/-- The mode marginals printed in Davie--Stothers Lemma 5.1(ii):
`(N,N,0,0,0)`, `(alpha+gamma,2 beta,alpha+gamma,0,0)`, and
`(0,alpha,beta+gamma,beta+gamma,alpha)`. -/
def marginalMultiplicity
    (N alpha beta gamma : ℕ) : Fin 3 → Fin 5 → ℕ
  | 0, 0 => N
  | 0, 1 => N
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 1, 0 => alpha + gamma
  | 1, 1 => 2 * beta
  | 1, 2 => alpha + gamma
  | 1, 3 => 0
  | 1, 4 => 0
  | 2, 0 => 0
  | 2, 1 => alpha
  | 2, 2 => beta + gamma
  | 2, 3 => beta + gamma
  | 2, 4 => alpha

/-- A length-`2N` word in the six supported summands. -/
abbrev ProfileWord (N : ℕ) := Fin (2 * N) → Fin 6

/-- Projection of a six-label word to one of its three grade words. -/
def modeWord {N : ℕ} (w : ProfileWord N) (i : Fin 3) : Fin (2 * N) → Fin 5 :=
  fun j => pattern (w j) i

/-- The exact symmetric profile used for the `phi_125` laser extraction. -/
def ExactProfileWord (N alpha beta gamma : ℕ) : Type :=
  {w : ProfileWord N //
    ∀ r : Fin 6,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => w j = r)).card = profileMultiplicity alpha beta gamma r}

/-- The ambient family obtained by remembering only the three mode
marginals of the exact profile. -/
def MarginalProfileWord (N alpha beta gamma : ℕ) : Type :=
  {w : ProfileWord N //
    ∀ i : Fin 3, ∀ s : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => modeWord w i j = s)).card =
          marginalMultiplicity N alpha beta gamma i s}

/-- Three cyclic copies of one exact profile, the edge set used before
type-2 hashing. -/
def CyclicExactEdge (N alpha beta gamma : ℕ) : Type :=
  ExactProfileWord N alpha beta gamma ×
    (ExactProfileWord N alpha beta gamma ×
      ExactProfileWord N alpha beta gamma)

/-- One vertex of a cyclic edge consists of one mode word from each cyclic
orientation. -/
def CyclicModeWord (N : ℕ) : Type :=
  (Fin (2 * N) → Fin 5) ×
    ((Fin (2 * N) → Fin 5) × (Fin (2 * N) → Fin 5))

/-- The actual three vertices of a cyclic exact edge. -/
def cyclicModeWord
    {N alpha beta gamma : ℕ}
    (e : CyclicExactEdge N alpha beta gamma) :
    Fin 3 → CyclicModeWord N
  | ⟨0, _⟩ => (modeWord e.1.1 0, (modeWord e.2.1.1 2, modeWord e.2.2.1 1))
  | ⟨1, _⟩ => (modeWord e.1.1 1, (modeWord e.2.1.1 0, modeWord e.2.2.1 2))
  | ⟨2, _⟩ => (modeWord e.1.1 2, (modeWord e.2.1.1 1, modeWord e.2.2.1 0))
  | ⟨_ + 3, h⟩ => absurd h (by omega)

end MME.StothersFourth.Phi125


