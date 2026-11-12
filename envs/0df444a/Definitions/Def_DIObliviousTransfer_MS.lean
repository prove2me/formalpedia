-- Prove2me | Definitions.Def_DIObliviousTransfer_MS
-- name    : DIObliviousTransfer_MS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:03:30.480302+00:00
-- url     : https://prove2.me/theorems/00d742b5-71e4-4ba5-99c9-623432740aab
-- title:
--   Magic Square predicate and one-copy Magic Square strategies
-- statement:
--   For questions $x,y\in\{0,1,2\}$ and answers $a,b\in\{0,1\}^3$,
--   $$\mathrm{MS}(x,y,a,b)=\mathbb I[a_y=b_x,\ a_0\oplus a_1\oplus a_2=0,\ b_0\oplus b_1\oplus b_2=1].$$
--   Honest controllers record two bits and complete a row as $(a_0,a_1,a_0\oplus a_1)$ and a column as $(b_0,b_1,1\oplus b_0\oplus b_1)$.
--
--   A **one-copy strategy** consists of a state $\rho$ on $\mathcal H_C\otimes\mathcal H_D$, a POVM of Charlie for each row question (outcome an even row), and an instrument of Dave for each column question (outcome an odd column, quantum output on $\mathcal H_{D'}$). The module defines the loss probability at each question pair, the average loss $\varepsilon$ over uniform questions, and Dave's probability of guessing an entry of Charlie's row from his retained memory.
--
--   **Formalization Note** Strategies are finite-dimensional, and instruments are given in Kraus form.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Definition 1, p.13; (3), p.23; Lemma 28, p.63

import Mathlib
import Definitions.Def_DIObliviousTransfer_pGuess

namespace DIObliviousTransfer

open Matrix
open scoped Kronecker ComplexOrder

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), Definition 1
(p.13), the honest encoding of rows and columns (p.23, before (3)), and the one-copy Magic Square
strategies of Lemmas 28–29 (p.63).

**Formalization Note** (decision D2). Questions are trits `Fin 3`. A row or column answer is
recorded as two bits and completed by parity, `(a₀, a₁, a₀ ⊕ a₁)` for a row and
`(b₀, b₁, 1 ⊕ b₀ ⊕ b₁)` for a column (p.23), so even rows and odd columns are exactly the
outputs of the strategies below. A strategy is finite-dimensional: a state on `H_C ⊗ H_D`, a POVM
of Charlie for each row question, and an instrument of Dave (Kraus form, quantum output space
`H_D'`) for each column question. Probabilities are real parts of traces.
-/

/-- **Definition 1** (Magic Square predicate), p.13:
`MS(x, y, a, b) = 𝕀[a_y = b_x, ⊕_j a_j = 0, ⊕_j b_j = 1]`. -/
def MS (x y : Fin 3) (a b : Fin 3 → Bool) : Bool :=
  decide (a y = b x) && (a 0 ^^ a 1 ^^ a 2 == false) && (b 0 ^^ b 1 ^^ b 2 == true)

/-- The honest row encoding `(a₀, a₁, a₀ ⊕ a₁)` of two recorded bits (p.23). -/
def rowOf (a : Bool × Bool) : Fin 3 → Bool := ![a.1, a.2, a.1 ^^ a.2]

/-- The honest column encoding `(b₀, b₁, 1 ⊕ b₀ ⊕ b₁)` of two recorded bits (p.23). -/
def colOf (b : Bool × Bool) : Fin 3 → Bool := ![b.1, b.2, !(b.1 ^^ b.2)]

/-- A one-copy Magic Square strategy with even-row and odd-column outputs (Lemma 28, p.63):
a state `ρ` on `H_C ⊗ H_D`, Charlie's POVM `M x` for each row question `x`, and Dave's
instrument `K y` (Kraus operators `H_D → H_D'`, outcome the column) for each column question. -/
structure MSStrategy where
  HC : Type
  HD : Type
  HD' : Type
  κ : Type
  [fHC : Fintype HC] [dHC : DecidableEq HC]
  [fHD : Fintype HD] [dHD : DecidableEq HD]
  [fHD' : Fintype HD'] [dHD' : DecidableEq HD']
  [fκ : Fintype κ]
  ρ : Matrix (HC × HD) (HC × HD) ℂ
  hρ : IsState ρ
  M : Fin 3 → Bool × Bool → Matrix HC HC ℂ
  hM : ∀ x, IsPOVM (M x)
  K : Fin 3 → Bool × Bool → κ → Matrix HD' HD ℂ
  hK : ∀ y, ∑ b, ∑ k, (K y b k)ᴴ * K y b k = 1

attribute [instance] MSStrategy.fHC MSStrategy.dHC MSStrategy.fHD MSStrategy.dHD
  MSStrategy.fHD' MSStrategy.dHD' MSStrategy.fκ

namespace MSStrategy

variable (S : MSStrategy)

/-- The subnormalized post-instrument state on `H_C ⊗ H_D'` for column question `y` and
column outcome `b`: `Σ_k (I ⊗ K) ρ (I ⊗ K)†`. -/
noncomputable def post (y : Fin 3) (b : Bool × Bool) : Matrix (S.HC × S.HD') (S.HC × S.HD') ℂ :=
  ∑ k, ((1 : Matrix S.HC S.HC ℂ) ⊗ₖ S.K y b k) * S.ρ * ((1 : Matrix S.HC S.HC ℂ) ⊗ₖ S.K y b k)ᴴ

/-- `Pr[MS(x, y, A, B) = 0 | X = x, Y = y]`. -/
noncomputable def lossAt (x y : Fin 3) : ℝ :=
  ∑ a, ∑ b, if MS x y (rowOf a) (colOf b) then 0 else
    ((S.M x a ⊗ₖ (1 : Matrix S.HD' S.HD' ℂ)) * S.post y b).trace.re

/-- The average loss over independent uniform questions, `ε = (1/9) Σ_{x,y} Pr[MS = 0 | x, y]`. -/
noncomputable def avgLoss : ℝ := (1 / 9 : ℝ) * ∑ x, ∑ y, S.lossAt x y

/-- For fixed questions `x, y`, the probability that Dave's guessing measurement `N b`
(chosen after his column outcome `b`, knowing `x` and `y`) outputs the entry `A[k]` of
Charlie's row. -/
noncomputable def guessProb (x y : Fin 3) (k : Fin 3) (N : Bool × Bool → Bool → Matrix S.HD' S.HD' ℂ) :
    ℝ :=
  ∑ a, ∑ b, ((S.M x a ⊗ₖ N b (rowOf a k)) * S.post y b).trace.re

end MSStrategy

end DIObliviousTransfer


