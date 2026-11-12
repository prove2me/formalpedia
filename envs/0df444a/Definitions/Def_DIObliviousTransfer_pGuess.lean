-- Prove2me | Definitions.Def_DIObliviousTransfer_pGuess
-- name    : DIObliviousTransfer_pGuess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:02:27.586224+00:00
-- url     : https://prove2.me/theorems/e505b969-130a-43b7-b996-7c577872ab18
-- title:
--   Guessing probability $p_{\mathrm{guess}}(X\mid E)$ and min-entropy
-- statement:
--   Let $\rho_{XE}=\sum_x |x\rangle\langle x|\otimes\rho^E_x$ be a subnormalized classical–quantum state with $X$ ranging over a finite set and $E$ finite-dimensional. Its **guessing probability** is
--   $$p_{\mathrm{guess}}(X\mid E)_\rho=\max_{M_x\succeq0,\ \sum_x M_x=I_E}\ \sum_x \operatorname{Tr}(M_x\rho^E_x),$$
--   and its **conditional min-entropy** is $H_{\min}(X\mid E)_\rho=-\log_2 p_{\mathrm{guess}}(X\mid E)_\rho$, with $\log 0=-\infty$, so $H_{\min}=+\infty$ when the guessing probability vanishes.
--
--   The module also defines POVMs, subnormalized and normalized states, and the block-diagonal operator of a cq state. These are used in the masking lemma and in the one-copy guessing bounds.
--
--   **Formalization Note** The maximum is a supremum over all POVMs; $H_{\min}$ takes values in the extended reals.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Definition 2, p.14

import Mathlib
import Definitions.Def_WildeQIT_traceNorm

namespace DIObliviousTransfer

open Matrix
open scoped Kronecker ComplexOrder

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), §2.1, p.13 and
Definition 2, p.14: states, measurements, classical–quantum states and the guessing probability.

**Formalization Note** (decision D2). Registers are finite-dimensional: an operator on a register
is a complex matrix indexed by a finite type. A subnormalized state is positive semidefinite with
trace at most one. A cq state `ρ_{XE} = Σ_x |x⟩⟨x| ⊗ ρ^E_x` is the family `x ↦ ρ^E_x` of
positive semidefinite blocks. The conditional min-entropy takes values in `EReal`, so that
`log 0 = −∞` gives `H_min = +∞` when the guessing probability is zero (p.14).
-/

/-- A positive operator-valued measure with outcomes in the finite type `α`. -/
def IsPOVM {α E : Type} [Fintype α] [Fintype E] [DecidableEq E]
    (M : α → Matrix E E ℂ) : Prop :=
  (∀ a, (M a).PosSemidef) ∧ ∑ a, M a = 1

/-- A subnormalized state: positive semidefinite, trace at most one. -/
def IsSubState {E : Type} [Fintype E] (ρ : Matrix E E ℂ) : Prop :=
  ρ.PosSemidef ∧ (ρ.trace).re ≤ 1

/-- A (normalized) density operator: positive semidefinite, trace one. -/
def IsState {E : Type} [Fintype E] (ρ : Matrix E E ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- A subnormalized cq state `Σ_x |x⟩⟨x| ⊗ ρ_x`: positive semidefinite blocks of total trace
at most one. -/
def IsSubCQ {X E : Type} [Fintype X] [Fintype E] (ρ : X → Matrix E E ℂ) : Prop :=
  (∀ x, (ρ x).PosSemidef) ∧ (∑ x, (ρ x).trace).re ≤ 1

/-- The block-diagonal operator `Σ_x |x⟩⟨x| ⊗ ρ_x` on `X × E`. -/
def cqOp {X E : Type} [DecidableEq X] (ρ : X → Matrix E E ℂ) : Matrix (X × E) (X × E) ℂ :=
  Matrix.of fun p p' => if p.1 = p'.1 then ρ p.1 p.2 p'.2 else 0

/-- **Definition 2** (guessing probability), p.14:
`p_guess(X | E)_ρ = max_{M_x ⪰ 0, Σ M_x = I} Σ_x Tr(M_x ρ_x)`. The maximum is the supremum over
all POVMs on `E` with outcomes in `X`. -/
noncomputable def pGuess {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
    (ρ : X → Matrix E E ℂ) : ℝ :=
  sSup {p : ℝ | ∃ M : X → Matrix E E ℂ, IsPOVM M ∧ p = (∑ x, (M x * ρ x).trace).re}

/-- **Definition 2** (min-entropy), p.14: `H_min(X | E)_ρ = −log₂ p_guess(X | E)_ρ`, with
`log 0 = −∞`, valued in `EReal`. -/
noncomputable def Hmin {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
    (ρ : X → Matrix E E ℂ) : EReal :=
  if pGuess ρ ≤ 0 then ⊤ else ((-Real.logb 2 (pGuess ρ) : ℝ) : EReal)

end DIObliviousTransfer


