-- Prove2me | Definitions.Def_QFairEx_kronMap
-- name    : QFairEx_kronMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:05.605455+00:00
-- url     : https://prove2.me/theorems/3a64e1ec-0d97-45d9-983b-5b9dea0af2c3
-- title:
--   Tensor product of maps on matrices and partial traces
-- statement:
--   For maps $\Phi$ on matrices over $Q$ and $\Psi$ on matrices over $Q'$, the **tensor product** $\Phi\otimes\Psi$ acts on matrices over $Q\times Q'$ by
--   $$(\Phi\otimes\Psi)(X)=\sum_{i,j\in Q}\ \sum_{i',j'\in Q'}X_{(i,i'),(j,j')}\;\Phi(|i\rangle\langle j|)\otimes\Psi(|i'\rangle\langle j'|).$$
--   With $\Psi=\mathrm{id}$ this is the operation $\Phi\otimes\mathrm{id}$ on the first register only, the way the paper applies "operations on specified registers … as the identity on all other registers". The **partial traces** are $(\operatorname{Tr}_2X)_{ij}=\sum_eX_{(i,e),(j,e)}$ and $(\operatorname{Tr}_1X)_{ij}=\sum_eX_{(e,i),(e,j)}$.
--
--   These are used to let each party act on its own registers inside the joint state, and to discard a register.
--
--   **Formalization Note** The tensor product is defined through matrix units, so it is the tensor product of linear maps whenever $\Phi$ and $\Psi$ are linear.
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), §3.1, p.13

import Mathlib

namespace QFairEx

open Matrix

/-- **Tensor product of two maps on matrices**, `Φ ⊗ Ψ`.
Chung, Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), §3.1, p.13: "Operations on specified registers act as the
identity on all other registers, including any reference register entangled with the input."

`kronMap Φ Ψ X = ∑_{i,j,i',j'} X_{(i,i'),(j,j')} · Φ(|i⟩⟨j|) ⊗ Ψ(|i'⟩⟨j'|)`, the linear
extension of `A ⊗ B ↦ Φ A ⊗ Ψ B`. With `Ψ = id` this is `Φ ⊗ id`, an operation on the first
register only.

**Formalization Note.** Defined through matrix units, so it is the tensor product of the linear
maps whenever `Φ`, `Ψ` are linear (as every map of Kraus form is). -/
noncomputable def kronMap {Q R Q' R' : Type} [Fintype Q] [Fintype Q'] [DecidableEq Q]
    [DecidableEq Q'] (Φ : Matrix Q Q ℂ → Matrix R R ℂ) (Ψ : Matrix Q' Q' ℂ → Matrix R' R' ℂ)
    (X : Matrix (Q × Q') (Q × Q') ℂ) : Matrix (R × R') (R × R') ℂ :=
  ∑ i : Q, ∑ j : Q, ∑ i' : Q', ∑ j' : Q',
    X (i, i') (j, j') • Matrix.kroneckerMap (· * ·) (Φ (Matrix.single i j 1)) (Ψ (Matrix.single i' j' 1))

/-- **Partial trace over the second register**: `(Tr₂ X)_{i j} = ∑_e X_{(i,e),(j,e)}`. -/
def ptraceRight {Q E : Type} [Fintype E] (X : Matrix (Q × E) (Q × E) ℂ) : Matrix Q Q ℂ :=
  fun i j => ∑ e, X (i, e) (j, e)

/-- **Partial trace over the first register**: `(Tr₁ X)_{i j} = ∑_e X_{(e,i),(e,j)}`. -/
def ptraceLeft {E Q : Type} [Fintype E] (X : Matrix (E × Q) (E × Q) ℂ) : Matrix Q Q ℂ :=
  fun i j => ∑ e, X (e, i) (e, j)

end QFairEx


