-- Prove2me | Definitions.Def_HarlowTASI_OperatorAlgebras
-- name    : HarlowTASI_OperatorAlgebras
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:11:01.057668+00:00
-- url     : https://prove2.me/theorems/f11476cc-9584-49dd-8bc4-d6a4fef4e156
-- title:
--   Block decompositions of finite-dimensional von Neumann algebras and algebraic (relative) entropy (Harlow TASI §5.3)
-- statement:
--   Vocabulary of §5.3 of Harlow's lectures: von Neumann algebras on a finite-dimensional Hilbert space, their block decomposition, and the algebraic entropy and relative entropy of a state on such an algebra.
--
--   A **von Neumann algebra** on $\mathcal H=\mathbb C^{C}$ (Definition 5.3: closed under products, sums and adjoints, and containing every $\lambda I$) is a $*$-subalgebra $M$ of the $C\times C$ complex matrices; its **commutant** $M'$ (Definition 5.4) is the set of matrices commuting with all of $M$, and its **center** is $Z_M=M\cap M'$ (Definition 5.5).
--
--   A **block decomposition** $\mathcal H\cong\bigoplus_{\alpha}\big(\mathcal H_{r_\alpha}\otimes\mathcal H_{\overline r_\alpha}\big)$, eq. (5.12), is encoded by a number $N$ of blocks, dimensions $d_{r_\alpha},d_{\overline r_\alpha}$, and a unitary $U:\mathcal H\to\bigoplus_\alpha\mathbb C^{d_{r_\alpha}}\otimes\mathbb C^{d_{\overline r_\alpha}}$. Transported back by $U$ we get the three sets of eq. (5.13):
--   $$\textstyle\bigoplus_\alpha\mathcal L(\mathcal H_{r_\alpha})\otimes I_{\overline r_\alpha},\qquad \bigoplus_\alpha I_{r_\alpha}\otimes\mathcal L(\mathcal H_{\overline r_\alpha}),\qquad \bigoplus_\alpha\lambda_\alpha I_{r_\alpha\overline r_\alpha}.$$
--
--   For a state $\rho$ on $\mathcal H$, write the diagonal blocks of $U\rho U^\dagger$ as $p_\alpha\rho_{r_\alpha\overline r_\alpha}$ with $p_\alpha=\mathrm{Tr}$ of the block, eq. (5.15), and set $\rho_{r_\alpha}=\mathrm{Tr}_{\overline r_\alpha}\rho_{r_\alpha\overline r_\alpha}$, $\rho_{\overline r_\alpha}=\mathrm{Tr}_{r_\alpha}\rho_{r_\alpha\overline r_\alpha}$. For $M=\bigoplus_\alpha\mathcal L(\mathcal H_{r_\alpha})\otimes I_{\overline r_\alpha}$ the **algebraic entropy** (5.16) and **algebraic relative entropy** (5.18) are
--   $$S(\rho,M)=-\sum_\alpha p_\alpha\log p_\alpha+\sum_\alpha p_\alpha S(\rho_{r_\alpha}),\qquad S(\rho|\sigma,M)=\sum_\alpha p^{\{\rho\}}_\alpha\log\frac{p^{\{\rho\}}_\alpha}{p^{\{\sigma\}}_\alpha}+\sum_\alpha p^{\{\rho\}}_\alpha S(\rho_{r_\alpha}|\sigma_{r_\alpha}),$$
--   and the same formulas with $\overline r_\alpha$ in place of $r_\alpha$ give $S(\rho,M')$ and $S(\rho|\sigma,M')$.
--
--   These definitions are the language of Theorem 5.1 and of the entanglement wedge reconstruction theorem (Theorem 5.2).
--
--   **Formalization Note** Blocks are indexed by `Fin N` with block dimensions given by functions `Fin N → ℕ`. When $p_\alpha=0$ the normalized block state is the zero matrix and contributes nothing. The classical term $p\log(p/q)$ is $0$ for $p=0$ and $+\infty$ for $p\neq0=q$; relative entropies are valued in `EReal`. The entropies are defined relative to a chosen block decomposition $U$; since the value does not depend on the choice, every statement using them quantifies over an arbitrary decomposition realizing the given algebra.
-- source:
--   Daniel Harlow, TASI Lectures on the Emergence of Bulk Physics in AdS/CFT, PoS(TASI2017)002 (2018), arXiv:1802.01040, §5.3 (pp. 43–45): Definitions 5.3–5.5, eqs. (5.12)–(5.13) of Theorem 5.1, eqs. (5.15), (5.16), (5.18).

import Mathlib
import Definitions.Def_HarlowTASI_QuantumBasics

/-!
# Harlow, TASI Lectures — von Neumann algebras on finite-dimensional spaces and their entropies

A von Neumann algebra on the finite-dimensional space `ℂ^C` in the sense of Definition 5.3
(closed under products, sums, adjoints, and containing all `λ I`) is a
`StarSubalgebra ℂ (Matrix C C ℂ)`; its commutant `M'` (Definition 5.4) is
`StarSubalgebra.centralizer ℂ M` and its center `Z_M = M ∩ M'` (Definition 5.5) is
`M ⊓ StarSubalgebra.centralizer ℂ M`.

A block decomposition (5.12) `H = ⊕_α (H_{r_α} ⊗ H_{r̄_α})` is encoded by a number `N` of
blocks, block dimensions `dr α = dim H_{r_α}`, `drb α = dim H_{r̄_α}`, and a unitary
`U : H → ⊕_α (ℂ^{dr α} ⊗ ℂ^{drb α})`. The algebraic entropies (5.16) and (5.18) are computed
from the diagonal blocks (5.15) of a state in such a decomposition.
-/

namespace HarlowTASI

open Matrix
open scoped Kronecker ComplexOrder

noncomputable section

/-- Index type of `⊕_{α < N} (ℂ^{dr α} ⊗ ℂ^{drb α})`. -/
abbrev BlockIndex (N : ℕ) (dr drb : Fin N → ℕ) : Type :=
  Σ a : Fin N, Fin (dr a) × Fin (drb a)

variable {N : ℕ} {dr drb : Fin N → ℕ}

/-- The block-diagonal operator `⊕_α (x_α ⊗ I_{r̄_α})`. -/
def blockLeftOp (x : ∀ a, Matrix (Fin (dr a)) (Fin (dr a)) ℂ) :
    Matrix (BlockIndex N dr drb) (BlockIndex N dr drb) ℂ :=
  blockDiagonal' fun a => x a ⊗ₖ (1 : Matrix (Fin (drb a)) (Fin (drb a)) ℂ)

/-- The block-diagonal operator `⊕_α (I_{r_α} ⊗ y_α)`. -/
def blockRightOp (y : ∀ a, Matrix (Fin (drb a)) (Fin (drb a)) ℂ) :
    Matrix (BlockIndex N dr drb) (BlockIndex N dr drb) ℂ :=
  blockDiagonal' fun a => (1 : Matrix (Fin (dr a)) (Fin (dr a)) ℂ) ⊗ₖ y a

/-- The block-diagonal operator `⊕_α λ_α I_{r_α r̄_α}`. -/
def blockScalarOp (c : Fin N → ℂ) : Matrix (BlockIndex N dr drb) (BlockIndex N dr drb) ℂ :=
  blockDiagonal' fun a => c a • (1 : Matrix (Fin (dr a) × Fin (drb a)) (Fin (dr a) × Fin (drb a)) ℂ)

variable {C : Type} [Fintype C] [DecidableEq C]

/-- `⊕_α L(H_{r_α}) ⊗ I_{r̄_α}`, transported to `ℂ^C` by the unitary `U`:
the set of all `U† (⊕_α x_α ⊗ I) U`. -/
def blockAlgebraLeft (U : Matrix (BlockIndex N dr drb) C ℂ) : Set (Matrix C C ℂ) :=
  {X | ∃ x : ∀ a, Matrix (Fin (dr a)) (Fin (dr a)) ℂ, X = Uᴴ * blockLeftOp (drb := drb) x * U}

/-- `⊕_α I_{r_α} ⊗ L(H_{r̄_α})`, transported to `ℂ^C` by `U`. -/
def blockAlgebraRight (U : Matrix (BlockIndex N dr drb) C ℂ) : Set (Matrix C C ℂ) :=
  {X | ∃ y : ∀ a, Matrix (Fin (drb a)) (Fin (drb a)) ℂ, X = Uᴴ * blockRightOp (dr := dr) y * U}

/-- `⊕_α λ_α I_{r_α r̄_α}`, transported to `ℂ^C` by `U`. -/
def blockAlgebraCenter (U : Matrix (BlockIndex N dr drb) C ℂ) : Set (Matrix C C ℂ) :=
  {X | ∃ c : Fin N → ℂ, X = Uᴴ * blockScalarOp (dr := dr) (drb := drb) c * U}

/-- The diagonal block `ρ_{r_α r̄_α, r_α r̄_α}` (unnormalized, i.e. `p_α ρ_{r_α r̄_α}` in (5.15))
of the operator `U ρ U†`. -/
def diagBlock (U : Matrix (BlockIndex N dr drb) C ℂ) (ρ : Matrix C C ℂ) (a : Fin N) :
    Matrix (Fin (dr a) × Fin (drb a)) (Fin (dr a) × Fin (drb a)) ℂ :=
  (U * ρ * Uᴴ).submatrix
    (Sigma.mk (β := fun b => Fin (dr b) × Fin (drb b)) a)
    (Sigma.mk (β := fun b => Fin (dr b) × Fin (drb b)) a)

/-- The block probability `p_α = Tr (diagonal block α)` (real part). -/
def blockWeight (U : Matrix (BlockIndex N dr drb) C ℂ) (ρ : Matrix C C ℂ) (a : Fin N) : ℝ :=
  (diagBlock U ρ a).trace.re

/-- `ρ_{r_α} = Tr_{r̄_α} ρ_{r_α r̄_α}` with `ρ_{r_α r̄_α} = p_α⁻¹ · (diagonal block α)`
(the zero matrix when `p_α = 0`). -/
def blockStateLeft (U : Matrix (BlockIndex N dr drb) C ℂ) (ρ : Matrix C C ℂ) (a : Fin N) :
    Matrix (Fin (dr a)) (Fin (dr a)) ℂ :=
  ((blockWeight U ρ a : ℂ))⁻¹ • traceRight (diagBlock U ρ a)

/-- `ρ_{r̄_α} = Tr_{r_α} ρ_{r_α r̄_α}` (the zero matrix when `p_α = 0`). -/
def blockStateRight (U : Matrix (BlockIndex N dr drb) C ℂ) (ρ : Matrix C C ℂ) (a : Fin N) :
    Matrix (Fin (drb a)) (Fin (drb a)) ℂ :=
  ((blockWeight U ρ a : ℂ))⁻¹ • traceLeft (diagBlock U ρ a)

/-- Algebraic entropy (5.16) of `ρ` on `M = U† (⊕_α L(H_{r_α}) ⊗ I) U`:
`S(ρ, M) = -∑_α p_α log p_α + ∑_α p_α S(ρ_{r_α})`. -/
def algebraicEntropyLeft (U : Matrix (BlockIndex N dr drb) C ℂ) (ρ : Matrix C C ℂ) : ℝ :=
  ∑ a, Real.negMulLog (blockWeight U ρ a) +
    ∑ a, blockWeight U ρ a * vonNeumannEntropy (blockStateLeft U ρ a)

/-- Algebraic entropy of `ρ` on the commutant `M' = U† (⊕_α I ⊗ L(H_{r̄_α})) U`:
`S(ρ, M') = -∑_α p_α log p_α + ∑_α p_α S(ρ_{r̄_α})`. -/
def algebraicEntropyRight (U : Matrix (BlockIndex N dr drb) C ℂ) (ρ : Matrix C C ℂ) : ℝ :=
  ∑ a, Real.negMulLog (blockWeight U ρ a) +
    ∑ a, blockWeight U ρ a * vonNeumannEntropy (blockStateRight U ρ a)

/-- The classical term `p log (p / q)` of (5.18) in the extended reals:
`0` if `p = 0`, `+∞` if `p ≠ 0 = q`, and `p log (p/q)` otherwise. -/
def classicalRelTerm (p q : ℝ) : EReal :=
  if p = 0 then 0 else if q = 0 then ⊤ else ((p * Real.log (p / q) : ℝ) : EReal)

/-- Algebraic relative entropy (5.18) on `M = U† (⊕_α L(H_{r_α}) ⊗ I) U`:
`S(ρ|σ, M) = ∑_α p_α^ρ log (p_α^ρ / p_α^σ) + ∑_α p_α^ρ S(ρ_{r_α} | σ_{r_α})`. -/
def algebraicRelEntropyLeft (U : Matrix (BlockIndex N dr drb) C ℂ) (ρ σ : Matrix C C ℂ) :
    EReal :=
  ∑ a, classicalRelTerm (blockWeight U ρ a) (blockWeight U σ a) +
    ∑ a, ((blockWeight U ρ a : ℝ) : EReal) *
      relativeEntropy (blockStateLeft U ρ a) (blockStateLeft U σ a)

/-- Algebraic relative entropy on the commutant `M' = U† (⊕_α I ⊗ L(H_{r̄_α})) U`. -/
def algebraicRelEntropyRight (U : Matrix (BlockIndex N dr drb) C ℂ) (ρ σ : Matrix C C ℂ) :
    EReal :=
  ∑ a, classicalRelTerm (blockWeight U ρ a) (blockWeight U σ a) +
    ∑ a, ((blockWeight U ρ a : ℝ) : EReal) *
      relativeEntropy (blockStateRight U ρ a) (blockStateRight U σ a)

end

end HarlowTASI


