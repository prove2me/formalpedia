-- Prove2me | Definitions.Def_AddXnor_Supplement_core
-- name    : AddXnor_Supplement_core
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:29:32.742527+00:00
-- url     : https://prove2.me/theorems/67810afd-a7d3-4d14-adca-12a609f49337
-- title:
--   Uniform Add/XNOR correlations, run profiles, and transfer matrix
-- statement:
--   For a left-to-right Add/XNOR chain on uniformly random independent $m$-bit operands, this module defines the operator-string value $E_A(x)$, maximal addition-run profile, signed single-bit correlations, the one-run carry correlation $c_j(z)$, and the transfer matrix
--   $$
--   M_j[s',s]=(-1)^{[s'<s]}.
--   $$
--   It also defines $c(z)=2^{-z/2}\cos(z\pi/4)$, the eigenvalues $\lambda_k=1-i\cot\theta_k$, and the decay factor $\rho_j$ used in Theorems 3--6.
--
--   The definitions provide one shared finite-probability semantics for all linear and differential statements in the supplement.
--
--   **Formalization Note** Words are `BitVec m`, operator positions and bit positions are 0-based, and bit $1$ is the second least-significant bit. Uniform probabilities are exact finite averages. The published `AddXnor.chain` supplies the arithmetic semantics.
-- source:
--   Wang, Lv, Shen, Zhang, Add/XNOR Chains: An NP-Complete Boolean–Arithmetic Problem at the Meet-in-the-Middle Barrier, manuscript (sha256 405d6dda…), Sections 4.2–4.4, pp.14–20 (PDF pp.14–20)

import Mathlib
import Definitions.Def_AddXnor_chain

set_option autoImplicit false

namespace AddXnor.Supplement

/-!
# Finite-probability and correlation objects for Add/XNOR chains

These definitions formalize Sections 4.2--4.4 of Wang--Lv--Shen--Zhang,
*Add/XNOR Chains* (manuscript, sha256 405d6dda..., pp.14--20, PDF pp.14--20).
All operator positions are 0-based.  An operator bit `false` is addition and `true` is XNOR,
as in the published `AddXnor.step` and `AddXnor.chain` definitions.
-/

/-- The arithmetic mean over a nonempty finite type. -/
noncomputable def uniformMean {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

/-- The probability of a predicate under the uniform law on a nonempty finite type. -/
noncomputable def uniformProb {α : Type*} [Fintype α] [Nonempty α]
    (P : α → Prop) [DecidablePred P] : ℝ :=
  uniformMean fun a => if P a then 1 else 0

/-- Evaluation `E_A(x)` of a `q`-operator, `q+1`-operand chain on `m`-bit words.

The operands are indexed `0,...,q`; operator `i` combines the current state with operand `i+1`.
-/
def eval {q m : ℕ} (A : Fin (q + 1) → BitVec m) (x : Fin q → Bool) : BitVec m :=
  AddXnor.chain (A 0) (List.ofFn fun i : Fin q => (x i, A i.succ))

/-- Hamming weight of an operator string (the number of XNOR operators). -/
def weight {q : ℕ} (x : Fin q → Bool) : ℕ :=
  ∑ i, if x i then 1 else 0

/-- The lengths of the maximal addition (`false`) runs, read from left to right.

The fold temporarily records zero-length separators and removes them at the end.  Thus an
all-XNOR string has the empty profile and its run product is the empty product `1`.
-/
def additionRuns {q : ℕ} (x : Fin q → Bool) : List ℕ :=
  ((List.ofFn x).foldr
    (fun b rs =>
      if b then 0 :: rs
      else match rs with
        | [] => [1]
        | z :: zs => (z + 1) :: zs)
    []).filter (fun z => z ≠ 0)

/-- The carry-free affine approximation to bit `j`:
`⊕_i A_{i,j} ⊕ (wt(x) mod 2)`.  Bit indices are least-significant first. -/
def affineBit {q m : ℕ} (A : Fin (q + 1) → BitVec m) (x : Fin q → Bool)
    (j : ℕ) : Bool :=
  decide (((∑ i, if (A i).getLsbD j then 1 else 0) + weight x) % 2 = 1)

/-- The signed correlation of bit `j` of `E_A(x)` with the carry-free affine model, averaged
over independent uniform operands `A_i ∈ {0,1}^m` (pp.14 and 17).

It is `+1` on agreement and `-1` on disagreement before averaging. -/
noncomputable def correlationAt {q m : ℕ} (x : Fin q → Bool) (j : ℕ) : ℝ :=
  uniformMean fun A : Fin (q + 1) → BitVec m =>
    if (eval A x).getLsbD j = affineBit A x j then 1 else -1

/-- `Cor(x)`, the signed correlation at bit `1`, the second least-significant bit (p.14). -/
noncomputable def correlation {q m : ℕ} (x : Fin q → Bool) : ℝ :=
  correlationAt (m := m) x 1

/-- The one-run bit-`j` carry correlation `c_j(z)` (p.17).  Width `j+1` retains exactly the
bits that can affect the carry into bit `j`; higher bits are irrelevant. -/
noncomputable def carryCorrelation (j z : ℕ) : ℝ :=
  correlationAt (m := j + 1) (fun _ : Fin z => false) j

/-- The closed form `c(z) = 2^{-z/2} cos(zπ/4)` of Theorem 3. -/
noncomputable def runCorrelation (z : ℕ) : ℝ :=
  Real.rpow 2 (-(z : ℝ) / 2) * Real.cos ((z : ℝ) * Real.pi / 4)

/-- The transfer matrix `M_j[s',s] = (-1)^[s'<s]`, with `N=2^j` (Theorem 5). -/
noncomputable def transferMatrix (j : ℕ) : Matrix (Fin (2 ^ j)) (Fin (2 ^ j)) ℂ :=
  fun s' s => if (s' : ℕ) < (s : ℕ) then -1 else 1

/-- `θ_k = (2k+1)π / 2^(j+1)` (Theorem 5). -/
noncomputable def theta (j : ℕ) (k : Fin (2 ^ j)) : ℝ :=
  ((2 * (k : ℕ) + 1 : ℕ) : ℝ) * Real.pi / (2 : ℝ) ^ (j + 1)

/-- `λ_k = 1 - i cot θ_k` (Theorem 5). -/
noncomputable def eigenvalue (j : ℕ) (k : Fin (2 ^ j)) : ℂ :=
  1 - Complex.I * (Real.cos (theta j k) / Real.sin (theta j k))

/-- `ρ_j = 1 / (2^j sin(π/2^(j+1)))` (Theorem 5). -/
noncomputable def rho (j : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ j * Real.sin (Real.pi / (2 : ℝ) ^ (j + 1)))

/-- A square complex matrix has an eigenbasis with the prescribed indexed eigenvalues.
Nonzero determinant says that the displayed eigenvectors (the columns of `P`) form a basis. -/
def HasIndexedEigenbasis {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (eig : Fin n → ℂ) : Prop :=
  ∃ P : Matrix (Fin n) (Fin n) ℂ,
    Matrix.det P ≠ 0 ∧
      ∀ k : Fin n, M.mulVec (fun i => P i k) = fun i => eig k * P i k

/-- Uniform collision probability of two operator strings on the same uniform operands. -/
noncomputable def collisionProb {q m : ℕ} (x x' : Fin q → Bool) : ℝ :=
  uniformProb fun A : Fin (q + 1) → BitVec m => eval A x = eval A x'

end AddXnor.Supplement


