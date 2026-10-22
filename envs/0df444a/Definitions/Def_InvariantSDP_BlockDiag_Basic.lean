-- Prove2me | Definitions.Def_InvariantSDP_BlockDiag_Basic
-- name    : InvariantSDP_BlockDiag_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:38:43.750261+00:00
-- url     : https://prove2.me/theorems/9e5af6f5-0241-4b33-8046-935d641a31da
-- title:
--   Definition 2.1, p. 10; p. 13; Theorem 2.2, p. 11 — zero-one diagonal $I_S$, center, unit, simple matrix ∗-algebra, maximal commutative ∗-subalgebra, the relation ∼
-- statement:
--   Throughout, a **matrix ∗-algebra** (Definition 2.1) is a complex linear subspace $\mathcal A \subseteq \mathbb C^{n\times n}$ that is closed under matrix multiplication and under the conjugate transpose $X \mapsto X^*$. It need not contain the identity matrix, and it may be $\{0\}$. This module fixes the vocabulary used by the rest of the mission.
--
--   1. $\mathcal A$ is **commutative** if $XY = YX$ for all $X, Y \in \mathcal A$ (§2.2).
--   2. The **center** of $\mathcal A$ is $\mathcal C_{\mathcal A} = \{Z \in \mathcal A : ZX = XZ \text{ for all } X \in \mathcal A\}$ (p. 13).
--   3. A matrix $E$ is a **unit** of $\mathcal A$ if $E \in \mathcal A$ and $EX = XE = X$ for every $X \in \mathcal A$ (p. 13).
--   4. $\mathcal A$ is **simple** if $\mathcal A \neq \{0\}$ and there is a unit $E$ of $\mathcal A$ with $\mathcal C_{\mathcal A} = \mathbb C E$ (p. 13). Only the inclusion $\mathcal C_{\mathcal A} \subseteq \mathbb C E$ is written out; the reverse inclusion holds automatically because $E$ lies in the center.
--   5. A matrix ∗-algebra $\mathcal B$ is an **inclusionwise maximal commutative ∗-subalgebra** of $\mathcal A$ if $\mathcal B \subseteq \mathcal A$, $\mathcal B$ is commutative, and every commutative matrix ∗-algebra $\mathcal B'$ with $\mathcal B \subseteq \mathcal B' \subseteq \mathcal A$ equals $\mathcal B$ (proof of Theorem 2.7, p. 14).
--   6. For a partition $[n] = S_0 \cup S_1 \cup \dots \cup S_k$, the **zero-one diagonal matrix** $I_i$ has ones in the diagonal positions from $S_i$ and zeros elsewhere (Theorem 2.2). A matrix ∗-algebra $\mathcal B$ is in **diagonal form** for the partition if $S_1, \dots, S_k$ are nonempty and
--   $$\mathcal B = \{\lambda_1 I_1 + \dots + \lambda_k I_k : \lambda_1, \dots, \lambda_k \in \mathbb C\}.$$
--   7. For a matrix ∗-algebra $\mathcal A$ and such a partition, the relation $\sim$ on $\{1, \dots, k\}$ is $i \sim j$ iff $I_i \mathcal A I_j \neq \{0\}$ (proof of Theorem 2.7, p. 14).
--
--   These notions carry the statement of the block-diagonalization theorem and of every step of its elementary proof.
--
--   **Formalization Note** A matrix ∗-algebra is a `NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)` (Mathlib's star on matrices is the conjugate transpose); the unital `StarSubalgebra` is deliberately not used, since the paper does not assume $I \in \mathcal A$. Indices are 0-based: `Fin n` stands for $[n]$. A partition is a map `S : Fin n → Option (Fin k)`; `S j = none` puts $j$ in $S_0$, and `S j = some i` puts $j$ in $S_{i+1}$ (so the paper's $I_1, \dots, I_k$ are `zeroOneDiag S (some 0), …, zeroOneDiag S (some (k-1))`, and $I_0$ is `zeroOneDiag S none`). $S_0$ may be empty and $k = 0$ is allowed. The center is a `Set`.
-- source:
--   Bachoc, Gijswijt, Schrijver & Vallentin, Invariant semidefinite programs, arXiv:1007.2905v2, p. 10, Definition 2.1; p. 11, §2.2 and Theorem 2.2; p. 13, terminology after Theorem 2.7; p. 14, proof of Theorem 2.7

import Mathlib

namespace InvariantSDP.BlockDiag

open Matrix

variable {n : ℕ}

/-- A matrix ∗-algebra (Definition 2.1, p. 10) is a `NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)`:
a complex linear subspace closed under matrix multiplication and conjugate transpose. No unit is assumed.
`A` is commutative (§2.2, p. 11) if any two of its elements commute. -/
def IsCommutative (A : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  ∀ X ∈ A, ∀ Y ∈ A, X * Y = Y * X

/-- The center `𝒞_𝒜 = {A ∈ 𝒜 : AB = BA for all B ∈ 𝒜}` (p. 13). -/
def center (A : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    Set (Matrix (Fin n) (Fin n) ℂ) :=
  {Z | Z ∈ A ∧ ∀ X ∈ A, Z * X = X * Z}

/-- `E` is a unit of `A` (p. 13): `E ∈ 𝒜` and `EX = XE = X` for every `X ∈ 𝒜`. -/
def IsUnitOf (A : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (E : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  E ∈ A ∧ ∀ X ∈ A, E * X = X ∧ X * E = X

/-- `A` is simple (p. 13): `𝒜` is non-zero, and its center is `ℂE` for its unit `E`. -/
def IsSimple (A : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  A ≠ ⊥ ∧ ∃ E, IsUnitOf A E ∧ ∀ Z ∈ center A, ∃ c : ℂ, Z = c • E

/-- `B` is an inclusionwise maximal commutative ∗-subalgebra of `A` (proof of Theorem 2.7, p. 14). -/
def IsMaxCommutative (A B : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  B ≤ A ∧ IsCommutative B ∧
    ∀ B' : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ),
      B ≤ B' → B' ≤ A → IsCommutative B' → B' = B

/-- The zero-one diagonal matrix of one part of a partition `[n] = S₀ ∪ S₁ ∪ ⋯ ∪ S_k` (Theorem 2.2, p. 11).
The partition is the map `S : Fin n → Option (Fin k)`: index `j` lies in `S₀` when `S j = none` and in
`S_{i+1}` when `S j = some i`. `zeroOneDiag S i` has ones in the positions of part `i`, zeros elsewhere. -/
noncomputable def zeroOneDiag {k : ℕ} (S : Fin n → Option (Fin k)) (i : Option (Fin k)) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun j => if S j = i then 1 else 0

/-- `B` is in the diagonal form of Theorem 2.2 for the partition `S`: the parts `S₁, …, S_k` are nonempty
and `ℬ = {λ₁I₁ + ⋯ + λ_kI_k : λ₁, …, λ_k ∈ ℂ}`. -/
def IsDiagForm {k : ℕ} (B : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (S : Fin n → Option (Fin k)) : Prop :=
  (∀ i : Fin k, ∃ j, S j = some i) ∧
    (B : Set (Matrix (Fin n) (Fin n) ℂ)) =
      Set.range fun l : Fin k → ℂ => ∑ i, l i • zeroOneDiag S (some i)

/-- The relation `∼` on `{1, …, k}` (proof of Theorem 2.7, p. 14): `i ∼ j` iff `I_i 𝒜 I_j ≠ {0}`. -/
def blockRel {k : ℕ} (A : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (S : Fin n → Option (Fin k)) (i j : Fin k) : Prop :=
  ∃ X ∈ A, zeroOneDiag S (some i) * X * zeroOneDiag S (some j) ≠ 0

end InvariantSDP.BlockDiag


