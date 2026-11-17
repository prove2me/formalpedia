-- Prove2me | Definitions.Def_SingleInteraction_Supplement_Linalg
-- name    : SingleInteraction_Supplement_Linalg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:00:40.593311+00:00
-- url     : https://prove2.me/theorems/7ffa5c62-d6a3-4ed1-a943-b8f220b58420
-- title:
--   Ground energy $\lambda_{\min}$, ground space, multiplicities, spectral gap, stoquasticity and qubit tensor products
-- statement:
--   Spectral and tensor-product notions used throughout the supplement, for an operator $A$ on the Hilbert space of a finite qubit register.
--
--   1. $\lambda_{\min}(A)=\inf_{\|\phi\|=1}\langle\phi|A|\phi\rangle$, the ground energy (the least eigenvalue when $A$ is Hermitian).
--   2. $\mathrm{Ground}(A)$, the eigenspace of $A$ for the eigenvalue $\lambda_{\min}(A)$.
--   3. The multiplicity of a real number $\mu$ as an eigenvalue of $A$, taken as its multiplicity as a root of the characteristic polynomial (zero when $\mu$ is not an eigenvalue).
--   4. The spectral gap of $A$: the least eigenvalue strictly above $\lambda_{\min}(A)$, minus $\lambda_{\min}(A)$.
--   5. A matrix is **stoquastic** in the computational basis if all its entries are real and all its off-diagonal entries are $\le0$ (Definition 33).
--   6. $A\otimes B$ on $a+b$ qubits with $A$ on the first $a$ qubits; $\Pi_{|z\rangle}=|z\rangle\langle z|$ for a basis state $z$; and $h_{\mathrm{check}}=I-\Pi_{|0\rangle}\otimes\Pi_{|1\rangle}$ on two qubits (eqs. (28), (49)).
--
--   These notions express the promises of the pinned, frustration-free, precise and guided problems and the spectral claims of Theorems 49 and 74.
--
--   **Formalization Note** The infimum is over unit vectors of a nonempty finite-dimensional space, and the energy is bounded below by $-\|A\|$, so $\lambda_{\min}$ is attained for Hermitian $A$. The spectral gap is used only under the hypothesis that some eigenvalue lies above $\lambda_{\min}$.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §2.1, p.15 (projectors); Definition 33, p.31 (stoquastic); Definitions 35, 39, 41, pp.31–33 (λmin, ground space); Theorem 49, pp.40–41 (Ground, spectral gap); Lemma 30, p.28 and Theorem 74, p.85 (multiplicities); eqs. (28), (49), pp.39, 73 (h_check)

import Mathlib
import Definitions.Def_SingleInteraction_energy

namespace SingleInteraction

namespace Supplement

/-!
# Spectral notions and qubit tensor products for the supplement

Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version,
sha256 19ddc444…): `λmin` (Definitions 35, 39, 41, pp.31–33), `Ground(·)` and the spectral gap
(Theorem 49, pp.40–41), eigenvalue multiplicities (Lemma 30, p.28; Theorem 74, p.85), stoquasticity
(Definition 33, p.31), the projectors `Π|i⟩` (§2.1, p.15) and tensor products of qubit operators.

**Formalization Note**
* `lamMin A` is the infimum of `⟨ϕ|A|ϕ⟩` over unit vectors `ϕ`. The index types used are
  `ι → Fin 2`, which are nonempty, so the set of unit vectors is nonempty, and the energy is bounded
  below by `−‖A‖`; for Hermitian `A` the infimum is attained and is the least eigenvalue.
* `groundSpace A` is the eigenspace of `A` (acting on `EuclideanSpace ℂ ι`) for the eigenvalue
  `lamMin A`.
* `eigMult A μ` is the multiplicity of `μ` as a root of the characteristic polynomial of `A`. For
  Hermitian `A` this is the dimension of the `μ`-eigenspace (it is `0` when `μ` is not an
  eigenvalue).
* `excited A` is the set of eigenvalues strictly above `lamMin A`, and `specGap A` is its least
  element minus `lamMin A`. The theorems that use `specGap` assume `excited A` nonempty; it is a
  finite set, so its infimum is then its minimum.
* `tensorQ A B` is `A ⊗ B` on `a + b` qubits: the first factor acts on qubits `0, …, a−1`, the
  second on qubits `a, …, a+b−1`. Basis states are `Fin q → Fin 2`, bit `0` is `|0⟩`.
* `IsStoquastic h`: every entry of `h` is real and every off-diagonal entry is `≤ 0`
  (Definition 33). -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `λmin(A)`: the infimum of the energy `⟨ϕ|A|ϕ⟩` over unit vectors `ϕ` (the least eigenvalue of a
Hermitian `A`). -/
noncomputable def lamMin (A : Matrix ι ι ℂ) : ℝ :=
  sInf (Set.range fun φ : {φ : EuclideanSpace ℂ ι // ‖φ‖ = 1} => energy A φ.1)

/-- `Ground(A)`: the eigenspace of `A` for the eigenvalue `λmin(A)`. -/
noncomputable def groundSpace (A : Matrix ι ι ℂ) : Submodule ℂ (EuclideanSpace ℂ ι) :=
  LinearMap.ker (Matrix.toEuclideanLin A - ((lamMin A : ℝ) : ℂ) • LinearMap.id)

/-- The multiplicity of `μ` as an eigenvalue of `A` (root multiplicity in the characteristic
polynomial). -/
noncomputable def eigMult (A : Matrix ι ι ℂ) (μ : ℝ) : ℕ :=
  A.charpoly.rootMultiplicity (μ : ℂ)

/-- The eigenvalues of `A` strictly above `λmin(A)`. -/
def excited (A : Matrix ι ι ℂ) : Set ℝ :=
  {μ | lamMin A < μ ∧ 0 < eigMult A μ}

/-- The spectral gap above the ground space: the least eigenvalue above `λmin(A)`, minus `λmin(A)`.
Meaningful when `excited A` is nonempty. -/
noncomputable def specGap (A : Matrix ι ι ℂ) : ℝ :=
  sInf (excited A) - lamMin A

/-- Stoquastic in the computational basis (Definition 33): real entries, non-positive off-diagonal
entries. -/
def IsStoquastic (h : Matrix ι ι ℂ) : Prop :=
  ∀ s t, (h s t).im = 0 ∧ (s ≠ t → (h s t).re ≤ 0)

/-- `A ⊗ B` on `a + b` qubits, `A` on the first `a` qubits and `B` on the last `b`. -/
def tensorQ {a b : ℕ} (A : Matrix (Fin a → Fin 2) (Fin a → Fin 2) ℂ)
    (B : Matrix (Fin b → Fin 2) (Fin b → Fin 2) ℂ) :
    Matrix (Fin (a + b) → Fin 2) (Fin (a + b) → Fin 2) ℂ :=
  fun s t => A (fun i => s (Fin.castAdd b i)) (fun i => t (Fin.castAdd b i)) *
    B (fun j => s (Fin.natAdd a j)) (fun j => t (Fin.natAdd a j))

/-- A single-qubit operator `M` as a matrix on `Fin 1 → Fin 2`. -/
def oneQ (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ :=
  fun s t => M (s 0) (t 0)

/-- `|i⟩⟨j|` on one qubit. -/
def ketBra (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.single i j 1

/-- The projector `Π|z⟩ = |z⟩⟨z|` onto a computational-basis state `z` of `q` qubits (for `q = 1`
this is `Π|0⟩` or `Π|1⟩`). -/
def basisProj {q : ℕ} (z : Fin q → Fin 2) : Matrix (Fin q → Fin 2) (Fin q → Fin 2) ℂ :=
  fun s t => if s = z ∧ t = z then 1 else 0

/-- `h_check = I − Π|0⟩ ⊗ Π|1⟩` on two qubits (eqs. (28), (49), p.39 and p.73). -/
def hCheck : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  1 - basisProj ![0, 1]

end Supplement

end SingleInteraction


