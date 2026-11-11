-- Prove2me | Definitions.Def_LindbladShallow_dnorm
-- name    : LindbladShallow_dnorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:10:56.406203+00:00
-- url     : https://prove2.me/theorems/f9603d01-5533-4719-91ec-2b93c8815fe2
-- title:
--   Operator norm, partial trace, initialization isometry and the unhalved diamond norm
-- statement:
--   Basic quantum-information objects used throughout the mission.
--
--   1. The **operator norm** $\|A\|$ of a rectangular complex matrix is the induced Euclidean (spectral) norm.
--   2. The **partial trace** over a second factor $A$ is $(\mathrm{Tr}_A X)_{ij}=\sum_a X_{(i,a),(j,a)}$.
--   3. The **initialization isometry** $\psi\mapsto\psi\otimes|a_0\rangle_A$, and the map $Z\mapsto \mathrm{Tr}_A(EZE^\dagger)$ induced by an initialized operator $E:S\to S\otimes A$.
--   4. The **diamond norm** of a map $\Phi$ between matrix spaces, without the factor $\tfrac12$:
--   $$\|\Phi\|_\diamond:=\sup_{r\ge 1}\ \sup_{Z\neq 0}\ \frac{\|(\Phi\otimes I_r)(Z)\|_1}{\|Z\|_1}.$$
--   5. The chronological ordered product $A_k\cdots A_1$ of a list $[A_1,\dots,A_k]$ (the head acts first) and the Loewner order $A\preceq B$ ($B-A$ positive semidefinite).
--
--   These are the norms of §2.2 of the paper: operator norms for initialized columns and the diamond norm for channels; every channel estimate is uniform over an untouched reference of any dimension.
--
--   **Formalization Note** The supremum is taken in $[0,\infty]$ over every reference dimension $r\ge1$ and every nonzero complex matrix $Z$, so a bound $\|\Phi\|_\diamond\le\epsilon$ says exactly $\|(\Phi\otimes I_r)(Z)\|_1\le\epsilon\|Z\|_1$ for all $r$ and $Z$. The trace norm is the published `QAlgorithms.traceNorm` and the stabilization is the published `QAlgorithms.idTensorSuperop` (reference factor first, which changes no value).
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), §2.2, p.10; Eq. (3), p.11; Eq. (47), p.50

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Channel

open scoped Matrix ComplexOrder ENNReal

namespace LindbladShallow

open QAlgorithms

/-- The induced Euclidean (spectral, `ℓ²→ℓ²`) operator norm `‖A‖` of a rectangular complex matrix
(Shen–Wu–Yuan–Zhang, *Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics*,
arXiv:2610.05362, held version sha256 8f4637ef…, §2.2, p.10: "For operators, ‖A‖ is the induced
Euclidean norm").

**Formalization Note** It is Mathlib's `Matrix.instL2OpNormedAddCommGroup` norm, used as an explicit
function so that no global norm instance on matrices is introduced. -/
noncomputable def opNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : ℝ :=
  @Norm.norm _ (Matrix.instL2OpNormedAddCommGroup (𝕜 := ℂ) (m := m) (n := n)).toNorm A

/-- Partial trace over the second tensor factor: `(Tr_A X)_{ij} = Σ_a X_{(i,a),(j,a)}`
(arXiv:2610.05362, Eq. (3), p.11, and Eq. (47), p.50). -/
def ptrace {S A : Type*} [Fintype A] (X : Matrix (S × A) (S × A) ℂ) : Matrix S S ℂ :=
  Matrix.of fun i j => ∑ a, X (i, a) (j, a)

/-- The initialization isometry `ψ ↦ ψ ⊗ |a₀⟩_A` as a matrix `(S × A) × S`
(arXiv:2610.05362, Lemma 2.2, p.11: `E_C ψ := U_C(ψ ⊗ |0⟩_A)`; §2.3, p.12: `E₀ψ := ψ ⊗ ⨂_b |0⟩_b`). -/
def vacIso {S A : Type*} [DecidableEq S] [DecidableEq A] (a₀ : A) : Matrix (S × A) S ℂ :=
  Matrix.of fun p i => if p = (i, a₀) then 1 else 0

/-- The map induced by an initialized operator `E : S → S ⊗ A`: `Z ↦ Tr_A(E Z E†)`
(arXiv:2610.05362, Eq. (3), p.11). For `E = U(· ⊗ |0⟩)` with `U` unitary this is the circuit's
induced channel. -/
noncomputable def isoChannel {S A : Type*} [Fintype S] [Fintype A] (E : Matrix (S × A) S ℂ) :
    Superop S S :=
  fun Z => ptrace (E * Z * Eᴴ)

/-- The **unhalved diamond norm** of a map `Φ` from `ι`-matrices to `κ`-matrices
(arXiv:2610.05362, §2.2, p.10, after [Wat18, Ch. 3]):
`‖Φ‖_⋄ := sup_{r ≥ 1} sup_{Z ≠ 0} ‖(Φ ⊗ I_r)(Z)‖₁ / ‖Z‖₁`.

**Formalization Note** The supremum is taken in `ℝ≥0∞` (`⨆`), over every reference dimension
`r ≥ 1` and every nonzero complex matrix `Z` on `ℂ^r ⊗ ℂ^ι` (not only density matrices), so there
is no junk value of a real `sSup`. The trace norm is the published `QAlgorithms.traceNorm`
(`Re Tr √(Z†Z)`). The reference factor is placed first (`QAlgorithms.idTensorSuperop`, i.e.
`id_r ⊗ Φ`); this reorders tensor factors and changes no value. A bound `dnorm Φ ≤ ofReal ε` says
exactly: for every `r ≥ 1` and every `Z`, `‖(Φ ⊗ I_r)(Z)‖₁ ≤ ε ‖Z‖₁`. -/
noncomputable def dnorm {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Φ : Superop ι κ) : ℝ≥0∞ :=
  ⨆ (r : ℕ) (_ : 1 ≤ r) (Z : Matrix (Fin r × ι) (Fin r × ι) ℂ) (_ : Z ≠ 0),
    ENNReal.ofReal (traceNorm (idTensorSuperop (R := Fin r) Φ Z) / traceNorm Z)

/-- Ordered product of a list of square matrices, **head acting first**:
`orderedProd [A₁, …, A_k] = A_k ⋯ A₁` (the chronological convention of arXiv:2610.05362, e.g.
`V = V_L ⋯ V_1`, p.20). -/
def orderedProd {n : Type*} [Fintype n] [DecidableEq n] (l : List (Matrix n n ℂ)) : Matrix n n ℂ :=
  l.foldl (fun acc A => A * acc) 1

/-- The Loewner order `A ⪯ B`, i.e. `B − A` is positive semidefinite. -/
def LoewnerLE {n : Type*} [Fintype n] (A B : Matrix n n ℂ) : Prop :=
  (B - A).PosSemidef

end LindbladShallow


