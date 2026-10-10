-- Prove2me | Definitions.Def_HarlowTASI_QuantumBasics
-- name    : HarlowTASI_QuantumBasics
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:10:22.941218+00:00
-- url     : https://prove2.me/theorems/2c4e828c-f14b-45bf-b2ee-f9ef4206585c
-- title:
--   Finite-dimensional quantum states, partial traces, entropies and erasure codes (Harlow TASI §4)
-- statement:
--   Basic finite-dimensional quantum-information vocabulary used throughout Harlow's lectures, §4 and §5.
--
--   All Hilbert spaces are finite-dimensional and are modelled by coordinates: a space with orthonormal basis indexed by a finite set $\iota$ is $\mathbb C^{\iota}$, and operators are complex $\iota\times\iota$ matrices. A bipartite space $\mathcal H_R\otimes\mathcal H_{\overline R}$ is $\mathbb C^{R\times\overline R}$, and $X\otimes Y$ is the Kronecker product.
--
--   1. An **isometry** is a matrix $V$ with $V^\dagger V=I$. A code subspace $\mathcal H_{code}\subseteq\mathcal H_R\otimes\mathcal H_{\overline R}$ is represented by an isometry $V:\mathbb C^{C}\to\mathcal H_R\otimes\mathcal H_{\overline R}$ whose columns $|\tilde i\rangle=V|i\rangle$ form an orthonormal basis of $\mathcal H_{code}$; an operator $\tilde O$ on $\mathcal H_{code}$ is a $C\times C$ matrix, and the code state $|\tilde\psi\rangle$ is $V|\psi\rangle$.
--   2. A **unitary** between two index sets is a matrix $U$ with $U^\dagger U=I$ and $UU^\dagger=I$.
--   3. A **density matrix** is a positive semidefinite matrix of trace one.
--   4. **Partial traces** $\mathrm{Tr}_{\overline R}$ and $\mathrm{Tr}_R$ of an operator on $\mathcal H_R\otimes\mathcal H_{\overline R}$.
--   5. The **von Neumann entropy** $S(\rho)=-\mathrm{Tr}\,\rho\log\rho=-\sum_\lambda \lambda\log\lambda$ over the eigenvalues of a Hermitian $\rho$ (with $0\log0=0$), eq. (5.14).
--   6. The **relative entropy** $S(\rho|\sigma)=\mathrm{Tr}\,\rho\log\rho-\mathrm{Tr}\,\rho\log\sigma\in(-\infty,+\infty]$, eq. (5.17), computed from spectral decompositions $\rho=\sum_i p_i|u_i\rangle\langle u_i|$, $\sigma=\sum_j q_j|v_j\rangle\langle v_j|$ as
--   $$S(\rho|\sigma)=\sum_{i,j}|\langle u_i|v_j\rangle|^2\,p_i\,(\log p_i-\log q_j),$$
--   with terms having $p_i=0$ or $\langle u_i|v_j\rangle=0$ equal to $0$, and terms having $p_i\neq0$, $\langle u_i|v_j\rangle\neq0$, $q_j=0$ equal to $+\infty$.
--   7. **Reduced density matrices** $\rho_{SB},\rho_S,\rho_B$ of a pure state $|\psi\rangle\in S\otimes A\otimes B$.
--   8. The **reference state** of eq. (4.18), $|\phi\rangle=|S|^{-1/2}\sum_i|i\rangle_S|\tilde i\rangle_{R\overline R}$, with the reference system $S$ indexed by the code basis.
--   9. For $n$ qudits of dimension $d$ and a set $A$ of sites, the splitting $(\mathbb C^d)^{\otimes n}\cong(\mathbb C^d)^{\otimes A}\otimes(\mathbb C^d)^{\otimes A^c}$, and the predicate **"the encoded information is accessible from $A$"**: every logical operator $\tilde O$ has an $O_A$ acting on $A$ alone with $O_A|\tilde\psi\rangle=\tilde O|\tilde\psi\rangle$ and $O_A^\dagger|\tilde\psi\rangle=\tilde O^\dagger|\tilde\psi\rangle$ for all code states (condition (1) of Theorem 4.1, as used in the derivation of the quantum Singleton bound).
--
--   These notions are shared by every statement of the mission.
--
--   **Formalization Note** Entropies are defined through the eigen-decomposition of a Hermitian matrix and take the junk value $0$ on non-Hermitian input; they are only ever applied to density matrices. The relative entropy is valued in `EReal` so that the value $+\infty$ (support of $\rho$ not contained in that of $\sigma$) is representable.
-- source:
--   Daniel Harlow, TASI Lectures on the Emergence of Bulk Physics in AdS/CFT, PoS(TASI2017)002 (2018), arXiv:1802.01040, §4.2–§4.3 (pp. 24–31): eqs. (4.16)–(4.20) of Theorem 4.1 and eqs. (4.21)–(4.25); §5.3 eqs. (5.14), (5.17).

import Mathlib

/-!
# Harlow, TASI Lectures on the Emergence of Bulk Physics in AdS/CFT — basic quantum notions

Finite-dimensional Hilbert spaces are modelled as `ℂ^ι` for a finite index type `ι`, and
operators as complex matrices indexed by `ι`. A bipartite space `H_R ⊗ H_R̄` is indexed by the
product type `R × Rb`, and `X ⊗ₖ Y` is the Kronecker (tensor) product of matrices.
A code subspace `H_code ⊆ H_R ⊗ H_R̄` is described by an isometry `V : ℂ^C → H_R ⊗ H_R̄`
whose columns form an orthonormal basis `|ĩ⟩` of `H_code`.
-/

namespace HarlowTASI

open Matrix
open scoped Kronecker ComplexOrder

noncomputable section

/-- `V` is an isometry: `V† V = 1`. Its columns are then an orthonormal basis of its range. -/
def IsIsometry {m n : Type} [Fintype m] [DecidableEq n] (V : Matrix m n ℂ) : Prop :=
  Vᴴ * V = 1

/-- `U` is unitary (possibly between two differently indexed spaces of equal dimension):
`U† U = 1` and `U U† = 1`. -/
def IsUnitaryMatrix {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (U : Matrix m n ℂ) : Prop :=
  Uᴴ * U = 1 ∧ U * Uᴴ = 1

/-- A density matrix (mixed state): positive semidefinite with unit trace. -/
def IsDensityMatrix {n : Type} [Fintype n] (ρ : Matrix n n ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- Partial trace over the second tensor factor: `(Tr_B X)_{ij} = ∑_k X_{(i,k),(j,k)}`. -/
def traceRight {A B : Type} [Fintype B] (X : Matrix (A × B) (A × B) ℂ) : Matrix A A ℂ :=
  fun i j => ∑ k, X (i, k) (j, k)

/-- Partial trace over the first tensor factor: `(Tr_A X)_{ij} = ∑_k X_{(k,i),(k,j)}`. -/
def traceLeft {A B : Type} [Fintype A] (X : Matrix (A × B) (A × B) ℂ) : Matrix B B ℂ :=
  fun i j => ∑ k, X (k, i) (k, j)

/-- Von Neumann entropy `S(ρ) = -Tr(ρ log ρ) = -∑ λ log λ` over the eigenvalues `λ` of a
Hermitian matrix `ρ` (with `0 log 0 = 0`). Junk value `0` on non-Hermitian input. -/
noncomputable def vonNeumannEntropy {n : Type} [Fintype n] [DecidableEq n]
    (ρ : Matrix n n ℂ) : ℝ :=
  if h : ρ.IsHermitian then ∑ i, Real.negMulLog (h.eigenvalues i) else 0

/-- Quantum relative entropy `S(ρ|σ) = Tr(ρ log ρ) - Tr(ρ log σ)`, valued in the extended reals.
Writing `ρ = ∑ pᵢ |uᵢ⟩⟨uᵢ|`, `σ = ∑ qⱼ |vⱼ⟩⟨vⱼ|` (spectral decompositions) and
`wᵢⱼ = |⟨uᵢ, vⱼ⟩|²`, it is `∑ᵢⱼ wᵢⱼ pᵢ (log pᵢ - log qⱼ)`, where a term with `pᵢ = 0` or
`wᵢⱼ = 0` is `0`, and a term with `pᵢ ≠ 0`, `wᵢⱼ ≠ 0`, `qⱼ = 0` is `+∞` (so `S(ρ|σ) = +∞`
exactly when the support of `ρ` is not contained in that of `σ`, for density matrices).
Junk value `0` on non-Hermitian input. -/
noncomputable def relativeEntropy {n : Type} [Fintype n] [DecidableEq n]
    (ρ σ : Matrix n n ℂ) : EReal :=
  if h : ρ.IsHermitian ∧ σ.IsHermitian then
    ∑ i, ∑ j,
      (if h.1.eigenvalues i = 0 ∨
          ‖inner ℂ (h.1.eigenvectorBasis i) (h.2.eigenvectorBasis j)‖ = 0 then (0 : EReal)
       else if h.2.eigenvalues j = 0 then ⊤
       else (((‖inner ℂ (h.1.eigenvectorBasis i) (h.2.eigenvectorBasis j)‖ ^ 2 *
          h.1.eigenvalues i * (Real.log (h.1.eigenvalues i) - Real.log (h.2.eigenvalues j)) : ℝ))
          : EReal))
  else 0

/-- Reduced density matrix on `S ⊗ B` of the pure state `|ψ⟩ ∈ S ⊗ A ⊗ B` (trace over `A`):
`ρ_{SB}((s,b),(s',b')) = ∑_a ψ(s,a,b) · conj ψ(s',a,b')`. -/
def reducedSB {S A B : Type} [Fintype A] (ψ : S × A × B → ℂ) : Matrix (S × B) (S × B) ℂ :=
  fun x y => ∑ a, ψ (x.1, a, x.2) * star (ψ (y.1, a, y.2))

/-- Reduced density matrix on `S` of the pure state `|ψ⟩ ∈ S ⊗ A ⊗ B`. -/
def reducedS {S A B : Type} [Fintype A] [Fintype B] (ψ : S × A × B → ℂ) : Matrix S S ℂ :=
  fun s s' => ∑ a, ∑ b, ψ (s, a, b) * star (ψ (s', a, b))

/-- Reduced density matrix on `B` of the pure state `|ψ⟩ ∈ S ⊗ A ⊗ B`. -/
def reducedB {S A B : Type} [Fintype S] [Fintype A] (ψ : S × A × B → ℂ) : Matrix B B ℂ :=
  fun b b' => ∑ s, ∑ a, ψ (s, a, b) * star (ψ (s, a, b'))

/-- The state `|φ⟩ = |S|^{-1/2} ∑ᵢ |i⟩_S |ĩ⟩_{RR̄}` of eq. (4.18), where the reference system
`S` is indexed by the same finite type `C` as the code basis, `|ĩ⟩ = V |i⟩`. As a function on
`S × R × R̄`: `φ(s, r, b) = |C|^{-1/2} V_{(r,b), s}`. -/
noncomputable def codeReferenceState {R Rb C : Type} [Fintype C]
    (V : Matrix (R × Rb) C ℂ) : C × R × Rb → ℂ :=
  fun x => ((Real.sqrt (Fintype.card C) : ℝ) : ℂ)⁻¹ * V (x.2.1, x.2.2) x.1

/-- Qudit systems: for a set `A` of sites among `n` qudits of dimension `d`, the
identification `(ℂ^d)^{⊗ n} ≅ (ℂ^d)^{⊗ A} ⊗ (ℂ^d)^{⊗ Aᶜ}` applied to the row index of an
encoding map `V : ℂ^{code} → (ℂ^d)^{⊗ n}`. -/
def splitAt {n d : ℕ} {C : Type} (A : Finset (Fin n)) (V : Matrix (Fin n → Fin d) C ℂ) :
    Matrix (({i // i ∈ A} → Fin d) × ({i // i ∉ A} → Fin d)) C ℂ :=
  V.submatrix (Equiv.piEquivPiSubtypeProd (fun i => i ∈ A) (fun _ => Fin d)).symm id

/-- The logical information encoded by `V` into `n` qudits is accessible from the set of
qudits `A` in the sense of condition (1) of Theorem 4.1: every logical operator `O` has a
representative `O_A` acting only on the qudits in `A` such that `O_A |ψ̃⟩ = O |ψ̃⟩` and
`O_A† |ψ̃⟩ = O† |ψ̃⟩` for every code state `|ψ̃⟩`. -/
def AccessibleFrom {n d : ℕ} {C : Type} [Fintype C] [DecidableEq C]
    (V : Matrix (Fin n → Fin d) C ℂ) (A : Finset (Fin n)) : Prop :=
  ∀ O : Matrix C C ℂ, ∃ OA : Matrix ({i // i ∈ A} → Fin d) ({i // i ∈ A} → Fin d) ℂ,
    (OA ⊗ₖ (1 : Matrix ({i // i ∉ A} → Fin d) ({i // i ∉ A} → Fin d) ℂ)) * splitAt A V
        = splitAt A V * O ∧
    (OAᴴ ⊗ₖ (1 : Matrix ({i // i ∉ A} → Fin d) ({i // i ∉ A} → Fin d) ℂ)) * splitAt A V
        = splitAt A V * Oᴴ

end

end HarlowTASI


