-- Prove2me | Definitions.Def_MFHeisGibbs_Model
-- name    : MFHeisGibbs_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:32.484603+00:00
-- url     : https://prove2.me/theorems/1c093efc-0c61-4b5b-b289-ea7c109f44ea
-- title:
--   The mean-field Heisenberg model: $\sigma^{(i,\alpha)}$, $S^\alpha_{\mathrm{tot}}$, $H_n$, $U_\pi$, $\Delta_{g,\pi}$, $R_n$, $P_n$
-- statement:
--   On $n$ qubits, with Hilbert space $\mathcal H_n=(\mathbb C^2)^{\otimes n}$, let $\sigma^{(i,\alpha)}$ be the Pauli operator $\alpha\in\{x,y,z\}$ on qubit $i$. The collective spins and the Hamiltonian are
--
--   $$S^\alpha_{\mathrm{tot}}=\frac12\sum_{i=1}^n\sigma^{(i,\alpha)},\qquad H_n=-\frac1n\sum_{\alpha}(S^\alpha_{\mathrm{tot}})^2 .$$
--
--   For $\pi\in S_n$, the unitary $U_\pi$ moves the content of site $i$ to site $\pi(i)$, $U_{(ij)}$ is the swap of sites $i,j$, and for $g\in SU(2)$ the conjugation is $\Delta_{g,\pi}[\cdot]=g^{\otimes n}U_\pi[\cdot](g^{\otimes n}U_\pi)^\dagger$. The symmetry sectors are the commutants $R_n=\mathrm{comm}\{S^x_{\mathrm{tot}},S^y_{\mathrm{tot}},S^z_{\mathrm{tot}}\}$ and $P_n=\mathrm{comm}\{U_{(ij)}:i<j\}$, together with $\mathrm{comm}\{H_n\}$ and the Hilbert–Schmidt orthogonal complement $V^\perp$.
--
--   These are the objects in which all the paper's statements are written.
--
--   **Formalization Note** The Hilbert space is functions on $\{0,1\}^n$, with $\alpha$ indexed by `Fin 3`. The file also proves that the Paulis, the collective spins and $H_n$ are Hermitian, which the eigendecomposition of $H_n$ needs.
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), (1), p.3 (PDF 4); (14), p.6 (PDF 7); Definitions 1–2, (19), p.7 (PDF 8)

import Mathlib

open Matrix

namespace MFHeisGibbs

/-!
# The mean-field Heisenberg model on `n` qubits

Raikovich, Mák, Czabán, Gilyén, *The complete phase diagram of detailed-balanced Gibbs samplers for
the mean-field Heisenberg model*, arXiv:2610.06818 (version dated November 3, 2026, sha256
164d57ba…), (1), p.3; (14), p.6; (19), Definitions 1–2, p.7.

**Formalization Note.** The Hilbert space `(ℂ²)^{⊗n}` is `(Fin n → Bool) → ℂ`, with computational
basis `|x⟩ = |x₀⟩ ⊗ ⋯ ⊗ |x_{n-1}⟩`, `false = |0⟩`, and `B(H_n)` is `Op n`. The direction index
`α ∈ {x, y, z}` is `Fin 3`, with `0 = x`, `1 = y`, `2 = z`.
-/

/-- The operator space `B(H_n)` of `n` qubits. -/
abbrev Op (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- The Pauli matrices `σˣ, σʸ, σᶻ` on `ℂ²`, indexed by `Fin 3`, with `σᶻ|0⟩ = |0⟩`,
`σʸ|0⟩ = i|1⟩`. -/
def pauli : Fin 3 → Matrix Bool Bool ℂ
  | 0 => Matrix.of fun a b => if a = b then 0 else 1
  | 1 => Matrix.of fun a b => if a = b then 0 else if a then Complex.I else -Complex.I
  | 2 => Matrix.of fun a b => if a = b then (if a then -1 else 1) else 0

/-- The Pauli operator `σ^(i,α)` acting on qubit `i`. -/
def pauliAt {n : ℕ} (i : Fin n) (α : Fin 3) : Op n :=
  Matrix.of fun x y => if ∀ j, j ≠ i → x j = y j then pauli α (x i) (y i) else 0

/-- The collective spin `S^α_tot = (1/2) ∑_i σ^(i,α)`, (1). -/
noncomputable def Stot (n : ℕ) (α : Fin 3) : Op n :=
  (1 / 2 : ℂ) • ∑ i : Fin n, pauliAt i α

/-- The Hamiltonian `H_n = −(1/n) ∑_α (S^α_tot)²`, (1). -/
noncomputable def Hn (n : ℕ) : Op n :=
  (-(n : ℂ)⁻¹) • ∑ α : Fin 3, Stot n α * Stot n α

theorem pauli_isHermitian (α : Fin 3) : (pauli α).IsHermitian := by
  ext a b
  fin_cases α <;> cases a <;> cases b <;> simp [pauli]

theorem pauliAt_isHermitian {n : ℕ} (i : Fin n) (α : Fin 3) : (pauliAt i α).IsHermitian := by
  ext x y
  have h : (∀ j, j ≠ i → y j = x j) ↔ (∀ j, j ≠ i → x j = y j) :=
    forall₂_congr fun _ _ => eq_comm
  have hp := congrFun (congrFun (pauli_isHermitian α) (x i)) (y i)
  simp only [conjTranspose_apply] at hp
  simp only [pauliAt, conjTranspose_apply, of_apply, h]
  split_ifs
  · exact hp
  · simp

theorem Stot_isHermitian (n : ℕ) (α : Fin 3) : (Stot n α).IsHermitian := by
  unfold Stot Matrix.IsHermitian
  rw [conjTranspose_smul, conjTranspose_sum]
  simp only [fun i : Fin n => (pauliAt_isHermitian i α).eq]
  simp

/-- `H_n` is Hermitian, which is what its eigendecomposition (6) needs. -/
theorem Hn_isHermitian (n : ℕ) : (Hn n).IsHermitian := by
  unfold Hn Matrix.IsHermitian
  rw [conjTranspose_smul, conjTranspose_sum]
  simp only [conjTranspose_mul, (Stot_isHermitian n _).eq]
  simp

/-- The unitary `U_π`, `U_π|ψ₁⟩⊗⋯⊗|ψ_n⟩ = |ψ_{π⁻¹(1)}⟩⊗⋯⊗|ψ_{π⁻¹(n)}⟩`, p.6: the content of site
`i` moves to site `π(i)`. -/
def permU {n : ℕ} (π : Equiv.Perm (Fin n)) : Op n :=
  Matrix.of fun y x => if ∀ k, y k = x (π⁻¹ k) then 1 else 0

/-- The swap `U_(ij)` of sites `i` and `j`, (19). -/
def swapOp {n : ℕ} (i j : Fin n) : Op n := permU (Equiv.swap i j)

/-- The tensor power `g^{⊗n}` of a single-qubit matrix. -/
def tensorPow (n : ℕ) (g : Matrix Bool Bool ℂ) : Op n :=
  Matrix.of fun x y => ∏ k, g (x k) (y k)

/-- The superoperator `X ↦ A X B`. -/
def conjMap {n : ℕ} (A B : Op n) : Op n →ₗ[ℂ] Op n where
  toFun X := A * X * B
  map_add' X Y := by simp [mul_add, add_mul]
  map_smul' c X := by simp

/-- The conjugation `∆_{g,π}[·] = g^{⊗n} U_π [·] (g^{⊗n} U_π)†`, (14). -/
def Delta {n : ℕ} (g : Matrix Bool Bool ℂ) (π : Equiv.Perm (Fin n)) : Op n →ₗ[ℂ] Op n :=
  conjMap (tensorPow n g * permU π) (tensorPow n g * permU π)ᴴ

/-- The commutator `[A, X] = A X − X A`. -/
def comm {n : ℕ} (A X : Op n) : Op n := A * X - X * A

/-- The commutant `comm({H_n})`, (16). -/
noncomputable def commH (n : ℕ) : Set (Op n) := {X | X * Hn n = Hn n * X}

/-- The collective-spin-rotation-invariant algebra `R_n = comm({Sˣ_tot, Sʸ_tot, Sᶻ_tot})`,
Definition 1. -/
noncomputable def Rn (n : ℕ) : Set (Op n) := {X | ∀ α, X * Stot n α = Stot n α * X}

/-- The permutation-invariant algebra `P_n = comm({U_(ij) : i < j})`, Definition 2. -/
def Pn (n : ℕ) : Set (Op n) := {X | ∀ i j : Fin n, i < j → X * swapOp i j = swapOp i j * X}

/-- The Hilbert–Schmidt orthogonal complement `V^⊥`, for `⟨Y, X⟩ = Tr(Y†X)`. -/
def hsPerp {n : ℕ} (V : Set (Op n)) : Set (Op n) := {X | ∀ Y ∈ V, trace (Yᴴ * X) = 0}

end MFHeisGibbs


