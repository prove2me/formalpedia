-- Prove2me | Definitions.Def_ClonableQMASep_Main_Channels
-- name    : ClonableQMASep_Main_Channels
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:23:39.757364+00:00
-- url     : https://prove2.me/theorems/52e42d6e-c7a6-48c1-a283-c7aaab95c6aa
-- title:
--   Trace distance, density operators and quantum channels
-- statement:
--   For complex matrices indexed by a finite set:
--
--   1. the **trace norm** $\|A\|_1=\operatorname{Tr}\sqrt{A^\dagger A}$, the sum of the singular values of $A$;
--   2. the **trace distance** $D(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$;
--   3. a **density operator** is a positive semidefinite matrix of trace one;
--   4. a **quantum channel** from operators on $\mathbb C^{\iota}$ to operators on $\mathbb C^{\kappa}$ is a map of Kraus form $\Phi(\rho)=\sum_k K_k\rho K_k^\dagger$ with finitely many $K_k$ and $\sum_k K_k^\dagger K_k=I$ (in finite dimension these are exactly the CPTP maps; measurements with classical outcome registers are included);
--   5. the pure density operator $|v\rangle\langle v|$;
--   6. the states of a chain of operations $\rho_{t+1}=\Psi_t(\Phi_t(\rho_t))$, where $\Phi_t$ is a subroutine and $\Psi_t$ an operation interleaved after it; dimensions may change from step to step.
--
--   These are the objects of §2.1 and of the hybrid bound for channels (Lemma 2).
-- source:
--   Alper Cakan, Kai-Min Chung, Wei-Hsiang Hung, Tzu-Yi Yang, Separating ClonableQMA and QCMA Relative to a Classical Oracle, STOC 2027 submission #844 (October 2026), §2.1 p. 11 (trace distance); §2.3 pp. 11–12 (quantum channels, interleaved channels)

import Mathlib

set_option autoImplicit false

namespace ClonableQMASep.Main

open scoped ComplexConjugate Matrix ComplexOrder

/-- The **trace norm** `‖A‖₁ = Tr √(A†A)`, the sum of the singular values of `A`. -/
noncomputable def traceNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : ℝ :=
  ∑ i, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-- The **trace distance** `D(ρ, σ) = ½ ‖ρ − σ‖₁`. -/
noncomputable def traceDist {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ σ : Matrix ι ι ℂ) : ℝ :=
  traceNorm (ρ - σ) / 2

/-- A **density operator**: positive semidefinite with unit trace. -/
def IsDensity {ι : Type*} [Fintype ι] (ρ : Matrix ι ι ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- A **quantum channel** (CPTP map) from operators on `ℂ^ι` to operators on `ℂ^κ`, in Kraus
form: `Φ(ρ) = ∑_k K_k ρ K_k†` for finitely many `K_k` with `∑_k K_k† K_k = I`. -/
def IsChannel {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (Φ : Matrix ι ι ℂ → Matrix κ κ ℂ) : Prop :=
  ∃ (m : ℕ) (K : Fin m → Matrix κ ι ℂ), ∑ k, (K k)ᴴ * K k = 1 ∧
    ∀ ρ, Φ ρ = ∑ k, K k * ρ * (K k)ᴴ

/-- The pure density operator `|v⟩⟨v|`. -/
noncomputable def pureDM {ι : Type*} (v : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => v i * conj (v j)

/-- The states `ρ_0, ρ_1, …` of a chain of quantum operations: `ρ_{t+1} = Ψ_t(Φ_t(ρ_t))`, where
`Φ_t` is the `t`-th subroutine and `Ψ_t` an arbitrary operation interleaved after it (the
dimensions `d_t`, `e_t` may change from step to step). -/
noncomputable def chainState {d e : ℕ → Type}
    (Φ : ∀ t, Matrix (d t) (d t) ℂ → Matrix (e t) (e t) ℂ)
    (Ψ : ∀ t, Matrix (e t) (e t) ℂ → Matrix (d (t + 1)) (d (t + 1)) ℂ)
    (ρ₀ : Matrix (d 0) (d 0) ℂ) : ∀ t, Matrix (d t) (d t) ℂ
  | 0 => ρ₀
  | t + 1 => Ψ t (Φ t (chainState Φ Ψ ρ₀ t))

end ClonableQMASep.Main


