-- Prove2me | Definitions.Def_RobustQSC_accOp
-- name    : RobustQSC_accOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:48:42.052389+00:00
-- url     : https://prove2.me/theorems/07c512a5-4677-4931-8247-7b288e152924
-- title:
--   The acceptance operator $A$ of Protocol 1
-- statement:
--   For a target $|\psi\rangle$, the acceptance operator is
--
--   $$
--   A=\frac1{2n}\sum_i\sum_{z\in\{0,1\}^{n-1}}|z\rangle\langle z|_{[n]\setminus i}\otimes|\psi^{(i)}_z\rangle\langle\psi^{(i)}_z|_i+\frac1{2n}\sum_i\sum_{z\in\{0,1\}^{n-1}}(H^{\otimes n-1}|z\rangle\langle z|H^{\otimes n-1})_{[n]\setminus i}\otimes|\hat\psi^{(i)}_z\rangle\langle\hat\psi^{(i)}_z|_i,
--   $$
--
--   where $|\psi^{(i)}_z\rangle$ is the post-measurement state of qubit $i$ upon measuring all other qubits of $|\psi\rangle$ in the $Z$ basis with outcome $z$, and $|\hat\psi^{(i)}_z\rangle$ is the analogue for the $X$ basis.
--
--   The whole analysis of Protocol 1 is the analysis of this operator: its acceptance probability on $\rho$ is $\mathrm{Tr}[A\rho]$.
--
--   **Formalization Note** The string $z$ on $[n]\setminus i$ is represented by $x\in\{0,1\}^n$ with $x_i=0$. The $X$ term is written $H^{\otimes n}(|z\rangle\langle z|\otimes HPH)H^{\otimes n}$, equal to $(H^{\otimes n-1}|z\rangle\langle z|H^{\otimes n-1})\otimes P$ because $H^{\otimes n}=H^{\otimes n-1}\otimes H$ and $H^2=I$. If a post-measurement vector is $0$, its term is $0$.
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), §4, p.20 (display for A)

import Definitions.Def_RobustQSC_fourier
import Definitions.Def_QAlgorithms_Defs_LinearSystems

namespace RobustQSC

open QAlgorithms

/-- The (unnormalized) state left on qubit `i` when all other qubits of `|ψ⟩` are measured in the
`Z` basis with outcome `z = x|_{[n]∖i}`: the vector `(ψ(z, 0), ψ(z, 1))`, i.e. `(⟨z| ⊗ I)|ψ⟩`. -/
noncomputable def zHold {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) (i : Fin n) (x : Qubits n) :
    EuclideanSpace ℂ Bool :=
  WithLp.toLp 2 fun c => ψ (Function.update x i c)

/-- The (unnormalized) state left on qubit `i` when all other qubits of `|ψ⟩` are measured in the
`X` basis with outcome `z = x|_{[n]∖i}`: `(⟨z|H^{⊗(n−1)} ⊗ I)|ψ⟩ = H·(ψ̂(z, 0), ψ̂(z, 1))`, since
`H^{⊗n} = H^{⊗(n−1)} ⊗ H` and `H² = I`. -/
noncomputable def xHold {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) (i : Fin n) (x : Qubits n) :
    EuclideanSpace ℂ Bool :=
  act hadamard (WithLp.toLp 2 fun c => fourier ψ (Function.update x i c))

/-- `|z⟩⟨z|_{[n]∖i} ⊗ P_i` with `z = x|_{[n]∖i}`: the operator whose `(y, y')` entry is
`P(y_i, y'_i)` when `y` and `y'` agree with `x` off qubit `i`, and `0` otherwise. -/
noncomputable def restProj {n : ℕ} (i : Fin n) (x : Qubits n) (P : Matrix Bool Bool ℂ) :
    Matrix (Qubits n) (Qubits n) ℂ := by
  classical
  exact Matrix.of fun y y' =>
    if (∀ k, k ≠ i → y k = x k) ∧ (∀ k, k ≠ i → y' k = x k) then P (y i) (y' i) else 0

/-- The acceptance operator of Protocol 1,

$$A = \frac1{2n}\sum_i\sum_{z\in\{0,1\}^{n-1}} |z\rangle\langle z|_{[n]\setminus i}\otimes
  |\psi^{(i)}_z\rangle\langle\psi^{(i)}_z|_i + \frac1{2n}\sum_i\sum_{z\in\{0,1\}^{n-1}}
  (H^{\otimes n-1}|z\rangle\langle z|H^{\otimes n-1})_{[n]\setminus i}\otimes
  |\hat\psi^{(i)}_z\rangle\langle\hat\psi^{(i)}_z|_i,$$

where `|ψ^{(i)}_z⟩` (`|ψ̂^{(i)}_z⟩`) is the normalized post-measurement state of qubit `i` after
measuring all other qubits of `|ψ⟩` in the `Z` (`X`) basis with outcome `z`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles
for total influence*, arXiv:2607.27184 (sha256 09d2692e…), §4, p.20 (display for `A`).

**Formalization Note.**
1. `z ∈ {0,1}^{n−1}` on `[n] ∖ i` is represented by the `x ∈ {0,1}ⁿ` with `x i = false` (its
   restriction to `[n] ∖ i`); `restProj i x P` is `|z⟩⟨z|_{[n]∖i} ⊗ P_i`.
2. The `X` term is written `H^{⊗n} (|z⟩⟨z| ⊗ H P H) H^{⊗n}`, which equals
   `(H^{⊗n−1}|z⟩⟨z|H^{⊗n−1}) ⊗ P` because `H^{⊗n} = H^{⊗n−1} ⊗ H` and `H² = I`.
3. Zero fiber: if the post-measurement vector is `0` (outcome `z` has probability `0` on `|ψ⟩`),
   `normalizedVec 0 = 0` and the term is `0`; Protocol 1 then rejects (`protocol1`). -/
noncomputable def accOp {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  ((2 * (n : ℂ))⁻¹) • ∑ i : Fin n, ∑ x ∈ Finset.univ.filter (fun x : Qubits n => x i = false),
    (restProj i x (pureDensity (normalizedVec (zHold ψ i x))) +
      hadamardN n * restProj i x (hadamard * pureDensity (normalizedVec (xHold ψ i x)) * hadamard) *
        hadamardN n)

/-! ### Sanity tests -/

/-- `accOp` at `n = 0` is `0` (the prefactor `1/(2n)` and the empty sum). -/
example (ψ : EuclideanSpace ℂ (Qubits 0)) : accOp ψ = 0 := by
  simp [accOp]

/-- The `Z` side resolves the identity: with every holdout projector replaced by `I`,
`Σ_{z} |z⟩⟨z|_{[n]∖i} ⊗ I_i = I`. -/
theorem sum_restProj_one {n : ℕ} (i : Fin n) :
    ∑ x ∈ Finset.univ.filter (fun x : Qubits n => x i = false), restProj i x 1 = 1 := by
  classical
  ext y y'
  rw [Matrix.sum_apply]
  simp only [restProj, Matrix.of_apply, Matrix.one_apply]
  by_cases hyy : y = y'
  · subst hyy
    rw [if_pos rfl, Finset.sum_eq_single (Function.update y i false)]
    · simp
      intro k hk
      simp [Function.update_of_ne hk]
    · intro x hx hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [if_neg]
      rintro ⟨h1, -⟩
      apply hne
      ext k
      by_cases hk : k = i
      · subst hk; simp [hx]
      · simp [Function.update_of_ne hk, h1 k hk]
    · simp
  · rw [if_neg hyy]
    apply Finset.sum_eq_zero
    intro x _
    split_ifs with hc h
    · exfalso
      obtain ⟨h1, h2⟩ := hc
      apply hyy
      ext k
      by_cases hk : k = i
      · subst hk; exact h
      · rw [h1 k hk, h2 k hk]
    · rfl
    · rfl

end RobustQSC


