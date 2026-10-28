-- Prove2me | Definitions.Def_DeFinettiSDP_NoSymm_Random
-- name    : DeFinettiSDP_NoSymm_Random
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:43.461327+00:00
-- url     : https://prove2.me/theorems/7f43b3b4-c11b-4ec1-ac5c-24fa1d4fa2f5
-- title:
--   §2.6, pp. 9–10 — random subsystems, conditional states and expected product error
-- statement:
--   Let $\rho$ be an operator on $n=k+r$ copies of a $d_B$-dimensional system. A permutation $\pi$ lists the $k$ retained systems first and the $r$ systems available for measurement afterward. Measuring the first $m$ of the latter, with $0\le m\le r$, produces an outcome word $z$ and an unnormalized operator $\widetilde\rho_{\vec i\mid z}$ on the retained systems. Its trace $p_z$ is the outcome probability and, when $p_z>0$, the conditional state is $\rho_{\vec i\mid z}=p_z^{-1}\widetilde\rho_{\vec i\mid z}$.
--
--   The **random-subsystem product error** is
--
--   $$
--   E_m(\rho,M)=\frac1{n!}\sum_{\pi}\sum_z p_z\left\|\rho_{\vec i\mid z}-\bigotimes_{s=1}^k\rho_{i_s\mid z}\right\|_1.
--   $$
--
--   Here $\rho_{i_s\mid z}$ is the one-system marginal and the tensor product keeps the ordered positions of $\vec i$. This is exactly the expectation in Theorem 2.5; the auxiliary first-prefix marginal and tensor-step definitions express equation (12).
--
--   **Formalization Note** The paper's $n$ is $k+r$ in Lean. Outcomes of probability zero contribute zero even though their normalized conditional matrix uses Lean's zero inverse. The permutation average is over all $n!$ permutations, so the tuple of retained systems is ordered and uniform.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, Theorem 2.5 p. 9 and equation (12) p. 10

import Mathlib
import Definitions.Def_DeFinettiSDP_NoSymm_Quantum

namespace DeFinettiSDP.NoSymm

open Matrix
open scoped Kronecker ComplexOrder

/-- Permute the tensor factors of a state on `n` copies of B. Precomposition by `π` puts
the original factor `π⁻¹(s)` at position `s`. Uniform averaging makes π versus π⁻¹ immaterial. -/
def permSys {dB n : ℕ} (π : Equiv.Perm (Fin n))
    (ρ : Matrix (Fin n → Fin dB) (Fin n → Fin dB) ℂ) :
    Matrix (Fin n → Fin dB) (Fin n → Fin dB) ℂ :=
  ρ.submatrix (fun x => x ∘ π) (fun x => x ∘ π)

/-- Tensor product of a possibly different operator on each of `k` B systems. -/
def tensorFin {dB k : ℕ} (ω : Fin k → Matrix (Fin dB) (Fin dB) ℂ) :
    Matrix (Fin k → Fin dB) (Fin k → Fin dB) ℂ :=
  fun x y => ∏ s : Fin k, ω s (x s) (y s)

/-- One-system marginal, tracing out every factor except `s` (§2.6, p. 9). -/
noncomputable def marg {dB k : ℕ}
    (τ : Matrix (Fin k → Fin dB) (Fin k → Fin dB) ℂ) (s : Fin k) :
    Matrix (Fin dB) (Fin dB) ℂ :=
  fun c c' => ∑ x, ∑ y,
    if x s = c ∧ y s = c' ∧ (∀ u : Fin k, u ≠ s → x u = y u)
    then τ x y else 0

/-- Marginal on the first `j` systems of `τ`; all later systems are traced out.
The proof `j ≤ k` makes the chosen prefix explicit. -/
noncomputable def keepFirst {dB k : ℕ}
    (τ : Matrix (Fin k → Fin dB) (Fin k → Fin dB) ℂ)
    (j : ℕ) (hj : j ≤ k) : Matrix (Fin j → Fin dB) (Fin j → Fin dB) ℂ :=
  fun b b' => ∑ x, ∑ y,
    if (∀ s : Fin j,
          x (Fin.castLE hj s) = b s ∧ y (Fin.castLE hj s) = b' s) ∧
       (∀ s : Fin k, j ≤ s.val → x s = y s)
    then τ x y else 0

/-- The product of the first `s`-system marginal and the marginal at position `s`,
written on a word of length `s+1` with the new factor last (equation (12), p. 10). -/
noncomputable def tensorStep {dB k : ℕ}
    (τ : Matrix (Fin k → Fin dB) (Fin k → Fin dB) ℂ) (s : Fin k) :
    Matrix (Fin (s.val + 1) → Fin dB) (Fin (s.val + 1) → Fin dB) ℂ :=
  fun b b' =>
    keepFirst τ s.val (Nat.le_of_lt s.isLt)
        (fun i => b (Fin.castAdd 1 i)) (fun i => b' (Fin.castAdd 1 i)) *
      marg τ s (b (Fin.last s.val)) (b' (Fin.last s.val))

/-- Unnormalized state of the `k` kept factors after measuring the first `m` of the `r`
other factors and observing `z`; all remaining factors are traced out. A row/column pair
`x,y` contributes the Born-rule factor `M_z(y_u,x_u)` on a measured factor. The theorem
uses `m ≤ r` and `n = k+r` (the paper's `n-k+1` is `r+1`). -/
noncomputable def condU {dB t : ℕ} (k r : ℕ)
    (σ : Matrix (Fin (k + r) → Fin dB) (Fin (k + r) → Fin dB) ℂ)
    (M : Fin t → Matrix (Fin dB) (Fin dB) ℂ)
    (m : ℕ) (z : Fin m → Fin t) :
    Matrix (Fin k → Fin dB) (Fin k → Fin dB) ℂ :=
  fun b b' => ∑ x, ∑ y,
    if (∀ s : Fin k,
          x (Fin.castAdd r s) = b s ∧ y (Fin.castAdd r s) = b' s) then
      (∏ u : Fin r,
        if hu : u.val < m then
          M (z ⟨u.val, hu⟩) (y (Fin.natAdd k u)) (x (Fin.natAdd k u))
        else if x (Fin.natAdd k u) = y (Fin.natAdd k u) then 1 else 0) * σ x y
    else 0

/-- Probability of a measured outcome string (the trace of its unnormalized state). -/
noncomputable def outcomeWeight {dB t : ℕ} (k r : ℕ)
    (σ : Matrix (Fin (k + r) → Fin dB) (Fin (k + r) → Fin dB) ℂ)
    (M : Fin t → Matrix (Fin dB) (Fin dB) ℂ)
    (m : ℕ) (z : Fin m → Fin t) : ℝ :=
  (Matrix.trace (condU k r σ M m z)).re

/-- Conditional state for an outcome with positive weight. At zero weight Lean's inverse
is zero; all uses multiply its trace distance by the zero outcome probability. -/
noncomputable def conditioned {dB t : ℕ} (k r : ℕ)
    (σ : Matrix (Fin (k + r) → Fin dB) (Fin (k + r) → Fin dB) ℂ)
    (M : Fin t → Matrix (Fin dB) (Fin dB) ℂ)
    (m : ℕ) (z : Fin m → Fin t) :
    Matrix (Fin k → Fin dB) (Fin k → Fin dB) ℂ :=
  (((outcomeWeight k r σ M m z)⁻¹ : ℝ) : ℂ) • condU k r σ M m z

/-- Expected error in Theorem 2.5. The uniform permutation selects ordered kept systems
`i₁,…,i_k`, followed by ordered measured candidates `j₁,…,j_r`. The inner sum is expectation
over outcomes of measuring `j₁,…,j_m`. The paper's `n` is `k+r` here. -/
noncomputable def rsError {dB t : ℕ} (k r : ℕ)
    (ρ : Matrix (Fin (k + r) → Fin dB) (Fin (k + r) → Fin dB) ℂ)
    (M : Fin t → Matrix (Fin dB) (Fin dB) ℂ) (m : ℕ) : ℝ :=
  (1 / ((k + r).factorial : ℝ)) *
    ∑ π : Equiv.Perm (Fin (k + r)),
      ∑ z : Fin m → Fin t,
        outcomeWeight k r (permSys π ρ) M m z *
          WildeQIT.traceNorm
            (conditioned k r (permSys π ρ) M m z -
              tensorFin (fun s => marg (conditioned k r (permSys π ρ) M m z) s))

end DeFinettiSDP.NoSymm


