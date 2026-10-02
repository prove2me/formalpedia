-- Prove2me | Definitions.Def_TeschlQM_Atomic_atomicHamiltonian
-- name    : TeschlQM_Atomic_atomicHamiltonian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T08:56:54.01457+00:00
-- url     : https://prove2.me/theorems/467dd071-1f7e-4d64-a78c-e8d5068aba9d
-- title:
--   Atomic Hamiltonian H^(N) with N electrons (11.6)–(11.7)
-- statement:
--   Consider an atom with $N$ electrons at positions $x_1, \dots, x_N \in \mathbb R^3$ and nucleus fixed at the origin. On $L^2(\mathbb R^{3N})$ the **atomic Hamiltonian** is
--   $$H^{(N)} = -\sum_{j=1}^N \Delta_j - \sum_{j=1}^N V_{ne}(x_j) + \sum_{j=1}^N \sum_{j<k} V_{ee}(x_j - x_k), \qquad \mathfrak D(H^{(N)}) = H^2(\mathbb R^{3N}),$$
--   where $V_{ne}$ describes the interaction of one electron with the nucleus and $V_{ee}$ the interaction of two electrons:
--   $$V_j(x) = \frac{\gamma_j}{|x|}, \qquad \gamma_j > 0,\ j = ne, ee.$$
--   Thus $H^{(N)} = H_0 + V^{(N)}$ with $H_0 = -\Delta$ on $\mathbb R^{3N}$. No centre-of-mass motion is removed and no symmetry (Pauli principle) is imposed.
--
--   This is the operator of the HVZ theorem.
--
--   **Formalization Note.** $\mathbb R^{3N}$ is `EuclideanSpace ℝ (Fin N × Fin 3)` and `electron x j` $= x_j \in \mathbb R^3$, so $|x|^2 = \sum_j |x_j|^2$ and $-\sum_j \Delta_j = -\Delta$. The double sum $\sum_{j=1}^N\sum_{j<k}$ is read as the sum over pairs $1 \le j < k \le N$. `atomicHamiltonian γne γee N` is the `LinearPMap` sum `freeHamiltonian + mulOp V^{(N)}`, whose domain is $H^2(\mathbb R^{3N}) \cap \mathfrak D(V^{(N)})$; that this equals $H^2(\mathbb R^{3N})$, as (11.6) says, is part of Theorem 11.1. The parameters $\gamma_{ne}, \gamma_{ee}$ are arguments; their positivity is a hypothesis of the theorems. On the null set where a denominator vanishes, Lean's convention $a/0 = 0$ applies, which does not change the multiplication operator.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 241, Section 11.1, Eqs. (11.6)–(11.7)

import Mathlib
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian

namespace TeschlQM.Atomic

open MeasureTheory

/-- The position `x_j ∈ ℝ³` of the `j`-th electron in the configuration
`x = (x_1, …, x_N) ∈ ℝ^{3N}`, where `ℝ^{3N}` is `EuclideanSpace ℝ (Fin N × Fin 3)` and
`x_j = (x_{j,1}, x_{j,2}, x_{j,3})`. -/
noncomputable def electron {N : ℕ} (x : EuclideanSpace ℝ (Fin N × Fin 3)) (j : Fin N) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun a => x (j, a))

/-- Teschl (11.6)–(11.7), p. 241: the potential of an atom with `N` electrons and nucleus fixed
at the origin,
`V^{(N)}(x) = -∑_{j=1}^N V_ne(x_j) + ∑_{1 ≤ j < k ≤ N} V_ee(x_j - x_k)`, with
`V_ne(x) = γ_ne/|x|`, `V_ee(x) = γ_ee/|x|`. (At the null set where a denominator vanishes Lean's
`a / 0 = 0` applies; this does not affect the multiplication operator.) -/
noncomputable def atomicPotential (γne γee : ℝ) (N : ℕ) (x : EuclideanSpace ℝ (Fin N × Fin 3)) :
    ℝ :=
  -(∑ j : Fin N, γne / ‖electron x j‖) +
    ∑ j : Fin N, ∑ k ∈ Finset.univ.filter (fun k : Fin N => j < k),
      γee / ‖electron x j - electron x k‖

/-- Teschl (11.6), p. 241: the **atomic Hamiltonian** with `N` electrons,
`H^{(N)} = -∑_{j=1}^N Δ_j - ∑_{j=1}^N V_ne(x_j) + ∑_{j<k} V_ee(x_j - x_k) = H₀ + V^{(N)}`
in `L²(ℝ^{3N})`. It is the operator sum of `H₀ = -Δ` on `H²(ℝ^{3N})` and the multiplication
operator by `V^{(N)}`, so its domain is `H²(ℝ^{3N}) ∩ 𝔇(V^{(N)})`; that this is all of
`H²(ℝ^{3N})`, as (11.6) states, is part of Theorem 11.1. -/
noncomputable def atomicHamiltonian (γne γee : ℝ) (N : ℕ) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))) →ₗ.[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))) :=
  freeHamiltonian (Fin N × Fin 3) +
    mulOp volume (fun x => ((atomicPotential γne γee N x : ℝ) : ℂ))

end TeschlQM.Atomic


