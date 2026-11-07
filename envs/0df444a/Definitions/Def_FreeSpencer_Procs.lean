-- Prove2me | Definitions.Def_FreeSpencer_Procs
-- name    : FreeSpencer_Procs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:56.401239+00:00
-- url     : https://prove2.me/theorems/34630643-c5d6-42dc-8e13-1295df419a34
-- title:
--   The numerical procedures and their properties
-- statement:
--   The procedures Prepare, the movement basis and the solver as data, and their properties from Section 7.2, on the states the walk reaches ($H$ symmetric, $\|H\|\le n$, $0\preceq C\preceq I$):
--
--   1. Preparation holds $H$ fixed and decreases $C$; its trace is charged to the cut loss $a$ and the cleanup loss $u$; $a$ is a whole number of cuts of trace $\alpha_\ell$; the potential drops by at least $(t_\ell/2)a$; each discarded rank costs at most $2\delta$; on return either the recorded loss exceeds $\ell/32$, or the positive eigenvalues of $C$ are at least $2\delta$ and the no-spike condition at $t_\ell$ holds.
--   2. The basis is orthonormal, vanishes on the newly frozen coordinates $F$, is perpendicular to the current point, $\frac12P_W\preceq C$, and $\dim W\ge2\mathrm{Tr}\,C-\mathrm{rank}\,C-|F|-1$.
--   3. Computed values have error at most $\epsilon_A/3$, and the computed density for $f$ is a density within $\epsilon_A/(3s^2)$ of the optimal one in Hilbert–Schmidt norm.
--
--   **Formalization Note** Section 7.2 "separates the argument from the precision of the implementation", and Proposition 7.9 assumes "the properties of the procedures". So the walk is modelled over any procedures with these properties. The per-call cleanup form and the basis clause are what Lemma C.2, Lemma 7.1, Remark 7.2 and Appendix F.4 provide; the page's total $\ell/1024$ follows because the covariance range never grows. No exact eigendecomposition is assumed.
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 7.2, pp.50–51; p.52; Lemma C.2, pp.79–80; Lemma 7.1, Remark 7.2, p.49; Appendix F.4, p.90

import Mathlib
import Definitions.Def_FreeSpencer_Params
import Definitions.Def_FreeSpencer_lift
import Definitions.Def_FreeSpencer_pot
import Definitions.Def_FreeSpencer_covForm
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- The potential `E(H, C)` of a mode on the lifted family, with all `n` coordinates kept in the
coefficient space (Remark 7.2, p.49). -/
noncomputable abbrev Epot {n m : ℕ} (par : Params) (A : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  pot par.q par.θ par.κ (liftFam A) H C

/-- The soft maximum `f(H)` of a mode. -/
noncomputable abbrev fpot {m : ℕ} (par : Params) (H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) : ℝ :=
  softMax par.q par.θ par.κ H

/-- The numerical procedures of Algorithms 2 and 3 as data.
* `prep ℓ d H C` is Prepare at epoch size `ℓ`, recorded loss `d`, center `H`: it returns the new
  covariance, the trace `a` removed by cuts and the trace `u` removed by cleanup.
* `basis C x F` is the orthonormal basis `u₁, …, u_k` of the movement subspace `W`, for the current
  point `x` and the set `F` of newly frozen coordinates.
* `solveF H` is the computed value and density of `f` at `H`; `solveE H C` the computed value of `E`.

Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 7.2, pp.50–51; Algorithm 2, p.78.

**Formalization Note** Section 7.2 separates "the argument from the precision of the implementation"
and Proposition 7.9 assumes "the properties of the procedures". So the walk is modelled over any
procedures with those properties (`Procs.Spec`), which specializes to Algorithm 3. -/
structure Procs (n m : ℕ) where
  prep : ℕ → ℝ → Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ → Matrix (Fin n) (Fin n) ℝ →
    Matrix (Fin n) (Fin n) ℝ × ℝ × ℝ
  basis : Matrix (Fin n) (Fin n) ℝ → (Fin n → ℝ) → Finset (Fin n) → List (Fin n → ℝ)
  solveF : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ → ℝ × Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ
  solveE : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ → Matrix (Fin n) (Fin n) ℝ → ℝ

/-- Positive eigenvalues of `C` are at least `2δ`: `2δ ‖u‖² ≤ uᵀ C u` on `ran C`. -/
def CovFloor {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ u, InRan C u → 2 * deltaC * (u ⬝ᵥ u) ≤ u ⬝ᵥ (C *ᵥ u)

/-- The movement covariance `Q = ½ P_W` of an orthonormal list spanning `W`. -/
noncomputable def moveCov {n : ℕ} (l : List (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (l.map fun u => Matrix.vecMulVec u u).sum

/-- The properties of the procedures, on the states the walk can reach (`H` symmetric,
`‖H‖ ≤ n`, `0 ⪯ C ⪯ I`):

* Preparation holds `H` fixed and decreases `C`; its trace is charged to `a + u`; `a` is a whole
  number of cuts of trace `α_ℓ`; the potential drops by at least `(t_ℓ/2) a`; each discarded rank
  costs at most `2δ` of cleanup; on return either the recorded loss exceeds `ℓ/32`, or the covariance
  has positive eigenvalues at least `2δ` and satisfies the no-spike condition.
* The basis is orthonormal, lies in `V` (zero on `F`, perpendicular to `x`), has `½ P_W ⪯ C`, and
  `dim W ≥ 2 Tr C - rank C - codim V` with `codim V ≤ |F| + 1`.
* The solver has value errors at most `ε_A/3` and density error at most `ε_A/(3s²)` in
  Hilbert–Schmidt norm, and its density is feasible.

Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Section 7.2, pp.50–51; p.52; Lemma C.2, pp.79–80; Lemma 7.1, p.49; Remark 7.2,
p.49; Appendix F.4, p.90.

**Formalization Note** The page states the cleanup bound as a total, `ℓ/1024`, over a trial. The
per-call form here is what the appendix proves (each discard lowers the rank and removes trace below
`2δ`), and the total follows because the covariance range never grows. The basis clause is the
form App. F's Project provides, so no exact eigendecomposition is assumed. -/
structure Procs.Spec {n m : ℕ} (P : Procs n m) (A : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (par : Params) : Prop where
  prep_order : ∀ ℓ d H C, H.IsSymm → ‖H‖ ≤ n → C.PosSemidef → (1 - C).PosSemidef →
    (P.prep ℓ d H C).1.PosSemidef ∧ (C - (P.prep ℓ d H C).1).PosSemidef
  prep_trace : ∀ ℓ d H C, H.IsSymm → ‖H‖ ≤ n → C.PosSemidef → (1 - C).PosSemidef →
    0 ≤ (P.prep ℓ d H C).2.1 ∧ 0 ≤ (P.prep ℓ d H C).2.2 ∧
    Matrix.trace C - Matrix.trace (P.prep ℓ d H C).1 = (P.prep ℓ d H C).2.1 + (P.prep ℓ d H C).2.2
  prep_cut : ∀ ℓ d H C, H.IsSymm → ‖H‖ ≤ n → C.PosSemidef → (1 - C).PosSemidef →
    ∃ k : ℕ, (P.prep ℓ d H C).2.1 = k * alphaEll n m ℓ
  prep_drop : ∀ ℓ d H C, 1 ≤ ℓ → ℓ ≤ n → H.IsSymm → ‖H‖ ≤ n → C.PosSemidef → (1 - C).PosSemidef →
    Epot par A H (P.prep ℓ d H C).1 ≤ Epot par A H C - tEll ℓ / 2 * (P.prep ℓ d H C).2.1
  prep_cleanup : ∀ ℓ d H C, H.IsSymm → ‖H‖ ≤ n → C.PosSemidef → (1 - C).PosSemidef →
    (P.prep ℓ d H C).2.2 ≤ 2 * deltaC * ((C.rank : ℝ) - ((P.prep ℓ d H C).1.rank : ℝ))
  prep_return : ∀ ℓ d H C, 1 ≤ ℓ → ℓ ≤ n → H.IsSymm → ‖H‖ ≤ n → C.PosSemidef → (1 - C).PosSemidef →
    (ℓ : ℝ) / 32 < d + (P.prep ℓ d H C).2.1 + (P.prep ℓ d H C).2.2 ∨
      (CovFloor (P.prep ℓ d H C).1 ∧
        NoSpike par.q par.θ par.κ (liftFam A) H (P.prep ℓ d H C).1 (tEll ℓ))
  basis_orthonormal : ∀ C x F, C.PosSemidef → (1 - C).PosSemidef →
    (P.basis C x F).Pairwise (fun u w => u ⬝ᵥ w = 0) ∧ ∀ u ∈ P.basis C x F, u ⬝ᵥ u = 1
  basis_mem : ∀ C x F, C.PosSemidef → (1 - C).PosSemidef → ∀ u ∈ P.basis C x F,
    (∀ i ∈ F, u i = 0) ∧ u ⬝ᵥ x = 0
  basis_le : ∀ C x F, C.PosSemidef → (1 - C).PosSemidef → (C - moveCov (P.basis C x F)).PosSemidef
  basis_dim : ∀ C x F, C.PosSemidef → (1 - C).PosSemidef →
    2 * Matrix.trace C - (C.rank : ℝ) - ((F.card : ℝ) + 1) ≤ ((P.basis C x F).length : ℝ)
  solveF_value : ∀ H, H.IsSymm → ‖H‖ ≤ n → |(P.solveF H).1 - fpot par H| ≤ epsA / 3
  solveF_density : ∀ H, H.IsSymm → ‖H‖ ≤ n → IsDensity (P.solveF H).2 ∧
    Real.sqrt (Matrix.trace (((P.solveF H).2 - softOpt par.q par.θ par.κ H)ᵀ *
      ((P.solveF H).2 - softOpt par.q par.θ par.κ H))) ≤ epsA / (3 * sDim n (2 * m) ^ 2)
  solveE_value : ∀ H C, H.IsSymm → ‖H‖ ≤ n → C.PosSemidef → (1 - C).PosSemidef →
    |P.solveE H C - Epot par A H C| ≤ epsA / 3

end FreeSpencer


