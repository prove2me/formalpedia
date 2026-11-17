-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_alg2Loop
-- name    : IntroDelayAMDP_Supplement_alg2Loop
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:48:15.199461+00:00
-- url     : https://prove2.me/theorems/6b80ef2e-820e-486b-aa9f-7dfd0fdba850
-- title:
--   Algorithm 2 — the outer loop
-- statement:
--   The outer loop of **Algorithm 2**. While more than $\sqrt K\theta$ indices remain in $R$: set $m_j=|R|$, run the inner loop to obtain $R_j$, record the region with
--   $$\Lambda_j=\lambda I+\frac1{m_j}\sum_{i\in R_j}\phi_i\phi_i^\top,\qquad\hat p_j=\frac{|R_j|}{\sqrt K},\qquad\hat\Sigma_j=\Bigl[\frac1{|R_j|}\sum_{i\in R_j}\phi_i\phi_i^\top\Bigr]_{\text{eigenvalues}<\lambda m_j/|R_j|\ \to\ 0},$$
--   and set $R\leftarrow R\setminus R_j$.
--
--
--   **Formalization Note** The eigenvalue truncation is the continuous functional calculus of the symmetric matrix with the cut-off function (its spectrum is finite). The paper notes that every region keeps more than half of the $m_j$ features it starts with (p.17), so $R$ shrinks in every round and the fuel $|R|+1$ never binds; the guard $R_j\neq\emptyset$ only excludes a non-terminating loop.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 2, lines 2–9, p.17

import Mathlib
import Definitions.Def_IntroDelayAMDP_Supplement_Region
import Definitions.Def_IntroDelayAMDP_Supplement_alg2Inner

namespace IntroDelayAMDP.Supplement

open Classical in
/-- **The outer loop of Algorithm 2** (lines 2–9, printed p.17, PDF p.19, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)):
"while `|R| > √K θ` do: Let `j ← j + 1`, `m_j ← |R|`, `R_j ← R`, and `Λ_j ← λI + (1/m_j) ∑_{i∈R_j} ϕ_iϕ_iᵀ`.
[inner loop] Let `C_j ← …` be the `j`-th region. Let `p̂_j ← |R_j|/√K` be its empirical probability. Let
`Σ̂_j ← (1/|R_j|) ∑_{i∈R_j} ϕ_iϕ_iᵀ` with all eigenvalues below `λm_j/|R_j|` truncated to zero. Let
`R ← R \ R_j`."
`alg2Loop rule ϕ λ r √K θ fuel R acc` appends the regions built from the remaining index set `R` to the
list `acc` of regions built so far, with `r = 2d log(1 + 1/λ)`.

**Formalization Note.** The truncated covariance is `cfc (x ↦ if x < λm_j/|R_j| then 0 else x)` applied to the
symmetric matrix `(1/|R_j|) ∑ ϕ_iϕ_iᵀ` (continuous functional calculus = spectral decomposition; the
spectrum is finite, so the cut-off function is admissible). The page shows that "every region keeps more
than half of the `m_j` features it starts with" (printed p.17), so `R` strictly shrinks in each round and
`fuel = |R| + 1` rounds suffice; the guard `R_j ≠ ∅` (which then always holds) only rules out a loop
that would not terminate. -/
noncomputable def alg2Loop {d : ℕ} (rule : RemovalRule d) (ϕ : ℕ → Fin d → ℝ) (lam r : ℝ)
    (sqrtK : ℕ) (θ : ℝ) : ℕ → Finset ℕ → List (Region d) → List (Region d)
  | 0, _, acc => acc
  | fuel + 1, R, acc =>
    if (sqrtK : ℝ) * θ < R.card then
      let mj := R.card
      let Rj := alg2Inner rule ϕ lam r mj (R.card + 1) R
      if Rj.Nonempty then
        let Λ : Matrix (Fin d) (Fin d) ℝ :=
          lam • 1 + (1 / (mj : ℝ)) • ∑ i ∈ Rj, Matrix.vecMulVec (ϕ i) (ϕ i)
        let S : Matrix (Fin d) (Fin d) ℝ := (1 / (Rj.card : ℝ)) • ∑ i ∈ Rj, Matrix.vecMulVec (ϕ i) (ϕ i)
        let Shat := cfc (fun x : ℝ => if x < lam * mj / Rj.card then 0 else x) S
        alg2Loop rule ϕ lam r sqrtK θ fuel (R \ Rj)
          (acc ++ [{ lam := Λ, phat := (Rj.card : ℝ) / sqrtK, sig := Shat }])
      else acc
    else acc

end IntroDelayAMDP.Supplement


