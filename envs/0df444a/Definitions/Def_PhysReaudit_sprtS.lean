-- Prove2me | Definitions.Def_PhysReaudit_sprtS
-- name    : PhysReaudit_sprtS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:44:11.739992+00:00
-- url     : https://prove2.me/theorems/dc218dde-28c1-4427-87de-2f95ea846c4b
-- title:
--   SPRT statistic $S_n$, stopping index $\tau$ and the filtration $\mathcal F_n$
-- statement:
--   Let $0<q_0<t<1$, $z_-=\log(q_0/t)$, $z_+=\log((1-q_0)/(1-t))$ and $A=\log(1/\delta)$. For a sequence $Y_1,Y_2,\dots\in\{0,1\}$ of target outcomes,
--
--   $$
--   S_n=\sum_{i=1}^{n}\{Y_iz_-+(1-Y_i)z_+\},\qquad \tau=\inf\{n\ge1:\ S_n\ge A\ \text{or}\ S_n\le -A\},
--   $$
--
--   with $S_0=0$ and $\tau=\infty$ if neither boundary is reached. The module also defines the filtration $\mathcal F_n=\sigma(Y_1,\dots,Y_n)$ on the space $\{0,1\}^{\mathbb N}$ of target sequences ($\mathcal F_0$ trivial). The increment $Y z_-+(1-Y)z_+$ is the log-likelihood ratio of one observation, $\log(\mathbb P_{q_0}(Y)/\mathbb P_t(Y))$.
--
--   **Formalization Note** The paper's $Y_i$ is coordinate $i-1$ of the sequence (0-based). $\tau$ takes values in $\mathbb N\cup\{\infty\}$.
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), proof of Theorem 4, p.4 (PDF p.5): "Set A = log(1/δ) and z− = log(q0/t) < 0. … Sn = Σ_{i=1}^{n} {Yi z− + (1 − Yi) z+}, τ = inf{n ≥ 1 : Sn ≥ A or Sn ≤ −A}"

import Mathlib
import Definitions.Def_PhysReaudit_Delta

open MeasureTheory

namespace PhysReaudit

/-- The log-likelihood-ratio increment of one target observation `Y`: `Y z₋ + (1 − Y) z₊`
(Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), proof of Theorem 4, p.4 (PDF p.5)), with `Y = 1` encoded as `true`. -/
noncomputable def sprtIncr (q₀ t : ℝ) (y : Bool) : ℝ :=
  if y then zMinus q₀ t else zPlus q₀ t

/-- The SPRT statistic `S_n = Σ_{i=1}^n {Y_i z₋ + (1 − Y_i) z₊}` (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), proof of Theorem 4, p.4 (PDF p.5))
on a sequence of target outcomes `y`, where the paper's `Y_i` is `y (i − 1)` (0-based). `S_0 = 0`. -/
noncomputable def sprtS (q₀ t : ℝ) (y : ℕ → Bool) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, sprtIncr q₀ t (y i)

/-- The SPRT stopping index `τ = inf{n ≥ 1 : S_n ≥ A or S_n ≤ −A}` with `A = log(1/δ)`
(Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), proof of Theorem 4, p.4 (PDF p.5)), valued in `ℕ∞` (`⊤` if no boundary is ever reached). -/
noncomputable def sprtTau (q₀ t δ : ℝ) (y : ℕ → Bool) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : 1 ≤ n ∧ (Real.log (1 / δ) ≤ sprtS q₀ t y n ∨ sprtS q₀ t y n ≤ -Real.log (1 / δ))),
    (n : ℕ∞)

/-- The filtration `F_n = σ(Y_1, …, Y_n)` of the first `n` target outcomes on the target tape `ℕ → Bool`
(coordinates `0, …, n − 1`); `F_0` is trivial. -/
def pastFiltration : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → Bool)) where
  seq n := ⨆ i ∈ Finset.range n, MeasurableSpace.comap (fun y : ℕ → Bool => y i) inferInstance
  mono' m n hmn := by
    refine iSup₂_le fun i hi => ?_
    have hi' : i ∈ Finset.range n := by
      simp only [Finset.mem_range] at hi ⊢; omega
    exact le_iSup₂ (f := fun j (_ : j ∈ Finset.range n) =>
      MeasurableSpace.comap (fun y : ℕ → Bool => y j) inferInstance) i hi'
  le' n := iSup₂_le fun i _ => (measurable_pi_apply i).comap_le

end PhysReaudit


