-- Prove2me | Definitions.Def_GaussTesting_algorithm1
-- name    : GaussTesting_algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:00:52.455395+00:00
-- url     : https://prove2.me/theorems/af28f555-0ff1-4572-9c2d-3f32eb10fc29
-- title:
--   Algorithm 1 (tolerant quantum property tester)
-- statement:
--   Given a base tester on $k$ copies with accepting effect $E$, a number of rounds $t$, and constants $\varepsilon_1,\varepsilon_2,\alpha_1,\alpha_2$, Algorithm 1 runs the base tester on $t$ fresh blocks $|\psi\rangle^{\otimes k}$, records $s_i=1$ if round $i$ rejects and $s_i=0$ otherwise, and computes
--
--   $$
--   s=\frac1t\sum_{i=1}^t s_i,\qquad (q_1,q_2)=(\alpha_1\varepsilon_1^2,\ \alpha_2\varepsilon_2^2),\qquad \theta=\theta(q_1,q_2).
--   $$
--
--   It returns ACCEPT if $s\le\theta$ and REJECT otherwise.
--
--   **Formalization Note** Algorithm 1 is a block tester with $t$ rounds; $t$ is a parameter, and Theorem 3.6 states how large it must be.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Algorithm 1, p.28

import Definitions.Def_GaussTesting_BlockTester
import Definitions.Def_GaussTesting_threshold

namespace GaussTesting

/-- Algorithm 1 (tolerant quantum property tester): run the base tester (accepting effect `E` on `k`
copies) for `t` rounds, let `s = (1/t) ∑ᵢ sᵢ` be the fraction of rounds that rejected, set
`(q₁, q₂) = (α₁ε₁², α₂ε₂²)` and `θ = threshold q₁ q₂`, and ACCEPT iff `s ≤ θ`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), Algorithm 1, p.28.

**Formalization Note.** Round outcome `true` means the base tester accepted (`sᵢ = 0`), `false` that it
rejected (`sᵢ = 1`). The number of rounds `t` is a parameter; Theorem 3.6 gives its size. -/
noncomputable def algorithm1 {ι : Type*} {k : ℕ} (E : Ell2 (Fin k → ι) →L[ℂ] Ell2 (Fin k → ι))
    (hE₀ : E.IsPositive) (hE₁ : (1 - E).IsPositive) (t : ℕ) (ε₁ ε₂ α₁ α₂ : ℝ) :
    BlockTester ι k where
  rounds := t
  E := E
  E_nonneg := hE₀
  E_le_one := hE₁
  accept s := decide (((Finset.univ.filter (fun i => s i = false)).card : ℝ) / t ≤
    threshold (α₁ * ε₁ ^ 2) (α₂ * ε₂ ^ 2))

end GaussTesting


