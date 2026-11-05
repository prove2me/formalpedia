-- Prove2me | Definitions.Def_DegenNRM_msMu
-- name    : DegenNRM_msMu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:33:59.791838+00:00
-- url     : https://prove2.me/theorems/5c88e71e-2fd7-4f02-9339-803141240e55
-- title:
--   The constant $\mu$ of Lemma 15 (Mangasarian–Shiau)
-- statement:
--   For a real $\ell\times k$ matrix $\hat A$,
--   $$\mu=\sup_v\Big\{\|v\|_1\;:\;\|v^\top\hat A\|_1=1,\ v\ge0,\ \text{the rows of }\hat A\text{ corresponding to the nonzero entries of }v\text{ are linearly independent}\Big\}.$$
--   It is the Lipschitz constant of the solution set of $\hat Ax\le b$ with respect to $b$ in Lemma 15.
--
--   **Formalization Note** The supremum is that of a set of reals; Lemma 15 also asserts that the set is bounded above. When the set is empty (for instance $\hat A=0$) this is Lean's $\sup\emptyset=0$.
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, Lemma 15, p.36

import Mathlib

namespace DegenNRM

/-- **The constant `µ` of Lemma 15** (Mangasarian and Shiau 1987, Theorem 2.2, as quoted in
Jiang, Ma & Zhang, arXiv:2210.07996v5, Lemma 15, p.36):

`µ = sup_v { ‖v‖₁ : ‖vᵀ Â‖₁ = 1, v ≥ 0, the rows of Â corresponding to the nonzero entries of v
are linearly independent }`

for a real `ℓ × k` matrix `Â`.

**Formalization Note.** The supremum is `sSup` of a set of reals; Lemma 15 (a milestone of this
mission) also asserts that the set is bounded above, so `µ` is finite. When the set is empty
(e.g. `Â = 0`) this is Lean's `sSup ∅ = 0`. -/
noncomputable def msMu {ℓ k : ℕ} (A : Matrix (Fin ℓ) (Fin k) ℝ) : ℝ :=
  sSup {μ | ∃ v : Fin ℓ → ℝ, μ = ∑ i, |v i| ∧ (∑ j, |∑ i, v i * A i j|) = 1 ∧ 0 ≤ v ∧
    LinearIndependent ℝ (fun i : {i : Fin ℓ // v i ≠ 0} => A i.1)}

end DegenNRM


