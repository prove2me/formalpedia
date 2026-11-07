-- Prove2me | Definitions.Def_QuantumLTF_Membership_disagree
-- name    : QuantumLTF_Membership_disagree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:31:47.652512+00:00
-- url     : https://prove2.me/theorems/9f3c3321-8c14-4b2c-8dbc-dbaa34c9c644
-- title:
--   Gaussian disagreement $d_{\gamma_n}(f,g)$
-- statement:
--   For $f,g:\mathbb R^n\to\{\pm1\}$, the disagreement under the standard Gaussian distribution $\gamma_n$ on $\mathbb R^n$ is
--   $$d_{\gamma_n}(f,g)=\Pr_{x\sim\gamma_n}[f(x)\ne g(x)].$$
--   This is the error measure in which the mission's learner is judged.
--
--   **Formalization Note** $\gamma_n$ is Mathlib's `stdGaussian` on `EuclideanSpace ℝ (Fin n)`. The value is the real number of a probability measure of the set; the LTFs and constants used here have Borel disagreement sets.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §1.3, unnumbered, p. 6 (PDF p. 7)

import Mathlib

namespace QuantumLTF.Membership

/-- **Gaussian disagreement.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, §1.3, unnumbered, p. 6 (PDF p. 7):
`d_{γ_n}(f, g) := Pr_{x∼γ_n}[f(x) ≠ g(x)]`, with `γ_n` the standard Gaussian on `Rⁿ`
(Mathlib's `ProbabilityTheory.stdGaussian`).

**Formalization Note.** `toReal` of a probability measure is the real probability. For the functions
used in this mission (`ltf`, constants) the set is Borel; `stdGaussian` is a probability measure,
so no junk value arises. -/
noncomputable def disagree {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℤ) : ℝ :=
  (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n)) {x | f x ≠ g x}).toReal

end QuantumLTF.Membership


