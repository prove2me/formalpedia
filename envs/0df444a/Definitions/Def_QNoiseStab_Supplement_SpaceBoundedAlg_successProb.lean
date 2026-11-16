-- Prove2me | Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg_successProb
-- name    : QNoiseStab_Supplement_SpaceBoundedAlg_successProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:19:59.091511+00:00
-- url     : https://prove2.me/theorems/ecbc27f8-a0e6-4776-85f1-bf110edef483
-- title:
--   Success probability of a space-bounded algorithm computing a multi-output function on a uniform input
-- statement:
--   Let $X$ be a finite alphabet identified with $\mathbb Z_d$ by a bijection $\mathrm{enc}$, and let $f:X^n\to Y^K$ be a multi-output function. The **success probability** of a space-bounded algorithm $\mathcal A$ with post-processing $q$ in computing $f$ on a uniformly random input is
--
--   $$
--   \mathrm{succ}_f(\mathcal A)=\frac1{|X|^n}\sum_{x\in X^n}\ \sum_{o\ \text{computes}\ f(x)}\Pr\nolimits_x[o],
--   $$
--
--   where $\Pr_x[o]$ is the probability of the commit sequence $o$ when $\mathcal A$ queries the phase oracle of $\mathrm{enc}(x)$. It is the probability, over the uniform input and all measurement outcomes, that every output coordinate is committed and every commit is correct.
--
--   The time-space lower bounds for hashing, sorting and matrix-vector product are statements about this quantity.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §2.1–2.2, pp.6–7; Theorem 4.3, p.19; Theorem 5.1, p.26; Theorem 6.6, p.42

import Mathlib
import Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg_commitProb
import Definitions.Def_QNoiseStab_Supplement_CommitsCorrect

set_option autoImplicit false

namespace QNoiseStab.Supplement

open Classical in
/-- The **success probability** of a space-bounded algorithm in computing a multi-output function
`f : Xⁿ → (K → Y)` on a uniformly random input (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §2.1–2.2, pp.6–7; Theorem 4.3, p.19:
"succeeds with probability at least 2^{−ℓ} on inputs uniformly chosen"; Theorem 5.1, p.26;
Theorem 6.6, p.42). The input alphabet `X` is identified with `ZMod d` by `enc` (p.6: "a bijective
map v between X and [d]"), the oracle is `phaseQuery ω (enc ∘ x)`, and the value is
`|X|^{−n} Σ_x Σ_{o computes f x} Pr[o]`: the probability, over the uniform input and the
measurement outcomes, that all commits are correct and every coordinate is committed. -/
noncomputable def SpaceBoundedAlg.successProb {n d : ℕ} [NeZero d] {X W K V Y ι : Type}
    [Fintype X] [Fintype W] [DecidableEq W] [Fintype K] [Fintype V] [Fintype ι] {T : ℕ}
    (enc : X ≃ ZMod d) (ω : ℂ) (A : SpaceBoundedAlg n d W K V ι T) (q : V → Y)
    (f : (Fin n → X) → K → Y) : ℝ :=
  ((Fintype.card X : ℝ) ^ n)⁻¹ *
    ∑ x : Fin n → X, ∑ o : Fin (T + 1) → Option (K × V),
      if CommitsCorrect q (f x) o then A.commitProb ω (fun i => enc (x i)) o else 0

end QNoiseStab.Supplement


