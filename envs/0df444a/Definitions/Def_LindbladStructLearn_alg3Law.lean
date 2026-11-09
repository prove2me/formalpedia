-- Prove2me | Definitions.Def_LindbladStructLearn_alg3Law
-- name    : LindbladStructLearn_alg3Law
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:09:50.143596+00:00
-- url     : https://prove2.me/theorems/f8313b39-910e-4324-b98f-813007ba7d25
-- title:
--   Output law of Algorithm 3: $(\ell, Y_{\overline P}(x))$
-- statement:
--   Algorithm 3 with threshold $\Gamma \in \mathbb N$ and time $t$ samples $\ell \in \{0,1,\dots,\Gamma\}$ with $\Pr[0] = 2^{-\Gamma}$ and $\Pr[\ell] = 2^{-\ell}$ for $1 \le \ell \le \Gamma$; it outputs $Y_{\overline P}(x) = 0$ if $\ell = 0$ and otherwise $Y_{\overline P}(x) = \frac{2^\ell t^\ell}{\ell!} Z^{(\ell)}_{\overline P}(x)$ with $Z^{(\ell)}$ from Algorithm 2. This is the law of the pair $(\ell, Y)$.
--
--   **Formalization Note** The printed input allows $\Gamma = +\infty$; only finite $\Gamma$ is used ((5.79)) and is defined here. The sampled degree is kept in the outcome because Lemma 4.10 bounds $|Y|$ in terms of it.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Algorithm 3, p.32

import Mathlib
import Definitions.Def_LindbladStructLearn_alg2Law

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The law of `(ℓ, Y_P̄(x))` in Algorithm 3 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.32): sample `ℓ ∈ {0,…,Γ}` with
`Pr[0] = 2^(−Γ)` and `Pr[ℓ] = 2^(−ℓ)` (`1 ≤ ℓ ≤ Γ`); output `Y = 0` if `ℓ = 0`, else
`Y = (2^ℓ t^ℓ/ℓ!) Z^(ℓ)_P̄(x)` with `Z^(ℓ)` from Algorithm 2.

**Formalization Note** The threshold is a natural number `Γ` (the printed `Γ ∈ ℕ ∪ {+∞}` is only
used with finite `Γ`; Lemma 4.10 says "any threshold Γ ≥ 0"). The sampled degree is kept in the
outcome because Lemma 4.10 bounds `|Y|` in terms of it. -/
def alg3Law {n k : ℕ} (x : Idx n k → ℂ) (P : Pauli n × Pauli n) (Γ : ℕ) (t : ℝ) :
    FinDist (ℕ × ℂ) :=
  FinDist.bind
    (List.map (fun ℓ => (if ℓ = 0 then (1 / 2 : ℝ) ^ Γ else (1 / 2 : ℝ) ^ ℓ, ℓ)) (List.range (Γ + 1)))
    fun ℓ => if ℓ = 0 then [(1, (0, 0))]
      else List.map (fun o => (o.1, (ℓ, ((2 : ℂ) ^ ℓ * (t : ℂ) ^ ℓ / (ℓ.factorial : ℂ)) * o.2)))
        (alg2Law x P ℓ)

end LindbladStructLearn


