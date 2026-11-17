-- Prove2me | Definitions.Def_CompNonlocal_Supplement_IsCertificateK
-- name    : CompNonlocal_Supplement_IsCertificateK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:06:43.112321+00:00
-- url     : https://prove2.me/theorems/d688259a-d0c4-4f0b-870a-e0037409fe85
-- title:
--   Certificates of computational nonlocality (Definition 10)
-- statement:
--   A game $G$ is a $(c,s)$-**certificate** for a state $\omega$ on $n_A+n_B$ qubits if $Q$, $A$, $B$, $\mathrm{Val}$ are uniform quantum polynomial-time, $k(\kappa)$ is polynomially bounded and polynomial-time computable, $c,s:\mathbb N\to[0,1]$, and
--
--   1. **completeness:** for all sufficiently large $\kappa$, the honest players on copies of $\omega$ are accepted with probability at least $c(\kappa)$;
--   2. **soundness:** for every pair of polynomial-size circuit families $A',B'$ with classical advice and every family of separable states $\tau$ on the same registers, for all sufficiently large $\kappa$ (onset depending on the strategy), the acceptance probability is at most $s(\kappa)$;
--   3. the gap $c(\kappa)-s(\kappa)$ exceeds $1/\mathrm{poly}(\kappa)$ for all sufficiently large $\kappa$.
--
--   **Formalization Note** Separability is the published `IsSeparableDensity`. $1/\mathrm{poly}$ is $1/(q(\kappa)+1)$ for a polynomial $q$ with natural coefficients.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), Definition 10, p.25

import Mathlib
import Definitions.Def_CompNonlocal_Supplement_Game
import Definitions.Def_CompNonlocal_Uniform
import Definitions.Def_CompNonlocal_PolySize
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability

set_option autoImplicit false

namespace CompNonlocal.Supplement

open QAlgorithms.Complexity

/-- A `(c, s)`-certificate of computational nonlocality. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 10, p.25: "For functions
c, s : N → [0, 1], we say that a state ω_AB ∈ S(H_A ⊗ H_B) is (c, s)-computationally nonlocal if
there exists a polynomial-time computable, polynomially bounded k = k(κ), a game G(ω_AB, k, ·, c, s),
A(·), B(·) ∈ QPT(·), V = (Q, Val) ∈ QPT(·) with the following asymptotic guarantees:
1. (Completeness) If G(ω_AB, k, κ, c, s) was run in mode (i) with A(κ), B(κ) then, for all
sufficiently large κ, Pr[V accepts] ≥ c(κ),
2. (Soundness) For every pair of quantum circuit families A′, B′ of polynomial size with classical
advice of polynomial length, and every family of separable states {τ_AB}, for all sufficiently large
κ, with the onset allowed to depend on the fixed strategy, mode (ii) satisfies Pr[V accepts] ≤ s(κ).
The gap is defined as γ(κ) := c(κ) − s(κ). We require γ(κ) > 1/poly(κ) for all sufficiently large κ."

`IsCertificateK G ω cc s`: the game `G` (Definition 9, `Game.accK`) certifies the state `ω` on
`n_A + n_B` qubits with completeness `cc` and soundness `s`.

**Formalization Note** Separable states are the published `QAlgorithms.Entanglement.IsSeparableDensity`
(finite convex combinations of products of density matrices) on the same registers `n_A`, `n_B` as
`ω`. "Polynomial-time computable" `k`: a polynomial-time machine maps `1^κ` to `1^{k(κ)}`. "1/poly"
is `1 / (q(κ) + 1)` for some `q : Polynomial ℕ`. -/
def IsCertificateK (G : Game) {nA nB : ℕ} (ω : Matrix (Bits nA × Bits nB) (Bits nA × Bits nB) ℂ)
    (cc s : ℕ → ℝ) : Prop :=
  Uniform G.Qg ∧ Uniform G.A ∧ Uniform G.B ∧ Uniform G.Val ∧
    (∃ p : Polynomial ℕ, ∀ κ, G.k κ ≤ p.eval κ) ∧
    (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ κ, g (unary κ) = unary (G.k κ)) ∧
    (∀ κ, 0 ≤ cc κ ∧ cc κ ≤ 1) ∧ (∀ κ, 0 ≤ s κ ∧ s κ ≤ 1) ∧
    (∀ᶠ κ in Filter.atTop, cc κ ≤ G.accK κ G.A G.B ω) ∧
    (∀ A' B' : Family, PolySize A' → PolySize B' →
      ∀ τ : ℕ → Matrix (Bits nA × Bits nB) (Bits nA × Bits nB) ℂ,
        (∀ κ, QAlgorithms.Entanglement.IsSeparableDensity (τ κ)) →
        ∀ᶠ κ in Filter.atTop, G.accK κ A' B' (τ κ) ≤ s κ) ∧
    (∃ q : Polynomial ℕ, ∀ᶠ κ in Filter.atTop, 1 / ((q.eval κ : ℕ) + 1 : ℝ) < cc κ - s κ)

end CompNonlocal.Supplement


