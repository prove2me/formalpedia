-- Prove2me | Definitions.Def_CEPolytopeHard_IsApproxCE
-- name    : CEPolytopeHard_IsApproxCE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:25.106281+00:00
-- url     : https://prove2.me/theorems/49d8c621-3d43-460e-b862-fec8476e756d
-- title:
--   $\varepsilon$-correlated equilibrium with finite support
-- statement:
--   Let finitely many players $i$ have strategy sets $X_i$ and utilities $u_i$ on profiles. A finitely supported distribution $\mu$ on profiles is an **$\varepsilon$-correlated equilibrium** if its weights are nonnegative with total mass $1$, it is supported on $X = \prod_i X_i$, and no player gains more than $\varepsilon$ by any swap deviation:
--   $$
--   \mathbb E_{x \sim \mu}\big[u_i(\phi_i(x_i), x_{-i}) - u_i(x)\big] \le \varepsilon \quad \text{for every player } i \text{ and every map } \phi_i : X_i \to X_i .
--   $$
--
--   This is the $\varepsilon$-approximate $\Phi$-equilibrium of Section 2.3 with $\Phi_i$ the set of all maps $X_i \to X_i$ ("swap regret corresponds to correlated equilibria"). It is used for the multilinear games of Theorem 4 and for the constructed game of Claim 4.4.
--
--   **Formalization Note** A map $X_i \to X_i$ is a map on the strategy type that sends $X_i$ into $X_i$; its values outside $X_i$ are never used.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Section 2.3, p.11 (ϵ-approximate Φ-equilibrium) and pp.10–11 (swap regret ↔ correlated equilibria)

import Mathlib

set_option autoImplicit false

namespace CEPolytopeHard

/-- An **ε-correlated equilibrium** with finite support (Anagnostides–Daskalakis–Farina–Golowich–
Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*,
arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, Section 2.3, p.11: "An
ϵ-approximate Φ-equilibrium is a distribution μ ∈ ∆(X) from which no player can profitably
deviate by applying any function ϕ_i ∈ Φ_i. Formally: E_{x∼μ}[u_i(ϕ_i(x_i), x_{−i}) − u_i(x)] ≤ ϵ
for every player i and every deviation ϕ_i ∈ Φ_i", with "swap regret corresponds to correlated
equilibria", i.e. `Φ_i` = all functions `X_i → X_i`, p.10–11).

Players are a finite type `ι`; player `i` has strategies in a type `E i` and strategy set
`X i ⊆ E i`; `u i` is player `i`'s utility on profiles. `μ` is a finitely supported distribution on
profiles (nonnegative weights of total mass 1, supported on `X = ∏ X_i`), and for every player `i`
and every map `φ : X_i → X_i` the expected gain of replacing `x_i` by `φ(x_i)` is at most `ε`.

**Formalization Note** `∆(X)` is the set of finite-support distributions (Notation, p.9). A map
`X_i → X_i` is written as a map `φ : E i → E i` with `Set.MapsTo φ (X i) (X i)`; its values
outside `X i` are never used, since `μ` is supported on `X`. -/
def IsApproxCE {ι : Type*} [DecidableEq ι] {E : ι → Type*} (X : ∀ i, Set (E i))
    (u : ι → ((i : ι) → E i) → ℝ) (ε : ℝ) (μ : ((i : ι) → E i) →₀ ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ (μ.sum fun _ w => w) = 1 ∧ (∀ x ∈ μ.support, ∀ i, x i ∈ X i) ∧
  ∀ (i : ι) (φ : E i → E i), Set.MapsTo φ (X i) (X i) →
    ∑ x ∈ μ.support, μ x * (u i (Function.update x i (φ (x i))) - u i x) ≤ ε

end CEPolytopeHard


