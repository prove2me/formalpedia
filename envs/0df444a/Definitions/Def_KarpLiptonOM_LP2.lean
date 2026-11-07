-- Prove2me | Definitions.Def_KarpLiptonOM_LP2
-- name    : KarpLiptonOM_LP2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:26.541966+00:00
-- url     : https://prove2.me/theorems/7e8a22e5-2f9e-4903-b96e-0956b513d0a6
-- title:
--   $\mathrm L^{\mathrm P}_2$: languages decided by the minimum of a polynomial-time linear order (Definition A.2.7)
-- statement:
--   A language $L$ is in $\mathrm L^{\mathrm P}_2$ if there are a polynomial $p$ and a polynomial-time predicate $V$ such that for every input $x$ the relation
--   $$
--   u \prec_x w \;:\iff\; V(x, u, w) = 1
--   $$
--   is a strict linear order on $\{0,1\}^{p(|x|)}$ whose minimum starts with $1$ if $x \in L$ and with $0$ if $x \notin L$.
--
--   This is the order-based definition (Korten–Pitassi); the paper uses only this definition.
--
--   **Formalization Note** $p(n) \ge 1$ for every $n$, the paper's standing convention that polynomials are at least $1$.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Definition A.2.7, p.22

import Mathlib
import Definitions.Def_KarpLiptonOM_PolyPred3
import Definitions.Def_KarpLiptonOM_IsStrictLinearOn
import Definitions.Def_KarpLiptonOM_IsMinOn

namespace KarpLiptonOM

/-- `L ∈ L₂^P` (Definition A.2.7, Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), p.22): a polynomial `p` and a polynomial-time `V` such that
for every `x` the relation `u ≺ₓ w :⇔ V(x, u, w) = 1` is a strict linear order on `{0,1}^{p(|x|)}`
whose minimum starts with `1` if `x ∈ L` and with `0` if `x ∉ L`.

**Formalization Note** `p ≥ 1` is the paper's convention "all polynomials are … at least 1" (p.20),
needed for the minimum to start with a bit. -/
def LP2 : Set (Set (List Bool)) :=
  {L | ∃ (p : Polynomial ℕ) (V : List Bool → List Bool → List Bool → Prop), PolyPred3 V ∧
    (∀ n, 1 ≤ p.eval n) ∧ ∀ x : List Bool, IsStrictLinearOn (p.eval x.length) (V x) ∧
      ∀ μ, IsMinOn (p.eval x.length) (V x) μ →
        (x ∈ L → μ.head? = some true) ∧ (x ∉ L → μ.head? = some false)}

end KarpLiptonOM


