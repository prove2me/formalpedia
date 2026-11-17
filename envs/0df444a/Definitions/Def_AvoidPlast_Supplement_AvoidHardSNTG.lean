-- Prove2me | Definitions.Def_AvoidPlast_Supplement_AvoidHardSNTG
-- name    : AvoidPlast_Supplement_AvoidHardSNTG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:58:29.175539+00:00
-- url     : https://prove2.me/theorems/109a709b-0a93-420d-b88a-50854081b559
-- title:
--   Avoid is hard for $\mathrm{SearchNTimeGuess}[\mathrm{poly}(n),g(n)]$ with success $p$
-- statement:
--   $\mathrm{Avoid}_C$ cannot be solved by any $\mathrm{SearchNTimeGuess}[\mathrm{poly}(n),g(n)]$ algorithm with success $p$ or more over the distributions $\mu_n$: for every non-deterministic polynomial-time machine $M$ and every sufficiently large $n$,
--   $$\Pr_{x\sim\mu_n}[M\text{ solves }\mathrm{Avoid}_C\text{ on }x\text{ with }g(n)\text{ non-deterministic bits}]<p(n).$$
--
--   **Formalization Note** "Every sufficiently large $n$" is what the proofs use (Fact 5.1.1, p.21).
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 3.5, p.14; Theorems 5.1, 5.4, pp.21, 23

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_Supplement_pr
import Definitions.Def_AvoidPlast_Supplement_IsPolyNTime
import Definitions.Def_AvoidPlast_Supplement_SolvesAvoidNDB

namespace AvoidPlast.Supplement

open AvoidPlast

/-- "`Avoid_C` cannot be solved by any `SearchNTimeGuess[poly(n), g(n)]` algorithm with success
`p` or more over `μ`" (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 3.5, p.14; Theorems 5.1, 5.4, pp.21, 23): for every
non-deterministic polynomial-time machine and every sufficiently large `n`, the probability over
`x ∼ μ_n` that it solves `Avoid_C` on `x` with at most `g(n)` non-deterministic bits is below
`p(n)`.

**Formalization Note** Reading: the proofs use the hardness for every sufficiently large `n`
(Fact 5.1.1, p.21); the literal negation of Definition 3.5 ("for every input length") would only
give one bad length per algorithm. -/
def AvoidHardSNTG (μ : ℕ → PMF (List Bool)) (C : List Bool → List Bool → List Bool)
    (ℓin ℓout g : ℕ → ℕ) (p : ℕ → ℝ) : Prop :=
  ∀ (M : Machine 2) (a : ℕ), IsPolyNTime M a → ∀ᶠ n : ℕ in Filter.atTop,
    pr (μ n) (fun x => SolvesAvoidNDB M C ℓin ℓout g x) < p n

end AvoidPlast.Supplement


