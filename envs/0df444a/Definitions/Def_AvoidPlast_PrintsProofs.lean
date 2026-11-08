-- Prove2me | Definitions.Def_AvoidPlast_PrintsProofs
-- name    : AvoidPlast_PrintsProofs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:48:32.336819+00:00
-- url     : https://prove2.me/theorems/c3a27d3d-6e0d-47b6-a04c-8e6292dac10d
-- title:
--   The conclusion of Theorem 5.12
-- statement:
--   The conclusion of Theorem 5.12 for a proof-printing machine $M$, with $\mathrm{solves}(x)$ standing for "$A(x)$ solves Avoid$_C$". For every sufficiently large $n$ and $x\in\{0,1\}^n$:
--
--   1. if $M(x)\ne\bot$, then $M(x)$ is a PCP proof accepted with probability $1$;
--   2. if $x\notin L$, then $M(x)=\bot$;
--   3. if $x\in L$ and $M(x)=\bot$, then $\mathrm{solves}(x)$.
--
--   Consequently, for distributions $D_n$ supported on $\{0,1\}^n$ and $p:\mathbb N\to[0,1]$, if eventually $\Pr_{x\sim D_n}[\mathrm{solves}(x)]\le p(n)$, then eventually $\Pr_{x\sim D_n}[x\in L\text{ and }M(x)=\bot]\le p(n)$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.12, pp.27–28

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_PCPSystem
import Definitions.Def_AvoidPlast_result

namespace AvoidPlast

/-- The conclusion of Theorem 5.12 for a proof-printing machine `M` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), pp.27–28), with `solves x`
standing for "`A(x)` solves `Avoid_C`". For every sufficiently large `n` and every `x ∈ {0,1}^n`:

1. if `M(x) ≠ ⊥`, then `M(x)` is a PCP proof accepted with probability 1;
2. if `x ∉ L`, then `M(x) = ⊥`;
3. if `x ∈ L` and `M(x) = ⊥`, then `solves x`.

"Consequently": for distributions `D_n` supported on `{0,1}^n` and `p : ℕ → [0,1]`, if eventually
`Pr_{x∼D_n}[solves x] ≤ p(n)`, then eventually `Pr_{x∼D_n}[x ∈ L and M(x) = ⊥] ≤ p(n)`. -/
def PrintsProofs (S : PCPSystem) (L : Set (List Bool)) (solves : List Bool → Prop) (M : Machine 1) :
    Prop :=
  (∀ᶠ n : ℕ in Filter.atTop, ∀ x : List Bool, x.length = n →
    (∀ π : List Bool, result M x = some π → π.length = S.proofLen n ∧
      ∀ ρ : List Bool, ρ.length = S.randLen n → Accepts S.V ![x, ρ, π]) ∧
    (x ∉ L → result M x = none) ∧
    (x ∈ L → result M x = none → solves x)) ∧
  ∀ (D : ℕ → PMF (List Bool)) (p : ℕ → ℝ),
    (∀ n, ∀ x ∈ (D n).support, x.length = n) → (∀ n, 0 ≤ p n ∧ p n ≤ 1) →
    (∀ᶠ n : ℕ in Filter.atTop, (D n).toOuterMeasure {x | solves x} ≤ ENNReal.ofReal (p n)) →
    ∀ᶠ n : ℕ in Filter.atTop,
      (D n).toOuterMeasure {x | x ∈ L ∧ result M x = none} ≤ ENNReal.ofReal (p n)

end AvoidPlast


