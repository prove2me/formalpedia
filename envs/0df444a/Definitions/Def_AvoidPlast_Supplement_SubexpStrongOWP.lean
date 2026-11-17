-- Prove2me | Definitions.Def_AvoidPlast_Supplement_SubexpStrongOWP
-- name    : AvoidPlast_Supplement_SubexpStrongOWP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:10:53.61277+00:00
-- url     : https://prove2.me/theorems/0cb45bc4-a618-4a75-bdbf-e4067143d9f5
-- title:
--   Sub-exponentially secure strong one-way permutations (Definition 6.10)
-- statement:
--   A polynomial-time computable, length-preserving, injective $f$ (a permutation of each $\{0,1\}^n$) and $\rho\in(0,1)$ such that every uniform probabilistic inverter running in time at most $2^{n^\rho}$ satisfies
--   $$\Pr_{u\in\{0,1\}^n,\,I}[I(1^n,u)=f^{-1}(u)]\le n^{-\omega(1)}$$
--   for all sufficiently large $n$.
--
--   **Formalization Note** $I(1^n,u)=f^{-1}(u)$ is written $f(I(1^n,u))=u$, the same event since $f$ is injective; $n^{-\omega(1)}$ is a negligible function.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 6.10, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_QuantumPRC_Negligible
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_InFP
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_Supplement_expBound

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Sub-exponentially secure strong one-way permutations exist (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 6.10, p.38):
a polynomial-time computable, length-preserving, injective `f` (a permutation of every `{0,1}^n`),
and `ρ ∈ (0,1)`, such that every uniform probabilistic inverter running in time at most `2^{n^ρ}`
has `Pr_{u ∈ {0,1}^n, r}[I(1^n, u) = f^{-1}(u)] ≤ n^{-ω(1)}` for all sufficiently large `n`.

**Formalization Note** `I(1^n, u) = f^{-1}(u)` is written `f(I(1^n, u)) = u`, the same event since
`f` is injective. -/
def SubexpStrongOWP : Prop :=
  ∃ f : List Bool → List Bool, InFP f ∧ (∀ u, (f u).length = u.length) ∧ Function.Injective f ∧
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
    ∀ I : Machine 3, (∀ (n : ℕ) (u r : List Bool), u.length = n → r.length = expBound ρ n →
        HaltsWithin I ![List.replicate n true, u, r] (expBound ρ n)) →
      ∃ ν : ℕ → ℝ, QuantumPRC.Negligible ν ∧ ∀ᶠ n : ℕ in Filter.atTop,
        prob (n + expBound ρ n) (fun ur =>
          f (output I ![List.replicate n true, ur.take n, ur.drop n]) = ur.take n) ≤ ν n

end AvoidPlast.Supplement


