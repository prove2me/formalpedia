-- Prove2me | Definitions.Def_AvoidPlast_Supplement_SubexpOWF
-- name    : AvoidPlast_Supplement_SubexpOWF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:10:07.744229+00:00
-- url     : https://prove2.me/theorems/9ade5d57-dbbb-475f-8132-296b0b065772
-- title:
--   Sub-exponentially secure one-way functions
-- statement:
--   There are a polynomial-time computable $f:\{0,1\}^*\to\{0,1\}^*$ and $\rho\in(0,1)$ such that every uniform probabilistic inverter $I$ running in time at most $2^{n^\rho}$ satisfies, for a negligible $\nu$ and every large $n$,
--   $$\Pr_{u\in\{0,1\}^n,\,I}\bigl[f(I(1^n,f(u)))=f(u)\bigr]\le\nu(n).$$
--
--   **Formalization Note** The paper does not define this notion; this is Definition 6.10 without the permutation, which is what the proofs of Theorems 6.9 and 7.11 contradict. The inverter's coins have its time bound as their length.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 1.6, 6.9, 7.11 (no definition in the paper; Definition 6.10 without the permutation, p.38)

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

/-- Sub-exponentially secure one-way functions exist (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorems 1.6, 6.9, 7.11; the
paper gives no definition, so this is Definition 6.10 without the permutation): a polynomial-time
computable `f`, and `ρ ∈ (0,1)`, such that every uniform probabilistic inverter `I` running in time
at most `2^{n^ρ}` on `(1^n, f(u), r)` has, for a negligible `ν` and every large `n`,
`Pr_{u ∈ {0,1}^n, r}[f(I(1^n, f(u))) = f(u)] ≤ ν(n)`.

**Formalization Note** The inverter's coins `r` have its own time bound as their length. -/
def SubexpOWF : Prop :=
  ∃ f : List Bool → List Bool, InFP f ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
    ∀ I : Machine 3, (∀ (n : ℕ) (u r : List Bool), u.length = n → r.length = expBound ρ n →
        HaltsWithin I ![List.replicate n true, f u, r] (expBound ρ n)) →
      ∃ ν : ℕ → ℝ, QuantumPRC.Negligible ν ∧ ∀ᶠ n : ℕ in Filter.atTop,
        prob (n + expBound ρ n) (fun ur =>
          f (output I ![List.replicate n true, f (ur.take n), ur.drop n]) = f (ur.take n)) ≤ ν n

end AvoidPlast.Supplement


