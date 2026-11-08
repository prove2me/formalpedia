-- Prove2me | Definitions.Def_AvoidPlast_IsPCPSystem
-- name    : AvoidPlast_IsPCPSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:50:02.284735+00:00
-- url     : https://prove2.me/theorems/cd825d03-d580-464c-a805-3fe4343e5372
-- title:
--   PCP systems with the parameters of Theorem 4.1
-- statement:
--   A PCP system for $L\in\mathrm{NTIME}[t]$, witnessed by $V_0$, with soundness error $s$:
--
--   1. **Completeness**: from a witness accepted by $V_0$, the honest machine computes in polynomial time a proof of length $\ell(n)$ accepted for every random string;
--   2. **Soundness**: for $x\notin L$ and every proof of length $\ell(n)$, $\Pr_\rho[\text{reject}]\ge 1-s(n)$;
--   3. **Complexity**: the verifier runs in time $\mathrm{poly}(n)$ and space $\mathrm{polylog}(n)$, with $\mathrm{polylog}(n)$ random bits, and reads $\mathrm{polylog}(n)$ positions of the proof, a set of positions that does not depend on the proof;
--   4. **Nice lengths**: the proof and randomness lengths are nice.
--
--   These are the parameters Theorem 5.12 refers to as "parameters match those in Theorem 4.1".
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 4.1, p.17; proof of Theorem 5.12, p.28

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_workSpace
import Definitions.Def_AvoidPlast_queries
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_lg
import Definitions.Def_AvoidPlast_IsNice
import Definitions.Def_AvoidPlast_PCPSystem

namespace AvoidPlast

/-- A PCP system for `L ∈ NTIME[t]`, witnessed by `V₀`, with soundness error `s` and the complexity of
Theorem 4.1 (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.17):

* Completeness and the "moreover": from a witness accepted by `V₀`, the machine `P` computes in
  polynomial time a proof of length `proofLen(n)` that is accepted for every `ρ`.
* Soundness: for `x ∉ L` and every proof, the rejection probability is at least `1 - s(n)`.
* Complexity: `V` runs in time `poly(n)` and space `polylog(n)`, and reads `polylog(n)` positions of
  `π`, a set of positions that does not depend on `π`.

**Formalization Note** The randomness length is `polylog(n)`, and the proof and randomness lengths are
*nice*. The statement of Theorem 4.1 does not list them, but Theorem 5.12's proof uses them ("using
`r(n) = polylog(n)` random bits", p.28) to enumerate the random strings and proofs. -/
structure IsPCPSystem (S : PCPSystem) (L : Set (List Bool)) (V₀ : Machine 2) (t : ℕ → ℕ) (C : ℕ)
    (s : ℕ → ℝ) : Prop where
  /-- the proof length and the randomness length are nice -/
  nice : IsNice S.proofLen ∧ IsNice S.randLen
  /-- `P` runs in polynomial time on witnesses of legal length -/
  honest_time : ∃ a : ℕ, ∀ x w : List Bool, w.length ≤ C * (t x.length + 1) →
    HaltsWithin S.P ![x, w] (a * (x.length ^ a + 1))
  /-- perfect completeness, through the honest proof -/
  completeness : ∀ x w : List Bool, w.length ≤ C * (t x.length + 1) → Accepts V₀ ![x, w] →
    (output S.P ![x, w]).length = S.proofLen x.length ∧
      ∀ ρ : List Bool, ρ.length = S.randLen x.length → Accepts S.V ![x, ρ, output S.P ![x, w]]
  /-- soundness -/
  soundness : ∀ x : List Bool, x ∉ L → ∀ π : List Bool, π.length = S.proofLen x.length →
    1 - s x.length ≤ prob (S.randLen x.length) (fun ρ => ¬ Accepts S.V ![x, ρ, π])
  /-- the complexity of the verifier -/
  complexity : ∃ a : ℕ,
    (∀ n : ℕ, (S.randLen n : ℝ) ≤ a * (lg n + 1) ^ a) ∧
    ∀ x ρ π : List Bool, ρ.length = S.randLen x.length → π.length = S.proofLen x.length →
      HaltsWithin S.V ![x, ρ, π] (a * (x.length ^ a + 1)) ∧
      (workSpace S.V ![x, ρ, π] : ℝ) ≤ a * (lg x.length + 1) ^ a ∧
      ((queries S.V ![x, ρ, π] 2).card : ℝ) ≤ a * (lg x.length + 1) ^ a
  /-- the positions read in the proof do not depend on the proof -/
  nonadaptive : ∀ x ρ π π' : List Bool, ρ.length = S.randLen x.length →
    π.length = S.proofLen x.length → π'.length = S.proofLen x.length →
    queries S.V ![x, ρ, π] 2 = queries S.V ![x, ρ, π'] 2

end AvoidPlast


