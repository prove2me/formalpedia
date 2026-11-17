-- Prove2me | Definitions.Def_CompNonlocal_Supplement_IsOWPuzz
-- name    : CompNonlocal_Supplement_IsOWPuzz
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:05:20.843588+00:00
-- url     : https://prove2.me/theorems/023a6e21-53a3-471e-9d7e-163dfb36e2bb
-- title:
--   One-way puzzles [KT24]
-- statement:
--   A **one-way puzzle** (Khurana–Tomer) is a pair $(\mathrm{Samp},\mathrm{Ver})$ where
--
--   1. $\mathrm{Samp}(1^\kappa)\to(\mathrm{puzz},\mathrm{ans})$ is a uniform quantum polynomial-time sampler of classical strings;
--   2. $\mathrm{Ver}(\mathrm{puzz},\mathrm{ans})\in\{0,1\}$ is an arbitrary function, not necessarily efficient;
--   3. **correctness:** $\Pr[\mathrm{Ver}(\mathrm{puzz},\mathrm{ans})=1]\ge1-\mathrm{negl}(\kappa)$;
--   4. **security:** for every polynomial-size quantum adversary $A$ with classical advice, $\Pr[\mathrm{Ver}(\mathrm{puzz},A(1^\kappa,\mathrm{puzz}))=1]\le\mathrm{negl}(\kappa)$.
--
--   The paper cites this definition ([KT24]; [CGG24, Definition 17]) for the conclusion of Theorem 9.
--
--   **Formalization Note** The puzzle is the first $l(\kappa)$ bits of the sampler's output; $\mathrm{Ver}$ does not depend on $\kappa$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), p.6 (citing [KT24]) and p.68 (citing [CGG24, Definition 17])

import Mathlib
import Definitions.Def_CompNonlocal_Uniform
import Definitions.Def_CompNonlocal_PolySize
import Definitions.Def_CompNonlocal_Negligible
import Definitions.Def_CompNonlocal_ICirc_effectOn

set_option autoImplicit false

namespace CompNonlocal.Supplement

open QAlgorithms.Complexity

/-- (Ordinary) one-way puzzles, as cited by Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), p.6 ("We obtain OWPuzz [KT24] … OWPuzz have an
efficient quantum sampler producing a classical puzzle and answer, but no efficient quantum
algorithm can find a valid answer from the puzzle with non-negligible probability; verification
need not be efficient") and p.68 ("[CGG24, Definition 17 and Theorem 33]"). The paper does not
restate the definition; this is the standard one of Khurana–Tomer [KT24]:

1. `Samp(1^κ) → (puzz, ans)` is uniform QPT with classical outputs (here the classical output `o`
   of `Samp κ`, split as `puzz = o.take (l κ)`, `ans = o.drop (l κ)`);
2. `Ver(puzz, ans) ∈ {0, 1}` is an arbitrary, not necessarily efficient, function;
3. correctness: `Pr[Ver(puzz, ans) = 1] ≥ 1 − negl(κ)`;
4. security: for every polynomial-size quantum adversary `A` with classical advice,
   `Pr[Ver(puzz, A(1^κ, puzz)) = 1] ≤ negl(κ)`.

**Formalization Note** `Ver` does not depend on `κ` (as in [KT24]). The adversary reads `puzz`
classically and its classical output is its answer. In 4 the negligible bound is chosen after the
adversary. -/
def IsOWPuzz (Samp : Family) (l : ℕ → ℕ) (Ver : Str → Str → Bool) : Prop :=
  Uniform Samp ∧
    (∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ κ : ℕ,
      1 - μ κ ≤ ∑ o : Bits (Samp κ).outC.length,
        ((Samp κ).effectOn 0 [] (fun t => decide (t = List.ofFn o))).trace.re *
          (if Ver ((List.ofFn o).take (l κ)) ((List.ofFn o).drop (l κ)) then 1 else 0)) ∧
    (∀ A : Family, PolySize A → ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ κ : ℕ,
      (∑ o : Bits (Samp κ).outC.length, ∑ a : Bits (A κ).outC.length,
        ((Samp κ).effectOn 0 [] (fun t => decide (t = List.ofFn o))).trace.re *
          ((A κ).effectOn 0 ((List.ofFn o).take (l κ)) (fun t => decide (t = List.ofFn a))).trace.re *
          (if Ver ((List.ofFn o).take (l κ)) (List.ofFn a) then 1 else 0)) ≤ μ κ)

end CompNonlocal.Supplement


