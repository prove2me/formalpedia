-- Prove2me | Definitions.Def_CompNonlocal_Supplement_puzzSD
-- name    : CompNonlocal_Supplement_puzzSD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:04:00.904699+00:00
-- url     : https://prove2.me/theorems/8e7a99cb-cc4d-460f-af64-69e294e4d788
-- title:
--   The statistical distance of a puzzle adversary, Eq. (9)
-- statement:
--   Let $\mathrm{Samp}$ be a sampler whose classical output is split as $(\mathrm{puzz},\mathrm{ans})$ (the first $l(\kappa)$ bits and the rest), and let $A$ be a circuit that reads $\mathrm{puzz}$ and outputs a string. This is the statistical (total-variation) distance
--   $$\mathrm{SD}\Big(\big(\mathrm{puzz},A(1^\kappa,\mathrm{puzz})\big),\ (\mathrm{puzz},\mathrm{ans})\Big),\qquad (\mathrm{puzz},\mathrm{ans})\leftarrow\mathrm{Samp}(1^\kappa),$$
--   i.e. $\tfrac12\sum_z|P_1(z)-P_2(z)|$ over pairs of strings $z$.
--
--   It is the quantity bounded below in the definition of distributional one-way puzzles (Definition 7, Eq. (9)).
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), Definition 7, p.23, Eq. (9)

import Mathlib
import Definitions.Def_CompNonlocal_Family
import Definitions.Def_CompNonlocal_ICirc_effectOn

set_option autoImplicit false

namespace CompNonlocal.Supplement

open QAlgorithms.Complexity

/-- The statistical distance of a puzzle adversary. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 7, p.23, Eq. (9):
SD((puzz, A(1^κ, puzz))_{(puzz,ans)←Samp(1^κ)}, (puzz, ans)_{(puzz,ans)←Samp(1^κ)}).

`Samp κ` has no input; its classical output `o` is split as `puzz = o.take (l κ)`,
`ans = o.drop (l κ)`. The adversary circuit `A` reads `puzz` classically and its classical output is
its answer. `P₁` is the law of `(puzz, A(puzz))` and `P₂` the law of `(puzz, ans)`, both on pairs of
strings; the value is `½ Σ_z |P₁ z − P₂ z|`, summed over a finite set `S` containing both supports
(the total-variation distance).

**Formalization Note** Probabilities of classical outputs are `Re Tr` of the circuit's
`effectOn` on its empty quantum input. The security parameter `1^κ` is implicit in the circuit
families. -/
noncomputable def puzzSD (Samp : Family) (l : ℕ → ℕ) (κ : ℕ) (A : ICirc) : ℝ :=
  let sp : Bits (Samp κ).outC.length → ℝ := fun o =>
    ((Samp κ).effectOn 0 [] (fun t => decide (t = List.ofFn o))).trace.re
  let ap : Str → Bits A.outC.length → ℝ := fun p a =>
    (A.effectOn 0 p (fun t => decide (t = List.ofFn a))).trace.re
  let P₁ : Str × Str → ℝ := fun z =>
    ∑ o, ∑ a, if ((List.ofFn o).take (l κ), List.ofFn a) = z then
      sp o * ap ((List.ofFn o).take (l κ)) a else 0
  let P₂ : Str × Str → ℝ := fun z =>
    ∑ o, if ((List.ofFn o).take (l κ), (List.ofFn o).drop (l κ)) = z then sp o else 0
  let S : Finset (Str × Str) :=
    (Finset.univ.image fun oa : Bits (Samp κ).outC.length × Bits A.outC.length =>
        ((List.ofFn oa.1).take (l κ), List.ofFn oa.2)) ∪
      Finset.univ.image fun o : Bits (Samp κ).outC.length =>
        ((List.ofFn o).take (l κ), (List.ofFn o).drop (l κ))
  (1 / 2) * ∑ z ∈ S, |P₁ z - P₂ z|

end CompNonlocal.Supplement


