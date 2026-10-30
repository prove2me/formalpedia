-- Prove2me | Definitions.Def_BartlettBousquetMendelson_LocalRad_supDevNeg
-- name    : BartlettBousquetMendelson_LocalRad_supDevNeg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:00:51.060312+00:00
-- url     : https://prove2.me/theorems/59f7443f-ee4a-4285-8164-c4886daa63e1
-- title:
--   Reversed uniform deviation $\sup_{g\in\mathcal G}(P_ng-Pg)$
-- statement:
--   For a class $\mathcal G$ and a sample,
--
--   $$
--   V^-=\sup_{g\in\mathcal G}\,(P_ng-Pg),
--   $$
--
--   the largest amount by which an empirical mean exceeds the corresponding true mean.
--
--   **Formalization Note** Same conventions as `supDev`.
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), Theorem 2.1, p. 8; §3.2, p. 14 (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_empMean

open MeasureTheory

namespace BartlettBousquetMendelson.LocalRad

/-- **Reversed uniform deviation `sup_{g∈G} (Pₙg − Pg)`.**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), Theorem 2.1, p. 8 ("the same results hold for the quantity sup_{f∈F}(Pnf − Pf)") and §3.2,
p. 14 ("V−r = sup_{g∈Gr} Png − Pg").

`supDevNeg P n G ω` is the supremum over `g ∈ G` of the empirical mean `Pₙg` on the sample
`ω` minus the true mean `Pg = ∫ g dP`.

**Formalization Note.** Same conventions as `supDev` (real `⨆`, `0` on an empty or unbounded
family). -/
noncomputable def supDevNeg {X : Type*} [MeasurableSpace X] (P : Measure X) (n : ℕ)
    (G : Set (X → ℝ)) (ω : Fin n → X) : ℝ :=
  ⨆ g : G, (empMean n g.1 ω - ∫ y, g.1 y ∂P)

end BartlettBousquetMendelson.LocalRad


