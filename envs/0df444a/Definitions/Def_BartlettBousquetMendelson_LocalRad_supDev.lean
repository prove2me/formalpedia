-- Prove2me | Definitions.Def_BartlettBousquetMendelson_LocalRad_supDev
-- name    : BartlettBousquetMendelson_LocalRad_supDev
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:00:12.585714+00:00
-- url     : https://prove2.me/theorems/7ffb008a-a1ff-4354-8203-97032143ecde
-- title:
--   Uniform deviation $\sup_{g\in\mathcal G}(Pg-P_ng)$
-- statement:
--   For a class $\mathcal G$ and a sample, the **uniform deviation** is
--
--   $$
--   V^+=\sup_{g\in\mathcal G}\,(Pg-P_ng),
--   $$
--
--   the largest amount by which a true mean exceeds the corresponding empirical mean.
--
--   **Formalization Note** Lean's real supremum: the paper's for nonempty classes on which the deviations are bounded above, $0$ otherwise. The reversed deviation is `supDevNeg`.
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), §2, p. 7; §3.2, p. 14 (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_empMean

open MeasureTheory

namespace BartlettBousquetMendelson.LocalRad

/-- **Uniform deviation `sup_{g∈G} (Pg − Pₙg)`.**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), §2, p. 7 ("quantities of the form sup_{f∈F}(Pf − Pnf)") and §3.2, p. 14
("V+r = sup_{g∈Gr} Pg − Png").

`supDev P n G ω` is the supremum over `g ∈ G` of the true mean `Pg = ∫ g dP` minus the
empirical mean `Pₙg` on the sample `ω`.

**Formalization Note.** Lean's real `⨆`: it is the paper's supremum for nonempty classes on
which the deviations are bounded above (every statement using it has a nonempty class with
ranges in `[a, b]`, or assumes the boundedness), and `0` otherwise. The reversed deviation
`sup_g (Pₙg − Pg)` is `supDevNeg`. -/
noncomputable def supDev {X : Type*} [MeasurableSpace X] (P : Measure X) (n : ℕ)
    (G : Set (X → ℝ)) (ω : Fin n → X) : ℝ :=
  ⨆ g : G, (∫ y, g.1 y ∂P - empMean n g.1 ω)

end BartlettBousquetMendelson.LocalRad


