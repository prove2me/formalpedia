-- Prove2me | Definitions.Def_BartlettBousquetMendelson_LocalRad_weightedClass
-- name    : BartlettBousquetMendelson_LocalRad_weightedClass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:59:27.42998+00:00
-- url     : https://prove2.me/theorems/60aab2a4-922e-4360-b7a0-f7a302240468
-- title:
--   Weighted class $\mathcal G_r=\{(r/w(f))f:f\in\mathcal F\}$
-- statement:
--   For a class $\mathcal F$, a functional $T$, $\lambda>1$ and $r>0$, the **weighted class** is
--
--   $$
--   \mathcal G_r=\Big\{\frac r{w(f)}\,f:f\in\mathcal F\Big\},
--   $$
--
--   with $w$ the weight. It rescales every function of large $T$-value down to $T$-value about $r$; Lemma 3.8 transfers deviation bounds on $\mathcal G_r$ back to $\mathcal F$.
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), §3.2, p. 14 (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_weight

namespace BartlettBousquetMendelson.LocalRad

/-- **The weighted class `G_r = {(r / w(f)) f : f ∈ F}`.**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), §3.2, p. 14: "Given a class F, λ > 1 and r > 0, let w(f) = min{rλ^k : k ∈ N, rλ^k ≥ T(f)}
and set Gr = {(r/w(f)) f : f ∈ F}."

`weightedClass F T r lam` is the image of `F` under `f ↦ (r / w(f)) • f`, with `w = weight`. -/
noncomputable def weightedClass {X : Type*} (F : Set (X → ℝ)) (T : (X → ℝ) → ℝ) (r lam : ℝ) :
    Set (X → ℝ) :=
  (fun f => (r / weight T r lam f) • f) '' F

end BartlettBousquetMendelson.LocalRad


