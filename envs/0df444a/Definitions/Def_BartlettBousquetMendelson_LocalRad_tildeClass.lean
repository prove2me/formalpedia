-- Prove2me | Definitions.Def_BartlettBousquetMendelson_LocalRad_tildeClass
-- name    : BartlettBousquetMendelson_LocalRad_tildeClass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:59:39.921782+00:00
-- url     : https://prove2.me/theorems/1af96978-741f-4304-bce6-b5867aa0549d
-- title:
--   Class $\tilde{\mathcal G}_r=\{rf/(T(f)\vee r):f\in\mathcal F\}$
-- statement:
--   For a class $\mathcal F$, a functional $T$ and $r>0$,
--
--   $$
--   \tilde{\mathcal G}_r=\Big\{\frac{rf}{T(f)\vee r}:f\in\mathcal F\Big\},
--   $$
--
--   where $u\vee v=\max(u,v)$. Functions with $T(f)\le r$ are kept, the others are scaled by $r/T(f)$. It is the class to which the proof of Theorem 3.3, part 2 applies Theorem 2.1.
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), §3.2, p. 14 (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib

namespace BartlettBousquetMendelson.LocalRad

/-- **The class `G̃_r = {r f / (T(f) ∨ r) : f ∈ F}`.**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), §3.2, p. 14: "For the second part of the theorem, we need to introduce another class of
functions, G̃r := {rf/(T(f) ∨ r) : f ∈ F}".

`tildeClass F T r` is the image of `F` under `f ↦ (r / max (T f) r) • f`. -/
noncomputable def tildeClass {X : Type*} (F : Set (X → ℝ)) (T : (X → ℝ) → ℝ) (r : ℝ) :
    Set (X → ℝ) :=
  (fun f => (r / max (T f) r) • f) '' F

end BartlettBousquetMendelson.LocalRad


