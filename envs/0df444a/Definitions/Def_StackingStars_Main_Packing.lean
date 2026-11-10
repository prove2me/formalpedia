-- Prove2me | Definitions.Def_StackingStars_Main_Packing
-- name    : StackingStars_Main_Packing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:43:00.103233+00:00
-- url     : https://prove2.me/theorems/537254ac-9f6e-44d2-81f0-0276dd19acb0
-- title:
--   Packings by translations and by rigid motions; OPT_trans, OPT_rot and OPT′ as infima of convex-hull areas
-- statement:
--   Objects are a finite family of sets $S_i\subseteq\mathbb R^2$ (the closed regions of the polygons).
--
--   * `IsPacking S`: the placed sets have pairwise disjoint interiors. Touching is allowed.
--   * `optTrans S` $=\mathrm{OPT}_{\mathrm{trans}}(S)$ is the infimum over translation vectors $t_i$ for which the translates $S_i+t_i$ form a packing of $\bigl|\operatorname{conv}\bigcup_i(S_i+t_i)\bigr|$. This is the infimum area of a convex container admitting a translational packing, because the least convex container of a placed family is the convex hull of its union.
--   * `optRot S` $=\mathrm{OPT}_{\mathrm{rot}}(S)$ is the same infimum over rigid poses $T_i$, using the published `PolygonPack.Pose` with `IsRigid`: $z\mapsto(az_1-bz_2+x,\ bz_1+az_2+y)$ with $a^2+b^2=1$. These are proper rotations followed by translations, and no reflection is possible.
--   * `optPrime S` $=\mathrm{OPT}'(S)$ is the infimum total area of one or more convex containers admitting a translational packing. The family is split into parts, each part is translated into its own container, and objects of one part have pairwise disjoint interiors while objects of different parts do not interact. The cost is $\sum_{\text{parts}}|\operatorname{conv}(\text{part})|$.
--
--   $$\mathrm{OPT}_{\mathrm{trans}}(S)=\inf_{t:\ (S_i+t_i)_i\ \text{packing}}\Bigl|\operatorname{conv}\bigcup_i (S_i+t_i)\Bigr| .$$
--
--   **Formalization Note.** Every infimum is a genuine `sInf` of a set of nonnegative reals. The sets are nonempty for bounded objects, because objects translated far apart form a packing, so the infimum is the true infimum and not a junk value. It need not be attained.
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 2 (MACC, translational and rotational variants), p. 11 (OPT, OPT′)

import Mathlib
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_StackingStars_Main_Geometry

namespace StackingStars.Main

/-!
# Packings, the minimum-area convex container, `OPT_trans`, `OPT_rot` and `OPT′`

Abrahamsen et al., *Stacking Stars*, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 2
(PDF 4): "Given a set of n polygons, the goal is to place them without overlap so as to minimize
the area of their convex hull […] In the translational variant, the objects may only be
translated. In the rotational variant, they may be both translated and rotated." p. 11 (PDF 13):
"We write OPT(P) for the infimum area of a convex container admitting a packing of P, and OPT′(P)
for the infimum total area of one or more convex containers admitting a packing of P."

Objects are indexed by a finite type `ι` and given as sets `S i` (the closed regions). Without
overlap means pairwise disjoint interiors (touching allowed). A rotational placement is a
published `PolygonPack.Pose` with `IsRigid` (`a² + b² = 1`): a proper rotation followed by a
translation, no reflection. The least area of a convex container of a placed family is the area
of the convex hull of its union, so `OPT` is the infimum of that hull area over packings.
-/

/-- A family of placed sets is a packing: pairwise disjoint interiors. -/
def IsPacking {ι : Type} (S : ι → Set Pt) : Prop :=
  Pairwise fun i j => Disjoint (interior (S i)) (interior (S j))

/-- `OPT_trans`: the infimum, over translations `t` under which the translates `S i + t i` form a
packing, of the area of the convex hull of their union. -/
noncomputable def optTrans {ι : Type} [Fintype ι] (S : ι → Set Pt) : ℝ :=
  sInf {A | ∃ t : ι → Pt, IsPacking (fun i => translate (t i) (S i)) ∧
    A = hullArea (⋃ i, translate (t i) (S i))}

/-- `OPT_rot`: the infimum, over rigid poses `T` (rotation and translation, no reflection) under
which the images `T i (S i)` form a packing, of the area of the convex hull of their union. -/
noncomputable def optRot {ι : Type} [Fintype ι] (S : ι → Set Pt) : ℝ :=
  sInf {A | ∃ T : ι → PolygonPack.Pose, (∀ i, (T i).IsRigid) ∧
    IsPacking (fun i => (T i).act '' S i) ∧ A = hullArea (⋃ i, (T i).act '' S i)}

/-- `OPT′` (translational): the infimum total area of one or more convex containers admitting a
packing. The objects are split into `k` parts by `part`; each part is translated into its own
container, objects of one part have pairwise disjoint interiors, objects of different parts do
not interact, and the cost is the sum over parts of the hull area of the part. -/
noncomputable def optPrime {ι : Type} [Fintype ι] (S : ι → Set Pt) : ℝ :=
  sInf {A | ∃ (k : ℕ) (part : ι → Fin k) (t : ι → Pt),
    (∀ i j, i ≠ j → part i = part j →
      Disjoint (interior (translate (t i) (S i))) (interior (translate (t j) (S j)))) ∧
    A = ∑ c : Fin k, hullArea (⋃ i ∈ {i | part i = c}, translate (t i) (S i))}

end StackingStars.Main


