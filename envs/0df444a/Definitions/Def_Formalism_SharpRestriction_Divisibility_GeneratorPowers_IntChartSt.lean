-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartSt
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:34.46041+00:00
-- url     : https://prove2.me/theorems/0716fcb7-0867-4023-a80c-8983f0f5af7c
-- title:
--   Int Chart St
-- statement:
--   Definitions and structural lemmas for Int Chart St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/IntChartSt.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
def IntChartStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V →
    ∀ (t : SAB H (Sp V)),
    IsProper ((Over.pullback (spMap (algebraMap V (FractionRing V)))).obj t.G).hom →
    ∀ {κ : Type} [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)),
      (∀ ℓ, IsTanAtG t (𝟙 (Sp V)) (tg ℓ)) →
      (∀ w, IsTanAtG t (𝟙 (Sp V)) w →
        ∃! a : κ → V, IsCombAtG t (𝟙 (Sp V)) (m := Fintype.card κ)
          (fun i => tg ((Fintype.equivFin κ).symm i)) (fun i => a ((Fintype.equivFin κ).symm i)) w) →
      ∀ [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
      ∃ (d : ℕ) (B : Germ.FB V d (𝓞 E)) (uvec : κ → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
        (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (wP : PrimTyG t),
        d = Fintype.card κ ∧ (∀ ℓ (j : Fin d), uvec ℓ j = if (j : ℕ) = (Fintype.equivFin κ ℓ : ℕ) then 1 else 0) ∧
        IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uvec x ∧
        IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e ∧
        IsPrimG t wP ∧ FrTrunc t (𝟙 (Sp V)) d x e ∧ Rig0G t (𝟙 (Sp V)) d x B.A.act e wP ∧
        ∀ (k : ℕ) (F : LB.Sec (LPow t.G t.PP.L k (Over.mk (𝟙 (Sp V))))),
          ∃ f, IsGermG t (𝟙 (Sp V)) d x B.A.act e wP k F f
end Formalism.MainNotions.ModuliIntegralCharts.H1


