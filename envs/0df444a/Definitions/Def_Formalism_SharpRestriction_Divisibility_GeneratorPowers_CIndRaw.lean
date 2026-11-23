-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndRaw
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndRaw
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:26:26.285315+00:00
-- url     : https://prove2.me/theorems/ecfca40c-328d-4051-a2d1-44c4e07aa06a
-- title:
--   CInd Raw
-- statement:
--   Definitions and structural lemmas for CInd Raw, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndRaw.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPolynomial (X C)
attribute [local instance] Over.cartesianMonoidalCategory
section Chart
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S] [Algebra c.F S] (x0 : Sp S ⟶ Xo.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (d : ℕ)
abbrev rjO (m n : ℕ) : Over Xo.X := overAt x0 (Jet S (Fin n × Fin d) m)
def rjpt (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) {n : ℕ} (m : ℕ) (i : Fin n) : rjO x0 d m n ⟶ Xo.univ.t.G :=
  homAt x0 (jetCopy d m i) ≫ x m
structure RIsChart (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (uvec : Lt1 Dw → Fin d → S)
    (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) : Prop where
  zero : ∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1
  trunc : ∀ m, homAt x0 (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) ≫ x (m + 1) = x m
  law : ∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m =
    rjpt x0 d x m (0 : Fin 2) * rjpt x0 d x m (1 : Fin 2)
  act : ∀ m (a : 𝓞 E), x m ≫ Xo.univ.t.act.act a =
    homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act a p.2)) ≫ x m
  tan : ∀ ℓ : Lt1 Dw, IsCombAt x0
    (fun j : Fin d => (homAt x0 (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left) (uvec ℓ)
    (u ℓ.1 ℓ.2)

  basis : ∀ v : Fin d → S, ∃! a : Lt1 Dw → S, ∀ j, ∑ ℓ, a ℓ * uvec ℓ j = v j
end Chart
section Frame
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S] [Algebra c.F S] (x0 : Sp S ⟶ Xo.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (d : ℕ)
variable (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G)
abbrev RFrTy (m : ℕ) : Type :=
  LB.Gen (cubeLB Xo.univ.t.G ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)] Xo.univ.t.PP.L)
def rpe (e : ∀ m, RFrTy x0 d x m) (m : ℕ) {n' : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S) :=
  LB.pullGen Xo.univ.t.PP.L (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m)
    (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left
structure RIsFrame (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S) (sy : MvPowerSeries (Fin 2 × Fin d) S)
    (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S) (e : ∀ m, RFrTy x0 d x m) : Prop where
  gen : ∀ m, (e m).IsGen
  ph1 : ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
        (lift (rjpt x0 d x m (0 : Fin 3)) (lift (rjpt x0 d x m (1 : Fin 3)) (rjpt x0 d x m (2 : Fin 3)))).left)
      (scaleGen _ _ (unitΓ u) (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (rpe x0 d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)])
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.invGen Xo.univ.t.PP.L _ _ (rpe x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))
          (LB.invGen Xo.univ.t.PP.L _ _ (rpe x0 d x e m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))
  ph2 : ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
        (lift (rjpt x0 d x m (1 : Fin 3)) (lift (rjpt x0 d x m (2 : Fin 3)) (rjpt x0 d x m (0 : Fin 3)))).left)
      (scaleGen _ _ (unitΓ u) (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (rpe x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.invGen Xo.univ.t.PP.L _ _ (rpe x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)]))
          (LB.invGen Xo.univ.t.PP.L _ _ (rpe x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))
  sy : ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e m)
      (scaleGen _ _ (unitΓ u⁻¹) (rpe x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))
  ad : ∀ a : 𝓞 E, ∃ wL : LB.Gen (LB.LinComb Xo.univ.t.PP.L
      (Sum.elim (cφ ![fst Xo.univ.t.G Xo.univ.t.G, snd Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act (H.bar a)])
        (cφ ![fst Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act a, snd Xo.univ.t.G Xo.univ.t.G]))
      (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧
    ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (rjpt x0 d x m (0 : Fin 2)) (rjpt x0 d x m (1 : Fin 2))).left)
          (rpe x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)]))
        (scaleGen _ _ (unitΓ u)
          (rpe x0 d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))
end Frame
section Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S] [Algebra c.F S] (x0 : Sp S ⟶ Xo.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (d : ℕ)
variable (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G)
def rjBase (m n : ℕ) : rjO x0 d m n ⟶ ptO Xo x0 :=
  Over.homMk (spMap (algebraMap S (Jet S (Fin n × Fin d) m))) rfl
def reL (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, RFrTy x0 d x m) (wP : PrimTy H Xo)
    (m : ℕ) :=
  LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ wP (x m).left)
    (rpe x0 d x e m ![fun j => X ((0 : Fin 1), j), fun j => psIn d m ![0] (act H.w0 j)])
def RIsGerm (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, RFrTy x0 d x m)
    (wP : PrimTy H Xo) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo x0))) (f : MvPowerSeries (Fin 1 × Fin d) S) :
    Prop :=
  ∀ m, ∃ (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (rjO x0 d m 1)))
    (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (x m).left) fun _ => (k : ℤ))),
    IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (rjBase x0 d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (genPow _ _ (reL x0 d x act e wP m) k) ∧
    IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (x m) τ (toΓ _ (psJet m f))
end Germ
section Pin
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
structure RChartAt [StarRing (𝓞 E)] {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (x0 : Sp S ⟶ Xo.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) where
  d : ℕ
  B : Germ.FB S d (𝓞 E)
  uvec : Lt1 Dw → Fin d → S
  x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G
  e : ∀ m, RFrTy x0 d x m
  wP : PrimTy H Xo
  h : Germ.PS S 2 d
  chart : RIsChart x0 u d B.G.F B.A.act uvec x
  frame : RIsFrame x0 d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e
  prim : IsPrim wP
  gauge : B.IsCanonGauge S h

  rig0 : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ (reL x0 d x B.A.act e wP 0)
      (homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left)
    (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt x0 S) 1)
end Pin
section ToRaw
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
def ChartAt.toRaw [StarRing (𝓞 E)] {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
    (C : ChartAt Xo c y) : RChartAt Xo c y.x y.u :=
  ⟨C.d, C.B, C.uvec, C.x, C.e, C.wP, C.h,
    ⟨C.chart.zero, C.chart.trunc, C.chart.law, C.chart.act, C.chart.tan, C.chart.basis⟩,
    ⟨C.frame.gen, C.frame.ph1, C.frame.ph2, C.frame.sy, C.frame.ad⟩, C.prim, C.gauge, C.rig0⟩
end ToRaw
end Formalism.MainNotions.ModuliIntegralCharts.H1


