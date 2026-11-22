-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:04:22.811207+00:00
-- url     : https://prove2.me/theorems/62dfbeff-328a-48d3-99f1-108a733e6631
-- title:
--   Chart Directions Integral
-- statement:
--   Definitions and structural lemmas for Chart Directions Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ChartDirectionsIntegral.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
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
namespace Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
attribute [local instance] Over.cartesianMonoidalCategory
def IsIntPS (T : CDVR) {n d : ℕ} (f : Germ.PS T.Fr n d) : Prop :=
  ∀ m, MvPowerSeries.coeff m f ∈ (algebraMap T.V T.Fr).range
instance (T : CDVR) : Algebra ℚ T.Fr := DivisionRing.toRatAlgebra
section Jet
variable {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (κ : Type) (m : ℕ)
theorem mem_orig_pow_map {a : MvPolynomial κ R} (ha : a ∈ orig R κ ^ (m + 1)) :
    MvPolynomial.map f a ∈ orig R' κ ^ (m + 1) := by
  have h : MvPolynomial.map f a ∈ Ideal.map (MvPolynomial.map f : MvPolynomial κ R →+* MvPolynomial κ R')
      (orig R κ ^ (m + 1)) := Ideal.mem_map_of_mem _ ha
  rw [map_orig_pow] at h
  simpa [MvPolynomial.map_X, orig] using h
def jetCoef : Jet R κ m →+* Jet R' κ m :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk (orig R' κ ^ (m + 1))).comp (MvPolynomial.map f)) fun _ ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (mem_orig_pow_map f κ m ha)
end Jet
section Flat
variable {X X' Y : Scheme.{0}} (L : LB X) (F : X' ⟶ X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ)
lemma wchart_pull_le (j : K → PUnit.{1} → L.ι) :
    LB.wchart (L.pull F) φ j ≤ LB.wchart L (fun k => φ k ≫ F) (fun k => j k ⟨⟩) := by
  intro y hy
  show y ∈ (⋂ k, (φ k ≫ F).base ⁻¹' (L.U (j k ⟨⟩) : Set _))
  refine Set.mem_iInter.2 fun k => ?_
  have h1 : (φ k).base y ∈ LB.wchart L (fun _ : PUnit.{1} => F) (j k) := Set.mem_iInter.1 hy k
  have h2 : F.base ((φ k).base y) ∈ L.U (j k ⟨⟩) := Set.mem_iInter.1 h1 ⟨⟩
  exact h2
def flatGen (c : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)) : LB.Gen (LB.LinComb (L.pull F) φ ε) where
  s := fun j => res (wchart_pull_le L F φ j) (c.s (fun k => j k ⟨⟩))
end Flat
section Data
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
structure IntData (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) where
  G : SAB H (Sp T.V)
  t' : SAB H (Sp T.Fr)
  m1 : letI := io.toAlgebra; SABMap t' Xo.univ.t y.x
  m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))
  ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G)
  tan : ∀ τ i, IsTan (ub τ i)
  eig : ∀ τ i, IsEigV c io G τ (ub τ i)
  basis : ∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w →
    ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w
  lift : letI := io.toAlgebra; ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t'.G.left, u' ≫ m1.φ = y.u τ i ∧
    u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left
  θ : LB.Sec G.PP.L
  θgen : ∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i,
    σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i
  w1 : letI := io.toAlgebra; LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)
  w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ)
  σ : LB.Sec t'.PP.L
  s1 : letI := io.toAlgebra; LB.Sec (Xo.univ.t.PP.L.pull m1.φ)
  θ2 : LB.Sec (G.PP.L.pull m2.φ)
  rig1 : letI := io.toAlgebra; RigIso m1 w1
  rig2 : RigIso m2 w2
  maps1 : letI := io.toAlgebra; IsoMaps w1 σ s1
  maps2 : IsoMaps w2 σ θ2
  pull : PullSec m2.φ θ θ2
  gen1 : letI := io.toAlgebra; ∀ g : t'.G.left ⟶ Gx y.x, g ≫ (CartesianMonoidalCategory.snd (Over.mk y.x) Xo.univ.t.G).left = m1.φ →
    g ≫ (CartesianMonoidalCategory.fst (Over.mk y.x) Xo.univ.t.G).left = t'.G.hom →
    ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx y.x).U (fun _ => j PUnit.unit)),
      s1.f j = (g.appLE _ _ h).hom (y.s.f (fun _ => j PUnit.unit))
def IntegralIffSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr),
    Integral T io y ↔ Nonempty (IntData Xo c T io y)
end Data
section Comparison₂
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}
def primφ (t : SAB H X0) : Fin 1 ⊕ ULift (Finset (Fin 2)) → (t.G.left ⟶ t.G.left) :=
  Sum.elim (fun _ : Fin 1 => 𝟙 t.G.left) (cφG t ![𝟙 t.G, t.act.act H.w0])
def primε : Fin 1 ⊕ ULift (Finset (Fin 2)) → ℤ := Sum.elim (fun _ => 1) fun I => -cε 2 I
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
abbrev chD {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (ch : letI := io.toAlgebra; ChartAt Xo c y.1) : ℕ :=
  letI := io.toAlgebra; ch.d
def IsGenFibreChart {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
    (ch : letI := io.toAlgebra; ChartAt Xo c y.1) (I : IntData Xo c T io y.1)
    (FT : Fin (chD ch) → PS T.V 2 (chD ch)) (actT : 𝓞 E → Fin (chD ch) → PS T.V 1 (chD ch)) (ph1T ph2T : PS T.V 3 (chD ch))
    (syT : PS T.V 2 (chD ch)) (adT : 𝓞 E → PS T.V 2 (chD ch)) (uvecT : Lt1 Dw → Fin (chD ch) → T.V)
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) (chD ch) m 1 ⟶ I.G.G) (eT : ∀ m, FrTyG I.G (𝟙 (Sp T.V)) (chD ch) xT m)
    (wPT : PrimTyG I.G) : Prop :=
  letI := io.toAlgebra
  ((∀ j, ch.B.G.F j = MvPowerSeries.map (algebraMap T.V T.Fr) (FT j)) ∧
    (∀ a j, ch.B.A.act a j = MvPowerSeries.map (algebraMap T.V T.Fr) (actT a j)) ∧
    ch.B.ph1 = MvPowerSeries.map (algebraMap T.V T.Fr) ph1T ∧
    ch.B.ph2 = MvPowerSeries.map (algebraMap T.V T.Fr) ph2T ∧
    ch.B.sy = MvPowerSeries.map (algebraMap T.V T.Fr) syT ∧
    (∀ a, ch.B.ad a = MvPowerSeries.map (algebraMap T.V T.Fr) (adT a)) ∧
    ∀ ℓ i, ch.uvec ℓ i = algebraMap T.V T.Fr (uvecT ℓ i)) ∧
  ∃ x' : ∀ m, jOG (𝟙 (Sp T.Fr)) ch.d m 1 ⟶ I.t'.G,
    (∀ m, (x' m).left ≫ I.m2.φ =
      spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin ch.d) m) ≫ (xT m).left) ∧
    (∀ m, (x' m).left ≫ I.m1.φ = (ch.x m).left) ∧
    (∃ e' : ∀ m, FrTyG I.t' (𝟙 (Sp T.Fr)) ch.d x' m, ∀ m, (e' m).IsGen ∧
      (∃ c₂ : LB.Gen (LB.LinComb I.G.PP.L
          (fun J => cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) ch.d x' m (0 : Fin 2),
            jptG I.t' (𝟙 (Sp T.Fr)) ch.d x' m (1 : Fin 2)] J ≫ I.m2.φ) (cε 2)),
        LB.Gen.Corr I.G.PP.L _ _ _ _ c₂
          (LB.pullGen I.G.PP.L _ _ (eT m) (spMap (jetCoef (algebraMap T.V T.Fr) (Fin 2 × Fin ch.d) m))) ∧
        LB.Gen.Maps (LB.linCombIso I.w2 (cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) ch.d x' m (0 : Fin 2),
            jptG I.t' (𝟙 (Sp T.Fr)) ch.d x' m (1 : Fin 2)]) (cε 2)) (e' m)
          (flatGen I.G.PP.L I.m2.φ _ _ c₂)) ∧
      ∃ c₁ : LB.Gen (LB.LinComb Xo.univ.t.PP.L
          (fun J => cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) ch.d x' m (0 : Fin 2),
            jptG I.t' (𝟙 (Sp T.Fr)) ch.d x' m (1 : Fin 2)] J ≫ I.m1.φ) (cε 2)),
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ c₁ (ch.e m) ∧
        LB.Gen.Maps (LB.linCombIso I.w1 (cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) ch.d x' m (0 : Fin 2),
            jptG I.t' (𝟙 (Sp T.Fr)) ch.d x' m (1 : Fin 2)]) (cε 2)) (e' m)
          (flatGen Xo.univ.t.PP.L I.m1.φ _ _ c₁)) ∧
    ∃ wP' : LB.Gen (LB.LinComb I.t'.PP.L (primφ I.t') primε), wP'.IsGen ∧
      (∃ c₂ : LB.Gen (LB.LinComb I.G.PP.L (fun k => primφ I.t' k ≫ I.m2.φ) primε),
        LB.Gen.Corr I.G.PP.L _ _ _ _ c₂ (LB.pullGen I.G.PP.L _ _ wPT I.m2.φ) ∧
        LB.Gen.Maps (LB.linCombIso I.w2 (primφ I.t') primε) wP' (flatGen I.G.PP.L I.m2.φ _ _ c₂)) ∧
      ∃ c₁ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (fun k => primφ I.t' k ≫ I.m1.φ) primε),
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ c₁ (LB.pullGen Xo.univ.t.PP.L _ _ ch.wP I.m1.φ) ∧
        LB.Gen.Maps (LB.linCombIso I.w1 (primφ I.t') primε) wP' (flatGen Xo.univ.t.PP.L I.m1.φ _ _ c₁)
variable (Xo c)
structure IntegralChartA3 (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) where
  ch : letI := io.toAlgebra; ChartAt Xo c y.1
  I : IntData Xo c T io y.1
  FT : Fin (chD ch) → PS T.V 2 (chD ch)
  actT : 𝓞 E → Fin (chD ch) → PS T.V 1 (chD ch)
  ph1T : PS T.V 3 (chD ch)
  ph2T : PS T.V 3 (chD ch)
  syT : PS T.V 2 (chD ch)
  adT : 𝓞 E → PS T.V 2 (chD ch)
  uvecT : Lt1 Dw → Fin (chD ch) → T.V
  tgT : Fin (chD ch) → (Sp (DualNumber T.V) ⟶ I.G.G.left)
  xT : ∀ m, jOG (𝟙 (Sp T.V)) (chD ch) m 1 ⟶ I.G.G
  eT : ∀ m, FrTyG I.G (𝟙 (Sp T.V)) (chD ch) xT m
  wPT : PrimTyG I.G

  tgBasis : (∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
    ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin (chD ch) → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w
  chartT : IsChartG I.G (𝟙 (Sp T.V)) (chD ch) FT actT tgT (fun j : Fin (chD ch) => Pi.single j (1 : T.V)) xT
  dirT : ∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
    (fun j : Fin (chD ch) => (homAt (𝟙 (Sp T.V))
      (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin (chD ch)) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left)
    (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left
  frameT : IsFrameG I.G (𝟙 (Sp T.V)) (chD ch) xT FT actT ph1T ph2T syT adT eT
  primT : IsPrimG I.G wPT
  gen : IsGenFibreChart ch I FT actT ph1T ph2T syT adT uvecT xT eT wPT
def ChartDirectionsIntegral : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (ℓ : Lt1 Dw) (i : Fin (chD C.ch)),
    (letI := io.toAlgebra; C.ch.uvec ℓ i) ∈ (algebraMap T.V T.Fr).range
def ChartSaturated : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (τ : E →+* ℂ),
    (∃ (w : Fin (chD C.ch) → Fin (chD C.ch) → T.V) (emb : Fin (Dw.mult τ) ↪ Fin (chD C.ch)),
      (∀ i, w (emb i) = C.uvecT ⟨τ, i⟩) ∧
      ∀ v : Fin (chD C.ch) → T.V, ∃! a : Fin (chD C.ch) → T.V, ∀ j, ∑ k, a k * w k j = v j) ∧
    ∀ (v : Fin (chD C.ch) → T.V) (a : T.V), a ≠ 0 →
      a • v ∈ Submodule.span T.V (Set.range fun i : Fin (Dw.mult τ) => C.uvecT ⟨τ, i⟩) →
      v ∈ Submodule.span T.V (Set.range fun i : Fin (Dw.mult τ) => C.uvecT ⟨τ, i⟩)
def IntegralChartExists : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Nonempty (IntegralChartA3 Xo c T io y)
end Comparison₂
end Formalism.L2.Pj


