-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:58.899988+00:00
-- url     : https://prove2.me/theorems/bade3fe4-493f-495f-a30c-069e88ff9b9b
-- title:
--   Th Germ
-- statement:
--   Definitions and structural lemmas for Th Germ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ThGerm.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsThRule
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open MvPolynomial (X C)
attribute [local instance] Over.cartesianMonoidalCategory
section At
variable {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
abbrev overAt (A : Type) [CommRing A] [Algebra S A] : Over X := Over.mk (spMap (algebraMap S A) ≫ x0)
theorem spMap_comp_alg {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B]
    (f : A →ₐ[S] B) : spMap (f : A →+* B) ≫ spMap (algebraMap S A) = spMap (algebraMap S B) := by
  first
    | rw [← spMap_comp, AlgHom.comp_algebraMap]
    | (unfold spMap; rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])
def homAt {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] (f : A →ₐ[S] B) :
    overAt x0 B ⟶ overAt x0 A :=
  Over.homMk (spMap (f : A →+* B)) (by
    dsimp
    rw [← Category.assoc, spMap_comp_alg])
end At
section Chart
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
abbrev jO (m n : ℕ) : Over Xo.X := overAt y.x (Jet S (Fin n × Fin d) m)
def jetCopy {n : ℕ} (m : ℕ) (i : Fin n) : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m :=
  jetMap (fun p => X (i, p.2)) fun _ => X_mem_orig _
def jetSubstP {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) : Jet S κ m →ₐ[S] Jet S κ' m :=
  jetMap (fun i => φ i - C (MvPolynomial.constantCoeff (φ i))) fun _ => sub_const_mem_orig _
def psIn {n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (f : MvPowerSeries (Fin n × Fin d) S) :
    MvPolynomial (Fin n' × Fin d) S :=
  MvPolynomial.rename (fun p => (r p.1, p.2)) (psTrunc m f)
def jpt (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) {n : ℕ} (m : ℕ) (i : Fin n) : jO y d m n ⟶ Xo.univ.t.G :=
  homAt y.x (jetCopy d m i) ≫ x m
structure IsChart (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (uvec : Lt1 Dw → Fin d → S)
    (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G) : Prop where
  zero : ∀ m, homAt y.x (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1
  trunc : ∀ m, homAt y.x (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) ≫ x (m + 1) = x m
  law : ∀ m, homAt y.x (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m =
    jpt y d x m (0 : Fin 2) * jpt y d x m (1 : Fin 2)
  act : ∀ m (a : 𝓞 E), x m ≫ Xo.univ.t.act.act a =
    homAt y.x (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act a p.2)) ≫ x m
  tan : ∀ ℓ : Lt1 Dw, IsCombAt y.x
    (fun j : Fin d => (homAt y.x (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left) (uvec ℓ)
    (y.u ℓ.1 ℓ.2)

  basis : ∀ v : Fin d → S, ∃! a : Lt1 Dw → S, ∀ j, ∑ ℓ, a ℓ * uvec ℓ j = v j
end Chart
section Frame
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
def cφ {T : Over Xo.X} {n : ℕ} (xs : Fin n → (T ⟶ Xo.univ.t.G)) :
    ULift (Finset (Fin n)) → (T.left ⟶ Xo.univ.t.G.left) :=
  fun I => (psum Xo.univ.t.G xs I.down).left
def cε (n : ℕ) : ULift (Finset (Fin n)) → ℤ := fun I => (-1) ^ (n - I.down.card)
def scaleGen {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) :
    LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε) :=
  ⟨fun j => res le_top u * g.s j⟩
def genPow {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (k : ℕ) :
    LB.Gen (LB.LinComb Xo.univ.t.PP.L φ fun i => (k : ℤ) * ε i) :=
  ⟨fun j => g.s j ^ k⟩
def unitΓ {A : Type} [CommRing A] (u : Aˣ) : Γ(Sp A, ⊤)ˣ := Units.map (toΓ A).toMonoidHom u
variable {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
variable (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G)
abbrev FrTy (m : ℕ) : Type :=
  LB.Gen (cubeLB Xo.univ.t.G ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)] Xo.univ.t.PP.L)
def pe (e : ∀ m, FrTy y d x m) (m : ℕ) {n' : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S) :=
  LB.pullGen Xo.univ.t.PP.L (cφ ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)]) (cε 2) (e m)
    (homAt y.x (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left
structure IsFrame (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S) (sy : MvPowerSeries (Fin 2 × Fin d) S)
    (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S) (e : ∀ m, FrTy y d x m) : Prop where
  gen : ∀ m, (e m).IsGen
  ph1 : ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
        (lift (jpt y d x m (0 : Fin 3)) (lift (jpt y d x m (1 : Fin 3)) (jpt y d x m (2 : Fin 3)))).left)
      (scaleGen _ _ (unitΓ u) (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (pe y d x e m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)])
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.invGen Xo.univ.t.PP.L _ _ (pe y d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))
          (LB.invGen Xo.univ.t.PP.L _ _ (pe y d x e m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))
  ph2 : ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
        (lift (jpt y d x m (1 : Fin 3)) (lift (jpt y d x m (2 : Fin 3)) (jpt y d x m (0 : Fin 3)))).left)
      (scaleGen _ _ (unitΓ u) (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (pe y d x e m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.invGen Xo.univ.t.PP.L _ _ (pe y d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)]))
          (LB.invGen Xo.univ.t.PP.L _ _ (pe y d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))
  sy : ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e m)
      (scaleGen _ _ (unitΓ u⁻¹) (pe y d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))
  ad : ∀ a : 𝓞 E, ∃ wL : LB.Gen (LB.LinComb Xo.univ.t.PP.L
      (Sum.elim (cφ ![fst Xo.univ.t.G Xo.univ.t.G, snd Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act (H.bar a)])
        (cφ ![fst Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act a, snd Xo.univ.t.G Xo.univ.t.G]))
      (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧
    ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (jpt y d x m (0 : Fin 2)) (jpt y d x m (1 : Fin 2))).left)
          (pe y d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)]))
        (scaleGen _ _ (unitΓ u)
          (pe y d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))
end Frame
section Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
variable (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G)
def jBase (m n : ℕ) : jO y d m n ⟶ ptO Xo y.x :=
  Over.homMk (spMap (algebraMap S (Jet S (Fin n × Fin d) m))) rfl
abbrev PrimTy (H : Host E) (Xo : Moduli Dw l) : Type :=
  LB.Gen (LB.LinComb Xo.univ.t.PP.L
    (Sum.elim (fun _ : Fin 1 => 𝟙 Xo.univ.t.G.left) (cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0]))
    (Sum.elim (fun _ => 1) fun I => -cε 2 I))
def IsPrim (wP : PrimTy H Xo) : Prop :=
  wP.IsGen ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ wP (eSec Xo.univ.t.G)) Xo.univ.t.PP.rig
def eL (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, FrTy y d x m) (wP : PrimTy H Xo)
    (m : ℕ) :=
  LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ wP (x m).left)
    (pe y d x e m ![fun j => X ((0 : Fin 1), j), fun j => psIn d m ![0] (act H.w0 j)])
def IsGerm (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (e : ∀ m, FrTy y d x m)
    (wP : PrimTy H Xo) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : MvPowerSeries (Fin 1 × Fin d) S) :
    Prop :=
  ∀ m, ∃ (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (jO y d m 1)))
    (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (x m).left) fun _ => (k : ℤ))),
    IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (jBase y d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (genPow _ _ (eL y d x act e wP m) k) ∧
    IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (x m) τ (toΓ _ (psJet m f))
end Germ
section Pin
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
structure ChartAt [StarRing (𝓞 E)] {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) where
  d : ℕ
  B : Germ.FB S d (𝓞 E)
  uvec : Lt1 Dw → Fin d → S
  x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G
  e : ∀ m, FrTy y d x m
  wP : PrimTy H Xo
  h : Germ.PS S 2 d
  chart : IsChart y d B.G.F B.A.act uvec x
  frame : IsFrame y d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e
  prim : IsPrim wP
  gauge : B.IsCanonGauge S h

  rig0 : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ (eL y d x B.A.act e wP 0)
      (homAt y.x (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left)
    (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1)
def IsNab [StarRing (𝓞 E)] (nab : NabV Xo c) : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) ∧
  ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S),
    ∃ C : ChartAt Xo c y,
      (∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))),
        ∃ f, IsGerm y C.d C.x C.B.A.act C.e C.wP k F f) ∧
      ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
        (f : MvPowerSeries (Fin 1 × Fin C.d) S),
        IsGerm y C.d C.x C.B.A.act C.e C.wP k F f →
          ∀ α : Lt1 Dw →₀ ℕ, nab y k F α = C.B.nabVal S C.h H.w0 k f C.uvec (MvPolynomial.monomial α 1)
end Pin
end Formalism.L2.Pj


