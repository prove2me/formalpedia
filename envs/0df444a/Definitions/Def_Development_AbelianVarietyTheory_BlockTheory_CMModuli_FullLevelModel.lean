-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FullLevelModel
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_FullLevelModel
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:01:28.132244+00:00
-- url     : https://prove2.me/theorems/fcf0ac55-ffdd-4f98-9c1a-fab01ef1e1d1
-- title:
--   Full Level Model
-- statement:
--   Definitions and structural lemmas for Full Level Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/FullLevelModel.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FullLevelModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
structure PModel (H : Host E) (O : Type) [CommRing O] where
  X : Scheme.{0}
  s : X ⟶ Sp O
  normal : IsNormalScheme X
  proj : IsProjOver s
  flat : Flat s
  t : SAB H X
structure ModelOf {F : Type} [Field F] {U : Scheme.{0}} (sU : U ⟶ Sp F) (tU : SAB H U) {O : Type} [CommRing O]
    (β : O →+* F) extends PModel H O where
  jQ : U ⟶ pullback s (spMap β)
  jQ_over : jQ ≫ pullback.snd _ _ = sU
  jQ_open : IsOpenImmersion jQ
  jQ_dense : Dense (Set.range jQ)
  m : SABMap tU t (jQ ≫ pullback.fst _ _)
  ab_gen : pullback.fst s (spMap β) ⁻¹' abLocus t.G = Set.range jQ
def ModelOf.j {F : Type} [Field F] {U : Scheme.{0}} {sU : U ⟶ Sp F} {tU : SAB H U} {O : Type} [CommRing O]
    {β : O →+* F} (Y : ModelOf sU tU β) : U ⟶ Y.X := Y.jQ ≫ pullback.fst _ _
def ofModel {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) : ModelOf (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) Y.oF.t β where
  X := Y.X
  s := Y.s
  normal := Y.normal
  proj := Y.proj
  flat := Y.flat
  t := Y.t
  jQ := Y.jQ
  jQ_over := Y.jQ_over
  jQ_open := Y.jQ_open
  jQ_dense := Y.jQ_dense
  m := Y.m
  ab_gen := Y.ab_gen
structure FinMap {O O' : Type} [CommRing O] [CommRing O'] (Y' : PModel H O') (Y : PModel H O) (b : O →+* O') where
  π : Y'.X ⟶ Y.X
  overB : π ≫ Y.s = Y'.s ≫ spMap b
  fin : IsFinite (pullback.lift π Y'.s overB : Y'.X ⟶ pullback Y.s (spMap b))
  mu : SABMap Y'.t Y.t π
def ModelOf.ExtendsAut {F : Type} [Field F] {U : Scheme.{0}} {sU : U ⟶ Sp F} {tU : SAB H U} {O : Type} [CommRing O]
    {β : O →+* F} (Y : ModelOf sU tU β) (r : U ≅ U) (ν : SABMap tU tU r.hom) (σ : O ≃+* O) : Prop :=
  ∃ (ρ : Y.X ≅ Y.X) (mu : SABMap Y.t Y.t ρ.hom),
    ρ.hom ≫ Y.s = Y.s ≫ spMap σ.toRingHom ∧ Y.j ≫ ρ.hom = r.hom ≫ Y.j ∧ Y.m.φ ≫ mu.φ = ν.φ ≫ Y.m.φ
def PModel.SplitFibres {O : Type} [CommRing O] (Y : PModel H O) : Prop :=
  ∀ x : Y.X, ∃ S : SplitExt (Sp (Y.X.residueField x)),
    S.IsGt ((Over.pullback (Y.X.fromSpecResidueField x)).obj Y.t.G)
def PModel.Uniformised {O : Type} [CommRing O] (Y : PModel H O) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R →
    IsAdicComplete (IsLocalRing.maximalIdeal R) R →
    ∀ (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), (ξ ⁻¹' abLocus Y.t.G).Nonempty →
      (∃ S : SplitExt (Sp (IsLocalRing.ResidueField R)),
        S.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj t.G)) →
      UniformisationConclusion t (ξ ⁻¹' abLocus Y.t.G)
def PushFree {X : Scheme.{0}} (G : Over X) (L : LB G.left) (r : ℕ) : Prop :=
  ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ θ : Fin r → ∀ i, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.U i),
    (∀ j, θ j ∈ secOn L (G.hom ⁻¹ᵁ V)) ∧
    (∀ (W : X.Opens) (hW : W ≤ V), ∀ s ∈ secOn L (G.hom ⁻¹ᵁ W), ∃! a : Fin r → Γ(X, W), ∀ i,
      s i = ∑ j, (G.hom.appLE W (G.hom ⁻¹ᵁ W ⊓ L.U i) inf_le_left).hom (a j) *
        resG G.left (inf_le_inf_right _ (G.hom.preimage_mono hW)) (θ j i)) ∧
    ∀ (W : X.Opens) (hW : W ≤ V) (a : Fin r → Γ(X, W)) (y : X), (∃ j, y ∈ X.basicOpen (a j)) →
      ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen
        (∑ j, (G.hom.appLE W (G.hom ⁻¹ᵁ W ⊓ L.U i) inf_le_left).hom (a j) *
          resG G.left (inf_le_inf_right _ (G.hom.preimage_mono hW)) (θ j i))
def lbPow {X : Scheme.{0}} (L : LB X) (k : ℕ) : LB X :=
  LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (k : ℤ))
structure AuxiliaryInertOddPrime (H : Host E) (n : ℕ) : Prop where
  prime : n.Prime
  odd : Odd n
  inert : ¬ IsSquare (-(H.d : ZMod n))
  unram : ¬ (n : ℤ) ∣ NumberField.discr E
def w0C (H : Host E) : ℂ := (1 + H.rt0) / 2
def oRing (H : Host E) (N c : ℕ) : Subring ℂ := Subring.closure {w0C H, zeta N, (c : ℂ)⁻¹}
def oLoc (H : Host E) (p N : ℕ) : Subring ℂ :=
  Subring.closure ({w0C H} ∪ ({zeta N} ∪ {x | ∃ k : ℕ, k.Coprime p ∧ x = (k : ℂ)⁻¹}))
def oW (H : Host E) (N c : ℕ) : oRing H N c := ⟨w0C H, Subring.subset_closure (by simp)⟩
def oZeta (H : Host E) (N c : ℕ) : oRing H N c := ⟨zeta N, Subring.subset_closure (by simp)⟩
def oRt (H : Host E) (N c : ℕ) : oRing H N c := 2 * oW H N c - 1
example (N c : ℕ) : ((oRt H N c : oRing H N c) : ℂ) = H.rt0 := by
  show (2 : ℂ) * ((1 + H.rt0) / 2) - 1 = H.rt0
  ring
theorem zeta_one : zeta 1 = 1 := by simp [zeta]
theorem oRing_le_KA (l : Level H) {N : ℕ} (h : zeta N ∈ KA l) (c : ℕ) : oRing H N c ≤ (KA l).toSubring := by
  refine Subring.closure_le.2 ?_
  have h1 : H.rt0 ∈ KA l := IntermediateField.subset_adjoin _ _ (by simp)
  rintro x (rfl | rfl | rfl)
  · exact (show w0C H ∈ KA l from div_mem (add_mem (one_mem (KA l)) h1) (ofNat_mem (KA l) 2))
  · exact h
  · exact (show (c : ℂ)⁻¹ ∈ KA l from inv_mem (natCast_mem (KA l) c))
def toKA (l : Level H) {N : ℕ} (h : zeta N ∈ KA l) (c : ℕ) : oRing H N c →+* KA l :=
  (oRing H N c).subtype.codRestrict (KA l) (fun x => oRing_le_KA l h c x.2)
theorem zeta_mem_of_eq (l : Level H) {N : ℕ} (h : l.A = N) : zeta N ∈ KA l := by
  subst h
  exact IntermediateField.subset_adjoin _ _ (by simp)
theorem zeta_one_mem (l : Level H) : zeta 1 ∈ KA l := by rw [zeta_one]; exact one_mem _
theorem oRing_le_mul (N n e : ℕ) (he : 0 < e) : oRing H N n ≤ oRing H N (n * e) := by
  refine Subring.closure_le.2 ?_
  rintro x (rfl | rfl | rfl)
  · exact Subring.subset_closure (by simp)
  · exact Subring.subset_closure (by simp)
  · have h : (n : ℂ)⁻¹ = (e : ℂ) * ((n * e : ℕ) : ℂ)⁻¹ := by
      have : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.2 he.ne'
      push_cast
      rw [mul_inv, mul_comm (n : ℂ)⁻¹, ← _root_.mul_assoc, mul_inv_cancel₀ this, _root_.one_mul]
    rw [SetLike.mem_coe, h]
    exact mul_mem (natCast_mem _ e) (Subring.subset_closure (by simp))
theorem oRing_one_le (N c : ℕ) : oRing H 1 c ≤ oRing H N c := by
  refine Subring.closure_le.2 ?_
  rintro x (rfl | rfl | rfl)
  · exact Subring.subset_closure (by simp)
  · rw [zeta_one]; exact one_mem _
  · exact Subring.subset_closure (by simp)
theorem oRing_le_oLoc (p N n : ℕ) (h : n.Coprime p) : oRing H N n ≤ oLoc H p N := by
  refine Subring.closure_le.2 ?_
  rintro x (rfl | rfl | rfl)
  · exact Subring.subset_closure (Or.inl rfl)
  · exact Subring.subset_closure (Or.inr (Or.inl rfl))
  · exact Subring.subset_closure (Or.inr (Or.inr ⟨n, h, rfl⟩))
theorem ZP_le_oLoc (p N : ℕ) : ZP p N ≤ oLoc H p N := Subring.closure_mono Set.subset_union_right
structure FullObj (D : Datum H) (N : ℕ) {B : Type} [CommRing B] (ρ ζ : B) {S : Scheme.{0}} (s : S ⟶ Sp B) where
  t : SAB H S
  proper : IsProper t.G.hom
  ample : Out.RelAmple t.G t.PP.L
  ktriv : Out.KTriv t.G t.PP.L
  lev : D.La → (𝟙_ (Over S) ⟶ t.G)
  lev_add : ∀ a c, lev (a + c) = lev a * lev c
  lev_lin : ∀ (c : 𝓞 E) a, lev (c • a) = lev a ≫ t.act.act c
  lev_ker : ∀ a, lev (N • a) = 1
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k) (z : kˣ), x ≫ s = spMap β →
    (z : k) = β ζ →
    (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = N • b)) ∧
    (∀ g : Over.mk x ⟶ t.G, g ^ N = 1 → ∃ a, toUnit _ ≫ lev a = g) ∧
    ∀ a b, Out.WeilIs t.G t.PP.L N (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z ^ D.EF a b))
  geom0 : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : B →+* k), x ≫ s = spMap β →
    DetCond D t.act x (β ρ) ∧
    ∃ I : TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)),
      (I.ζ N : k) = β ζ ∧ ∀ a, toUnit _ ≫ lev a = I.ev N a
structure FullMap {D : Datum H} {N : ℕ} {B : Type} [CommRing B] {ρ ζ : B} {S' S : Scheme.{0}} {s' : S' ⟶ Sp B}
    {s : S ⟶ Sp B} (o' : FullObj D N ρ ζ s') (o : FullObj D N ρ ζ s) (f : S' ⟶ S) extends SABMap o'.t o.t f where
  lev : ∀ a, (o'.lev a).left ≫ cm.F = f ≫ (o.lev a).left
def IsSimMod (D : Datum H) (N : ℕ) (gm : D.La →ₗ[𝓞 E] D.La) (ν : ℕ) : Prop :=
  (∃ gi : D.La →ₗ[𝓞 E] D.La, ∀ a, D.ModN N (gi (gm a) - a) ∧ D.ModN N (gm (gi a) - a)) ∧
    ∀ a b, (N : ℤ) ∣ D.EF (gm a) (gm b) - ν * D.EF a b
def gDim (D : Datum H) : ℕ := Module.finrank ℚ E / 2 * (D.p + D.q)
structure FullPre (D : Datum H) (N n : ℕ) extends PModel H (oRing H N n) where
  U : X.Opens
  U_eq : (U : Set X) = abLocus t.G
  U_dense : Dense (U : Set X)
  ab : FullObj D N (oRt H N n) (oZeta H N n) (U.ι ≫ s)
  mU : SABMap ab.t t U.ι
namespace FullPre
variable {D : Datum H} {N n : ℕ} (Z : FullPre D N n)
def Universal : Prop :=
  ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (oRing H N n)), IsReduced S → (∀ x : S, CharZero (S.residueField x)) →
    ∀ o : FullObj D N (oRt H N n) (oZeta H N n) s',
      ∃! f : S ⟶ Z.U.toScheme, f ≫ Z.U.ι ≫ Z.s = s' ∧ Nonempty (FullMap o Z.ab f)
def LevelChanges : Prop :=
  ∀ (σ : oRing H N n ≃+* oRing H N n) (gm : D.La →ₗ[𝓞 E] D.La) (ν : ℕ), IsSimMod D N gm ν →
    σ (oW H N n) = oW H N n → σ (oZeta H N n) = oZeta H N n ^ ν →
    ∃ (ρ : Z.X ≅ Z.X) (mu : SABMap Z.t Z.t ρ.hom) (ρU : Z.U.toScheme ⟶ Z.U.toScheme),
      ρ.hom ≫ Z.s = Z.s ≫ spMap σ.toRingHom ∧ ρU ≫ Z.U.ι = Z.U.ι ≫ ρ.hom ∧
      ∀ a, (Z.ab.lev (gm a)).left ≫ Z.mU.φ ≫ mu.φ = ρU ≫ (Z.ab.lev a).left ≫ Z.mU.φ
def GoodRedExt (V K : Type) [CommRing V] [Field K] [Algebra V K] : Prop :=
  ∀ (b : oRing H N n →+* V) (y : Sp K ⟶ Z.U.toScheme), y ≫ Z.U.ι ≫ Z.s = spMap (algebraMap V K) ≫ spMap b →
    (∃ (𝒜 : Over (Sp V)) (_ : GrpObj 𝒜) (𝓛 : LB 𝒜.left) (A : Over (Sp K)) (_ : GrpObj A)
      (φ₁ : A.left ⟶ 𝒜.left) (φ₂ : A.left ⟶ Z.ab.t.G.left),
      IsAbelianScheme 𝒜 ∧ 𝓛.IsLB ∧ Out.RelAmple 𝒜 𝓛 ∧ IsGrpPullback A 𝒜 (spMap (algebraMap V K)) φ₁ ∧
      IsGrpPullback A Z.ab.t.G y φ₂ ∧ LBIso (𝓛.pull φ₁) (Z.ab.t.PP.L.pull φ₂)) →
    ∃ y' : Sp V ⟶ Z.U.toScheme, y' ≫ Z.U.ι ≫ Z.s = spMap b ∧ spMap (algebraMap V K) ≫ y' = y
def GoodPointsExtend : Prop :=
  (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Z.GoodRedExt V K) ∧
  ∀ (p : ℕ) (V C : Type) [CommRing V] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [IsAlgClosed C] [CharZero C] [Algebra V C], p.Prime → IsUnitBall V C → ‖(p : C)‖ < 1 → Z.GoodRedExt V C
def SiegelFinite : Prop :=
  ∃ (XX : Scheme.{0}) (w : XX ⟶ Sp (oRing H N n)) (oX : FullObj D N (oRt H N n) (oZeta H N n) w)
    (u : Z.U.toScheme ⟶ XX) (_ : FullMap Z.ab oX u) (W : XX.Opens),
    IsReduced XX ∧ Flat w ∧ u ≫ w = Z.U.ι ≫ Z.s ∧ IsFinite u ∧ Surjective u ∧ IsIso (u ∣_ W) ∧
    (∀ x : XX, CharZero (XX.residueField x) → x ∈ W) ∧
    ∀ (p : ℕ) (hn : n.Coprime p), p.Prime →
      ∃ (Ag : SiegelFamily (gDim D) p N) (bas : (Fin (gDim D) ⊕ Fin (gDim D) → ℤ) ≃ₗ[ℤ] D.La)
        (cl : pullback w (spMap (Subring.inclusion (oRing_le_oLoc (H := H) p N n hn))) ⟶
          pullback Ag.s (spMap (Subring.inclusion (ZP_le_oLoc (H := H) p N))))
        (o : SiegPre (gDim D) N (zetaZP p N)
          (pullback.snd w (spMap (Subring.inclusion (oRing_le_oLoc (H := H) p N n hn))) ≫
            spMap (Subring.inclusion (ZP_le_oLoc (H := H) p N))))
        (φ : o.A.left ⟶ oX.t.G.left) (φ₂ : (G2 o.A).left ⟶ (G2 oX.t.G).left),
        (∀ a b, D.EF (bas a) (bas b) = omegaStd a b) ∧
        IsGrpPullback o.A oX.t.G (pullback.fst _ _) φ ∧ IsSquare φ φ₂ ∧
        LBIso o.P ((abelian₂ oX.t.G oX.t.PP.L).pull φ₂) ∧
        (∀ a, (o.lev a).left ≫ φ = pullback.fst _ _ ≫ (oX.lev (bas a)).left) ∧
        cl ≫ pullback.snd _ _ = pullback.snd _ _ ∧ SiegPB o Ag.univ (cl ≫ pullback.fst _ _) ∧
        IsFinite cl ∧ FormallyUnramified cl
end FullPre
structure FullModel {D : Datum H} (Xo : ∀ l : Level H, Moduli D l) (n J : ℕ) extends FullPre D (n ^ J) n where
  aux : AuxiliaryInertOddPrime H n
  J_pos : 1 ≤ J
  qproj : IsQProjOver (t.G.hom ≫ s)
  split : toPModel.SplitFibres
  theta : PushInvertible t.G t.PP.L
  sections : ∃ k : ℕ, 2 ≤ k ∧ 2 * k ≤ J ∧ PushFree t.G (lbPow t.PP.L (n ^ (2 * k))) ((n ^ (2 * k)) ^ gDim D)
  unif : toPModel.Uniformised
  univ : toFullPre.Universal
  acts : toFullPre.LevelChanges
  good : toFullPre.GoodPointsExtend
  siegel : toFullPre.SiegelFinite

  cover : ∀ l : Level H, l.A = n ^ J → ((Xo l).X ⟶ U.toScheme)
  cover_over : ∀ l h, cover l h ≫ U.ι ≫ s = (Xo l).s ≫ spMap (toKA l (zeta_mem_of_eq l h) n)
  coverM : ∀ l h, SABMap (Xo l).univ.t ab.t (cover l h)
  cover_lev : ∀ l h a, ((Xo l).univ.etaA a).left ≫ (coverM l h).φ = cover l h ≫ (ab.lev a).left
  cover_fet : ∀ l h (e : (Xo l).X ⟶ pullback (U.ι ≫ s) (spMap (toKA l (zeta_mem_of_eq l h) n))),
    e ≫ pullback.fst _ _ = cover l h → e ≫ pullback.snd _ _ = (Xo l).s → IsFinite e ∧ Etale e ∧ Surjective e
variable {D : Datum H}
def levelAt (l : Level H) (A : ℕ) (hA : 0 < A) : Level H := { l with A := A, A_pos := hA }
def IsLevelMap {l l₂ : Level H} (Xo₂ : Moduli D l₂) (Xo : Moduli D l) (r : Xo₂.X ⟶ Xo.X)
    (ν : SABMap Xo₂.univ.t Xo.univ.t r) : Prop :=
  l.Dvd l₂ ∧ (∃ jK : KA l →+* KA l₂, (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK) ∧
    (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ ν.φ = r ≫ (Xo.univ.eta a).left) ∧
    ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ ν.φ = r ≫ (Xo.univ.etaA a).left
def LevelActs {l : Level H} {Xo : Moduli D l} {O : Type} [CommRing O] {β : O →+* KA l}
    (Y : ModelOf Xo.s Xo.univ.t β) : Prop :=
  ∀ (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom) (gM gA : D.La →ₗ[𝓞 E] D.La) (σ : O ≃+* O)
    (σF : KA l ≃+* KA l), σF (baseKA l).ρ = (baseKA l).ρ → (∀ x, σF (β x) = β (σ x)) →
    r.hom ≫ Xo.s = Xo.s ≫ spMap σF.toRingHom →
    (∀ a, (Xo.univ.eta (gM a)).left ≫ ν.φ = r.hom ≫ (Xo.univ.eta a).left) →
    (∀ a, (Xo.univ.etaA (gA a)).left ≫ ν.φ = r.hom ≫ (Xo.univ.etaA a).left) →
    Y.ExtendsAut r ν σ
variable {Xo : ∀ l : Level H, Moduli D l} {n J : ℕ}
abbrev FullModel.up (Z : FullModel Xo n J) (l : Level H) : Level H :=
  levelAt l (n ^ J) (pow_pos Z.aux.prime.pos J)
structure BaseModels (Z : FullModel Xo n J) (l : Level H) (e : ℕ) where
  A_eq : l.A = 1
  e_pos : 0 < e
  Z₂ : ModelOf (Xo (Z.up l)).s (Xo (Z.up l)).univ.t (toKA (Z.up l) (zeta_mem_of_eq (Z.up l) (N := n ^ J) rfl) (n * e))
  toZ : FinMap Z₂.toPModel Z.toPModel (Subring.inclusion (oRing_le_mul (n ^ J) n e e_pos))
  toZ_j : Z₂.j ≫ toZ.π = Z.cover (Z.up l) rfl ≫ Z.U.ι
  toZ_φ : Z₂.m.φ ≫ toZ.mu.φ = (Z.coverM (Z.up l) rfl).φ ≫ Z.mU.φ
  Z₁ : ModelOf (Xo l).s (Xo l).univ.t (toKA l (zeta_one_mem l) (n * e))
  q : FinMap Z₂.toPModel Z₁.toPModel (Subring.inclusion (oRing_one_le (n ^ J) (n * e)))
  q_onto : Surjective q.π
  r : (Xo (Z.up l)).X ⟶ (Xo l).X
  ν : SABMap (Xo (Z.up l)).univ.t (Xo l).univ.t r
  lev : IsLevelMap (Xo (Z.up l)) (Xo l) r ν
  q_j : Z₂.j ≫ q.π = r ≫ Z₁.j
  q_φ : Z₂.m.φ ≫ q.mu.φ = ν.φ ≫ Z₁.m.φ
def BaseModels.Acts {Z : FullModel Xo n J} {l : Level H} {e : ℕ} (B : BaseModels Z l e) : Prop :=
  LevelActs B.Z₂ ∧ LevelActs B.Z₁
abbrev BaseFamily (Z : FullModel Xo n J) := ∀ l : Level H, l.A = 1 → BaseModels Z l l.M
def IsPrimeToPart (l₀ l : Level H) (p : ℕ) : Prop :=
  l₀.M = l.M / p ^ l.M.factorization p ∧ l.Mb ≤ l₀.Mb
def FromBase {Z : FullModel Xo n J} (B : BaseFamily Z) {p : ℕ} {W : ValuationSubring ℂ} (Y : LocalSystem Xo p W) :
    Prop :=
  n ≠ p ∧ ∀ i : Idx H p, ∃ (l₀ : Level H) (h₀ : l₀.A = 1) (b : oRing H 1 (n * l₀.M) →+* i.c.V W)
    (f : FinMap (ofModel (Y i)).toPModel (B l₀ h₀).Z₁.toPModel b)
    (r : (Xo i.l).X ⟶ (Xo l₀).X) (ν : SABMap (Xo i.l).univ.t (Xo l₀).univ.t r),
    IsPrimeToPart l₀ i.l p ∧ (∀ x, (((b x : i.c.V W) : i.c.F) : ℂ) = (x : ℂ)) ∧ IsLevelMap (Xo i.l) (Xo l₀) r ν ∧
    (Y i).j ≫ f.π = pullback.fst _ _ ≫ r ≫ (B l₀ h₀).Z₁.j ∧
    (Y i).m.φ ≫ f.mu.φ = (Y i).m0.toSABMap.φ ≫ ν.φ ≫ (B l₀ h₀).Z₁.m.φ
def FromTwoBases {n₁ J₁ n₂ J₂ : ℕ} {Z₁ : FullModel Xo n₁ J₁} {Z₂ : FullModel Xo n₂ J₂} (B₁ : BaseFamily Z₁)
    (B₂ : BaseFamily Z₂)
    (Y : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W) : Prop :=
  n₁ ≠ n₂ ∧ ∀ p W hp hW, FromBase B₁ (Y p W hp hW) ∨ FromBase B₂ (Y p W hp hW)
end GlobalTheory.IndefiniteRowSideFullHecke.FullLevelModel


