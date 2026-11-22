-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:35:33.30995+00:00
-- url     : https://prove2.me/theorems/67de6699-15b2-47fb-9138-2d5851d75633
-- title:
--   Clauses
-- statement:
--   Definitions and structural lemmas for Clauses, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/Clauses.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
section Siegel
variable {S : Scheme.{0}}
def omegaStd {h : ℕ} (a b : Fin h ⊕ Fin h → ℤ) : ℤ := ∑ i, (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i))
structure SiegPre (h M₁ : ℕ) {B : Type} [CommRing B] (ζ : B) (s : S ⟶ Sp B) where
  A : Over S
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  P : LB (G2 A).left
  isLB : P.IsLB
  rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen
  rig₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen
  symm : LBIso P (P.pull (lift (snd A A) (fst A A)).left)
  lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)
  lev_add : ∀ a b, lev (a + b) = lev a * lev b
  lev_tors : ∀ a, lev a ^ M₁ = 1
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k) (z : kˣ), x ≫ s = spMap β → (z : k) = β ζ →
    (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M₁ • b)) ∧
    (∀ g : Over.mk x ⟶ A, g ^ M₁ = 1 → ∃ a, toUnit _ ≫ lev a = g) ∧
    ∀ a b, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) M₁ (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b)
      (unitOn (z ^ (2 * omegaStd a b)))
attribute [instance] SiegPre.grp SiegPre.comm
variable {h M₁ : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {s : S ⟶ Sp B}
def SiegPre.diag (o : SiegPre h M₁ ζ s) : LB o.A.left := o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left
def SiegPre.Principal (o : SiegPre h M₁ ζ s) : Prop :=
  Out.RelAmple o.A o.diag ∧
    ∀ (T : Over S) (x : T ⟶ o.A),
      (∃ t : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, t.IsGen) → x = 1
def IsSquare {S' : Scheme.{0}} {G' : Over S'} {G : Over S} (φ : G'.left ⟶ G.left)
    (φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left) : Prop :=
  φ₂ ≫ (fst G G).left = (fst G' G').left ≫ φ ∧ φ₂ ≫ (snd G G).left = (snd G' G').left ≫ φ
def SiegPB {S' : Scheme.{0}} {s' : S' ⟶ Sp B'} (o' : SiegPre h M₁ ζ' s') (o : SiegPre h M₁ ζ s) (f : S' ⟶ S) : Prop :=
  ∃ (φ : o'.A.left ⟶ o.A.left) (φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left),
    IsGrpPullback o'.A o.A f φ ∧ IsSquare φ φ₂ ∧ LBIso o'.P (o.P.pull φ₂) ∧
      ∀ a, (o'.lev a).left ≫ φ = f ≫ (o.lev a).left
def ZP (p M : ℕ) : Subring ℂ := Subring.closure ({zeta M} ∪ {x | ∃ n : ℕ, n.Coprime p ∧ x = (n : ℂ)⁻¹})
def zetaZP (p M : ℕ) : ZP p M := ⟨zeta M, Subring.subset_closure (Or.inl rfl)⟩
def IsUnitBall (O C : Type) [CommRing O] [NormedField C] [Algebra O C] : Prop :=
  Function.Injective (algebraMap O C) ∧ ∀ x : C, x ∈ Set.range (algebraMap O C) ↔ ‖x‖ ≤ 1
structure SiegelFamily (h p M₁ : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp (ZP p M₁)
  smooth : SmoothOfRelativeDimension (h * (h + 1) / 2) s
  qc : QuasiCompact s
  univ : SiegPre h M₁ (zetaZP p M₁) s
  princ : univ.Principal

  points : ∀ (C O : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
    [CommRing O] [IsLocalRing O] [Algebra O C], IsUnitBall O C → ‖(p : C)‖ < 1 →
    ∀ (β : ZP p M₁ →+* O) (o : SiegPre h M₁ (zetaZP p M₁) (spMap β)),
      (∃ o' : SiegPre h M₁ (zetaZP p M₁) (spMap (algebraMap O C) ≫ spMap β),
        SiegPB o' o (spMap (algebraMap O C)) ∧ o'.Principal) →
      Out.RelAmple (Over.mk (pullback.snd o.A.hom (spMap (IsLocalRing.residue O))))
        (o.diag.pull (pullback.fst o.A.hom (spMap (IsLocalRing.residue O)))) →
      ∃ x : Sp O ⟶ X, x ≫ s = spMap β ∧ SiegPB o univ x

  unram : ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ X) (o : SiegPre h M₁ (zetaZP p M₁) (x ≫ s)),
    SiegPB o univ x → SiegPB o univ (constPt x) → x = constPt x
def N0 : Prop :=
  ∀ h p n : ℕ, 1 ≤ h → p.Prime → n.Prime → Odd n → n ≠ p →
    ∃ j : ℕ, 3 ≤ n ^ j ∧ Nonempty (SiegelFamily h p (n ^ j))
end Siegel
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
structure Idx (H : Host E) (p : ℕ) where
  l : Level H
  c : Coeff l
  good : l.GoodAt p
abbrev Coeff.V {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) : ValuationSubring c.F :=
  W.comap c.F.val.toRingHom
abbrev LocalSystem (Xo : ∀ l : Level H, Moduli D l) (p : ℕ) (W : ValuationSubring ℂ) :=
  ∀ i : Idx H p, Model (Xo i.l) i.c (i.c.V W).subtype
section Local
variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
def Model.GoodRedExt (Y : Model Xo c β) (V K : Type) [CommRing V] [Field K] [Algebra V K] : Prop :=
  ∀ (b : O →+* V) (y : Sp K ⟶ Xo.XF c), y ≫ Y.j ≫ Y.s = spMap (algebraMap V K) ≫ spMap b →
    (∃ (𝒜 : Over (Sp V)) (_ : GrpObj 𝒜) (𝓛 : LB 𝒜.left) (A : Over (Sp K)) (_ : GrpObj A)
      (φ₁ : A.left ⟶ 𝒜.left) (φ₂ : A.left ⟶ Y.oF.t.G.left),
      IsAbelianScheme 𝒜 ∧ 𝓛.IsLB ∧ Out.RelAmple 𝒜 𝓛 ∧ IsGrpPullback A 𝒜 (spMap (algebraMap V K)) φ₁ ∧
      IsGrpPullback A Y.oF.t.G y φ₂ ∧ LBIso (𝓛.pull φ₁) (Y.oF.t.PP.L.pull φ₂)) →
    ∃ y' : Sp V ⟶ Y.X, y' ≫ Y.s = spMap b ∧ spMap (algebraMap V K) ≫ y' = y ≫ Y.j ∧
      Set.range y' ⊆ abLocus Y.t.G
def Model.LevelStructureConditions (Y : Model Xo c β) (p : ℕ) : Prop :=
  Y.LevelActs ∧ (l.A = 1 → Y.Descends) ∧ PushInvertible Y.t.G Y.t.PP.L ∧
  (∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧ ∀ (a : D.La) (n : ℕ), n.Coprime p →
    (Y.oF.eta a ^ n = 1 → Y.Extends U (Y.oF.eta a)) ∧ (Y.oF.etaA a ^ n = 1 → Y.Extends U (Y.oF.etaA a))) ∧
  (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    [Field K] [Algebra V K] [IsFractionRing V K], Y.GoodRedExt V K) ∧
  ∀ (V C : Type) [CommRing V] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    [CharZero C] [Algebra V C], IsUnitBall V C → ‖(p : C)‖ < 1 → Y.GoodRedExt V C
def SiegelCompare {l₁ : Level H} {Xo₁ : Moduli D l₁} {c₁ : Coeff l₁} {O₁ : Type} [CommRing O₁] {β₁ : O₁ →+* c₁.F}
    (Y : Model Xo c β) (Y₁ : Model Xo₁ c₁ β₁) (b : O →+* O₁) (π : Y₁.X ⟶ Y.X) {g p M₁ : ℕ}
    (Ag : SiegelFamily g p M₁) (z : ZP p M₁ →+* O₁) : Prop :=
  ∀ (U : Y.X.Opens) (U₁ : Y₁.X.Opens), (U : Set Y.X) = abLocus Y.t.G → (U₁ : Set Y₁.X) = abLocus Y₁.t.G →
    (∃ e : U₁.toScheme ⟶ pullback (U.ι ≫ Y.s) (spMap b),
      e ≫ pullback.fst _ _ ≫ U.ι = U₁.ι ≫ π ∧ e ≫ pullback.snd _ _ = U₁.ι ≫ Y₁.s ∧
      IsFinite e ∧ Etale e ∧ Surjective e) ∧
    ∃ (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (cl : U₁.toScheme ⟶ pullback Ag.s (spMap z))
      (o : SiegPre g M₁ (zetaZP p M₁) (U₁.ι ≫ Y₁.s ≫ spMap z)) (φ : o.A.left ⟶ Y₁.t.G.left)
      (φ₂ : (G2 o.A).left ⟶ (G2 Y₁.t.G).left),
      (∀ u v, D.EF (bas u) (bas v) = omegaStd u v) ∧
      IsGrpPullback o.A Y₁.t.G U₁.ι φ ∧ IsSquare φ φ₂ ∧ LBIso o.P ((abelian₂ Y₁.t.G Y₁.t.PP.L).pull φ₂) ∧
      (∀ u (j' : Xo₁.XF c₁ ⟶ U₁.toScheme), j' ≫ U₁.ι = Y₁.j →
        j' ≫ (o.lev u).left ≫ φ = (Y₁.oF.etaA (bas u) ^ (l₁.A / M₁)).left ≫ Y₁.m.φ) ∧
      cl ≫ pullback.snd _ _ = U₁.ι ≫ Y₁.s ∧ SiegPB o Ag.univ (cl ≫ pullback.fst _ _) ∧ IsFinite cl ∧
      (¬ p ∣ l.M' →
        ∃ (XX : Scheme.{0}) (u : U₁.toScheme ⟶ XX) (w : XX ⟶ pullback Ag.s (spMap z)) (W : XX.Opens)
          (t : SAB H XX) (t₁ : SAB H U₁.toScheme) (m₁ : SABMap t₁ Y₁.t U₁.ι) (m₂ : SABMap t₁ t u)
          (η' ηA' : D.La → (𝟙_ (Over XX) ⟶ t.G)),
          u ≫ w = cl ∧ IsFinite u ∧ Surjective u ∧ Dense (W : Set XX) ∧ IsIso (u ∣_ W) ∧
          Dense ((u ⁻¹ᵁ W : U₁.toScheme.Opens) : Set U₁.toScheme) ∧
          IsAbelianScheme t.G ∧ IsReduced XX ∧ Flat (w ≫ pullback.snd _ _) ∧ IsFinite w ∧ FormallyUnramified w ∧
          ∀ (a : D.La) (j' : Xo₁.XF c₁ ⟶ U₁.toScheme) (g₁ : Xo₁.XF c₁ ⟶ t₁.G.left), j' ≫ U₁.ι = Y₁.j →
            (g₁ ≫ m₁.φ = (Y₁.oF.eta a).left ≫ Y₁.m.φ → g₁ ≫ m₂.φ = j' ≫ u ≫ (η' a).left) ∧
            (g₁ ≫ m₁.φ = (Y₁.oF.etaA a).left ≫ Y₁.m.φ → g₁ ≫ m₂.φ = j' ≫ u ≫ (ηA' a).left))
end Local
def IsIncl {l l₂ : Level H} {c : Coeff l} {c₂ : Coeff l₂} {W : ValuationSubring ℂ} (b : c.V W →+* c₂.V W) : Prop :=
  ∀ x : c.V W, (((b x : c₂.V W) : c₂.F) : ℂ) = ((x : c.F) : ℂ)
def N2 {Xo : ∀ l : Level H, Moduli D l} {p : ℕ} {W : ValuationSubring ℂ} (Y : LocalSystem Xo p W) : Prop :=
  (∀ i, (Y i).LevelStructureConditions p) ∧
  ∃ π : ∀ i i₂ : Idx H p, i.l.Dvd i₂.l → i.c.F ≤ i₂.c.F → ((Y i₂).X ⟶ (Y i).X),
    (∀ i i₂ hl hc (b : i.c.V W →+* i₂.c.V W), IsIncl b → IsTransition (Y i) (Y i₂) b (π i i₂ hl hc)) ∧
    ∃ (n j : ℕ) (Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p (n ^ j)),
      n.Prime ∧ Odd n ∧ n ≠ p ∧ 3 ≤ n ^ j ∧ (∀ l : Level H, n.Coprime l.M) ∧
      ∀ i i₁ hl hc (b : i.c.V W →+* i₁.c.V W) (z : ZP p (n ^ j) →+* i₁.c.V W), IsIncl b →
        (∀ x, (((z x : i₁.c.V W) : i₁.c.F) : ℂ) = (x : ℂ)) →
        i₁.l.M = i.l.M → i₁.l.Mb = i.l.Mb → i₁.l.A = Nat.lcm i.l.A (n ^ j) →
        i₁.c.F = i.c.F ⊔ IntermediateField.adjoin ℚ {zeta (n ^ j)} →
        SiegelCompare (Y i) (Y i₁) b (π i i₁ hl hc) Ag z
def N6 {Xo : ∀ l : Level H, Moduli D l}
    (Y : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W) : Prop :=
  ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p), l.A = 1 →
    ∃ Ygl : Model (Xo l) c (algebraMap (𝓞 c.F) c.F), Ygl.Descends ∧
      ∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W),
        (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → Dominates Ygl (Y p W hp hW ⟨l, c, hg p hp⟩) b
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


