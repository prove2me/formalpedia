-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
-- name    : Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:11.92981+00:00
-- url     : https://prove2.me/theorems/923ea807-02f9-4671-89a8-eb04a6af6fba
-- title:
--   Auxiliary Inert Odd Prime
-- statement:
--   Definitions and structural lemmas for Auxiliary Inert Odd Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/AuxiliaryInertOddPrime.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
noncomputable section
namespace GlobalTheory.Models
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def RZ (H : Host E) (S A : ℕ) : Subring ℂ := Subring.closure {(1 + H.rt0) / 2, (S : ℂ)⁻¹, zeta A}
def IsInc {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* ℂ) (i' : R' →+* ℂ) (β : R →+* R') : Prop :=
  ∀ x, i' (β x) = i x
def IsDedFrac {O F : Type} [CommRing O] [Field F] (β : O →+* F) : Prop :=
  (∃ _ : IsDomain O, IsDedekindDomain O) ∧ CharZero O ∧ @IsFractionRing O _ F _ β.toAlgebra
variable {H : Host E}
structure Cpt {U : Scheme.{0}} {F : Type} [Field F] (c : U ⟶ Sp F) (t₀ : SAB H U) {O : Type} [CommRing O]
    (β : O →+* F) where
  X : Scheme.{0}
  s : X ⟶ Sp O
  normal : IsNormalScheme X
  proj : IsProjOver s
  flat : Flat s
  jQ : U ⟶ pullback s (spMap β)
  jQ_over : jQ ≫ pullback.snd _ _ = c
  jQ_open : IsOpenImmersion jQ
  jQ_dense : Dense (Set.range jQ)
  t : SAB H X
  m : SABMap t₀ t (jQ ≫ pullback.fst _ _)
  ab_gen : pullback.fst s (spMap β) ⁻¹' abLocus t.G = Set.range jQ
def AbOpen {X : Scheme.{0}} (G : Over X) : Prop :=
  ∃ U : X.Opens, (U : Set X) = abLocus G ∧ IsProper (G.hom ∣_ U)
def SplitFib {X : Scheme.{0}} (G : Over X) [GrpObj G] : Prop :=
  ∀ x : X, ∃ (k : Type) (_ : Field k) (_ : Algebra (X.residueField x) k), FiniteDimensional (X.residueField x) k ∧ Algebra.IsSeparable (X.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x)).obj G)
def HasTheta {X : Scheme.{0}} (G : Over X) (L : LB G.left) : Prop :=
  ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ V), ∀ y ∈ V, ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i)
def Good {X : Scheme.{0}} (t : SAB H X) : Prop := AbOpen t.G ∧ SplitFib t.G ∧ HasTheta t.G t.PP.L
section
variable {U U' : Scheme.{0}} {F F' : Type} [Field F] [Field F'] {c : U ⟶ Sp F} {c' : U' ⟶ Sp F'} {t₀ : SAB H U}
  {t₀' : SAB H U'} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* F} {β' : O' →+* F'}
def Cpt.j (C : Cpt c t₀ β) : U ⟶ C.X := C.jQ ≫ pullback.fst _ _
structure Cpt.Above (C' : Cpt c' t₀' β') (C : Cpt c t₀ β) (b : O →+* O') (r : U' ⟶ U) (ν : SABMap t₀' t₀ r) where
  π : C'.X ⟶ C.X
  π_over : π ≫ C.s = C'.s ≫ spMap b
  fin : IsFinite (pullback.lift π C'.s π_over)
  mu : SABMap C'.t C.t π
  j_comm : C'.j ≫ π = r ≫ C.j
  φ_comm : C'.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ
def Cpt.ExtendsAut (C : Cpt c t₀ β) (r : U ≅ U) (ν : SABMap t₀ t₀ r.hom) : Prop :=
  ∃ (ρ : C.X ≅ C.X) (mu : SABMap C.t C.t ρ.hom), ρ.hom ≫ C.s = C.s ∧ C.j ≫ ρ.hom = r.hom ≫ C.j ∧
    C.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ
end
variable {D : Datum H}
def ofModel {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Cpt (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) Y.oF.t β :=
  ⟨Y.X, Y.s, Y.normal, Y.proj, Y.flat, Y.jQ, Y.jQ_over, Y.jQ_open, Y.jQ_dense, Y.t, Y.m, Y.ab_gen⟩
def LevComp {l l' : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l' B'}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} (o' : Obj D l' b' s') (o : Obj D l b s) (r : S' ⟶ S)
    (ν : SABMap o'.t o.t r) : Prop :=
  (∀ a, (o'.eta a ^ (l'.M / l.M)).left ≫ ν.φ = r ≫ (o.eta a).left) ∧
    ∀ a, (o'.etaA a ^ (l'.A / l.A)).left ≫ ν.φ = r ≫ (o.etaA a).left
def SiegData {T : Scheme.{0}} {O : Type} [CommRing O] (sT : T ⟶ Sp O) (t : SAB H T)
    (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) {g p N : ℕ} (Ag : SiegelFamily g p N) (z : ZP p N →+* O)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (cl : T ⟶ pullback Ag.s (spMap z)) : Prop :=
  ∃ (o : SiegPre g N (zetaZP p N) (sT ≫ spMap z)) (φ : o.A.left ⟶ t.G.left) (φ₂ : (G2 o.A).left ⟶ (G2 t.G).left),
    IsGrpPullback o.A t.G (𝟙 T) φ ∧ IsSquare φ φ₂ ∧ LBIso o.P ((abelian₂ t.G t.PP.L).pull φ₂) ∧
    (∀ u, (o.lev u).left ≫ φ = (lev (bas u)).left) ∧ cl ≫ pullback.snd _ _ = sT ∧
    SiegPB o Ag.univ (cl ≫ pullback.fst _ _)
structure Top (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) where
  Z : Scheme.{0}
  s : Z ⟶ Sp (RZ H n N)
  normal : IsNormalScheme Z
  proj : IsProjOver s
  flat : Flat s
  t : SAB H Z
  qproj : IsQProjOver (t.G.hom ≫ s)
  good : Good t
  ga : genericPoints Z ⊆ abLocus t.G
  a : ∀ l : Level H, l.A = N → ((Xo l).X ⟶ Z)
  m : ∀ l h, SABMap (Xo l).univ.t t (a l h)
  fin : ∀ l h (β : RZ H n N →+* KA l), IsInc (RZ H n N).subtype (KA l).val.toRingHom β →
    ∃ (W : (pullback s (spMap β)).Opens) (f : (Xo l).X ⟶ W.toScheme),
      (W : Set _) = pullback.fst s (spMap β) ⁻¹' abLocus t.G ∧ IsFinite f ∧ Surjective f ∧
      f ≫ W.ι ≫ pullback.fst _ _ = a l h ∧ f ≫ W.ι ≫ pullback.snd _ _ = (Xo l).s
  compat : ∀ l l' h h' (r : (Xo l').X ⟶ (Xo l).X) (ν : SABMap (Xo l').univ.t (Xo l).univ.t r) (k : KA l →+* KA l'),
    IsInc (KA l).val.toRingHom (KA l').val.toRingHom k → r ≫ (Xo l).s = (Xo l').s ≫ spMap k →
    (∀ x, ((Xo l').univ.etaA x).left ≫ ν.φ = r ≫ ((Xo l).univ.etaA x).left) →
    r ≫ a l h = a l' h' ∧ ν.φ ≫ (m l h).φ = (m l' h').φ
  sym : ∀ l h (r : (Xo l).X ≅ (Xo l).X) (ν : SABMap (Xo l).univ.t (Xo l).univ.t r.hom) (g : D.La →ₗ[𝓞 E] D.La)
    (σ : KA l ≃+* KA l), σ (baseKA l).ρ = (baseKA l).ρ → r.hom ≫ (Xo l).s = (Xo l).s ≫ spMap σ.toRingHom →
    (∀ x, ((Xo l).univ.etaA (g x)).left ≫ ν.φ = r.hom ≫ ((Xo l).univ.etaA x).left) →
    ∃ ρ : Z ≅ Z, a l h ≫ ρ.hom = r.hom ≫ a l h
  U : Z.Opens
  U_eq : (U : Set Z) = abLocus t.G
  MM : Scheme.{0}
  sM : MM ⟶ Sp (RZ H n N)
  tM : SAB H MM
  lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)
  MM_red : IsReduced MM
  MM_flat : Flat sM
  MM_ab : IsProper tM.G.hom
  u : U.toScheme ⟶ MM
  u_over : u ≫ sM = U.ι ≫ s
  u_fin : IsFinite u
  u_surj : Surjective u
  u_gen : ∃ W : MM.Opens, (∀ x : MM, (sM x).asIdeal = ⊥ → x ∈ W) ∧ IsIso (u ∣_ W)
  tU : SAB H U.toScheme
  mU : SABMap tU t U.ι
  mM : SABMap tU tM u
  lev_eq : ∀ l h (a' : (Xo l).X ⟶ U.toScheme) (x : D.La) (y : (Xo l).X ⟶ tU.G.left), a' ≫ U.ι = a l h →
    y ≫ mU.φ = ((Xo l).univ.etaA x).left ≫ (m l h).φ → y ≫ mM.φ = a' ≫ u ≫ (lev x).left
  sieg : ∀ p : ℕ, p.Prime → p ≠ n → ∃ (Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p N)
    (bas : (Fin (Module.finrank ℚ E / 2 * (D.p + D.q)) ⊕ Fin (Module.finrank ℚ E / 2 * (D.p + D.q)) → ℤ) ≃ₗ[ℤ] D.La),
    (∀ x y, D.EF (bas x) (bas y) = omegaStd x y) ∧
    ∀ (O : Type) [CommRing O] (i : O →+* ℂ) (z : ZP p N →+* O) (b : RZ H n N →+* O), Function.Injective i →
      IsInc (ZP p N).subtype i z → IsInc (RZ H n N).subtype i b →
      ∀ (T : Scheme.{0}) (sT : T ⟶ Sp O) (f : T ⟶ MM) (tT : SAB H T) (ν : SABMap tT tM f)
        (levT : D.La → (𝟙_ (Over T) ⟶ tT.G)), IsPullback f sT sM (spMap b) →
        (∀ x, (levT x).left ≫ ν.φ = f ≫ (lev x).left) →
        ∃ w : T ⟶ pullback Ag.s (spMap z), SiegData sT tT levT Ag z bas w ∧ IsFinite w ∧ FormallyUnramified w
def AuxiliaryInertOddPrime (H : Host E) (n : ℕ) : Prop :=
  n.Prime ∧ Odd n ∧ ¬ IsSquare (-(H.d : ZMod n)) ∧ ¬ (n : ℤ) ∣ NumberField.discr E
structure BaseModel {Xo : ∀ l : Level H, Moduli D l} {n N : ℕ} (T : Top Xo n N) (l₀ : Level H) where
  A_one : l₀.A = 1
  β : RZ H (n * l₀.M) 1 →+* KA l₀
  β_inc : IsInc (RZ H (n * l₀.M) 1).subtype (KA l₀).val.toRingHom β
  C : Cpt (Xo l₀).s (Xo l₀).univ.t β
  good : Good C.t
  acts : ∀ (r : (Xo l₀).X ≅ (Xo l₀).X) (ν : SABMap (Xo l₀).univ.t (Xo l₀).univ.t r.hom) (g : D.La →ₗ[𝓞 E] D.La),
    r.hom ≫ (Xo l₀).s = (Xo l₀).s → (∀ x, ((Xo l₀).univ.eta (g x)).left ≫ ν.φ = r.hom ≫ ((Xo l₀).univ.eta x).left) →
    C.ExtendsAut r ν
  l₁ : Level H
  M_eq : l₁.M = l₀.M
  Mb_eq : l₁.Mb = l₀.Mb
  A_eq : l₁.A = N
  β₁ : RZ H (n * l₀.M) N →+* KA l₁
  β₁_inc : IsInc (RZ H (n * l₀.M) N).subtype (KA l₁).val.toRingHom β₁
  C₁ : Cpt (Xo l₁).s (Xo l₁).univ.t β₁
  b : RZ H (n * l₀.M) 1 →+* RZ H (n * l₀.M) N
  b_inc : IsInc (RZ H (n * l₀.M) 1).subtype (RZ H (n * l₀.M) N).subtype b
  r : (Xo l₁).X ⟶ (Xo l₀).X
  ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r
  lev : LevComp (Xo l₁).univ (Xo l₀).univ r ν
  r_surj : Surjective r
  above : C₁.Above C b r ν
  b' : RZ H n N →+* RZ H (n * l₀.M) N
  b'_inc : IsInc (RZ H n N).subtype (RZ H (n * l₀.M) N).subtype b'
  q : C₁.X ⟶ T.Z
  q_over : q ≫ T.s = C₁.s ≫ spMap b'
  q_fin : IsFinite (pullback.lift q C₁.s q_over)
  qm : SABMap C₁.t T.t q
  q_j : C₁.j ≫ q = T.a l₁ A_eq
  q_φ : C₁.m.φ ≫ qm.φ = (T.m l₁ A_eq).φ
def Raises {Xo : ∀ l : Level H, Moduli D l} {n N : ℕ} {T : Top Xo n N} {l₀ l : Level H} (B : BaseModel T l₀)
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model (Xo l) c β) : Prop :=
  ∃ (b : RZ H (n * l₀.M) 1 →+* O) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap Y.oF.t (Xo l₀).univ.t r),
    IsInc (RZ H (n * l₀.M) 1).subtype (c.F.val.toRingHom.comp β) b ∧ LevComp Y.oF (Xo l₀).univ r ν ∧
    Nonempty ((ofModel Y).Above B.C b r ν)
def IsPrimeToPart (l₀ l : Level H) (p : ℕ) : Prop :=
  l₀.A = 1 ∧ l₀.M = l.M / p ^ l.M.factorization p ∧ l₀.Mb = l.Mb ⊔ Ideal.span {(l₀.M : 𝓞 E)}
structure System (Xo : ∀ l : Level H, Moduli D l) where
  n : Bool → ℕ
  J : Bool → ℕ
  aux : ∀ i, AuxiliaryInertOddPrime H (n i)
  J_pos : ∀ i, 1 ≤ J i
  T : ∀ i, Top Xo (n i) (n i ^ J i)
  B : ∀ i (l₀ : Level H), l₀.A = 1 → BaseModel (T i) l₀
  ch : ℕ → Bool
  ch_ne : ∀ p, n (ch p) ≠ p
  Y : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W
  raises : ∀ p W hp hW (i : Idx H p), ∃ (l₀ : Level H) (h : IsPrimeToPart l₀ i.l p),
    Raises (B (ch p) l₀ h.1) (Y p W hp hW i)
end GlobalTheory.Models
end


