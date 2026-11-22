-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:52.613034+00:00
-- url     : https://prove2.me/theorems/e4a1a640-e2c2-43c1-b4ee-a4aa1bf6d31b
-- title:
--   Two Weight Eq One Add Root
-- statement:
--   Definitions and structural lemmas for Two Weight Eq One Add Root, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/TwoWeightEqOneAddRoot.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ConstGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.dupNamespace false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
structure Host (E : Type) [Field E] [NumberField E] [IsCMField E] where
  d : ℕ
  d_mod : d % 16 = 7
  d_prime : d.Prime
  rt : 𝓞 E
  rt_sq : rt ^ 2 = -(d : 𝓞 E)
  w0 : 𝓞 E
  two_weight_eq_one_add_root : 2 * w0 = 1 + rt
  bar : 𝓞 E ≃+* 𝓞 E
  bar_eq : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)
  unram : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)
  rt0 : ℂ
  sqrt_neg_disc_sq : rt0 ^ 2 = -(d : ℂ)
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
structure Datum (H : Host E) where
  La : Type
  [acg : AddCommGroup La]
  [mod : Module (𝓞 E) La]
  fin : Module.Finite (𝓞 E) La
  proj : Module.Projective (𝓞 E) La
  EF : LinearMap.BilinForm ℤ La
  alt : ∀ x, EF x x = 0
  unimod : Function.Bijective EF
  adj : ∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y)
  p : ℕ
  q : ℕ
  rank : Module.finrank (𝓞 E) La = p + q
  dom : ∃ J : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La, (∀ x, J (J x) = -x) ∧
    (∀ x y, EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < EF.baseChange ℝ (J x) x) ∧
    ∀ (a : 𝓞 E) (A : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La) (t : ℂ), (∀ x : La, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) →
      t = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
        ((p : ℂ) * τ (a : E) + (q : ℂ) * starRingEnd ℂ (τ (a : E))) →
      J ∘ₗ A = A ∘ₗ J ∧ LinearMap.trace ℝ _ A = 2 * t.re ∧ LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * t.im
attribute [instance] Datum.acg Datum.mod
structure Level (H : Host E) where
  M : ℕ
  three_le : 3 ≤ M
  odd : Odd M
  Mb : Ideal (𝓞 E)
  fromK : Mb = Ideal.span {a | a ∈ Mb ∧ a ∈ Algebra.adjoin ℤ {H.w0}}
  prod : Mb * Mb.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(M : 𝓞 E)}
  coprime : Mb ⊔ Mb.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤
  A : ℕ
  A_pos : 0 < A
def Level.M' {H : Host E} (l : Level H) : ℕ := Nat.lcm l.M l.A
def Level.Dvd {H : Host E} (l l₂ : Level H) : Prop := l.M ∣ l₂.M ∧ l₂.Mb ≤ l.Mb ∧ l.A ∣ l₂.A
def Level.GoodAt {H : Host E} (l : Level H) (p : ℕ) : Prop := 3 ≤ l.M / p ^ l.M.factorization p
variable {S : Scheme.{0}}
structure SAB (H : Host E) (S : Scheme.{0}) where
  G : Over S
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiAbelian G
  act : OAct (𝓞 E) G
  PP : RigLB G
  cub : CubicalStr G PP
  sym : PP.IsSymmetric
  adj : ∀ a, LBIso (cubeLB G ![fst G G ≫ act.act a, snd G G] PP.L) (cubeLB G ![fst G G, snd G G ≫ act.act (H.bar a)] PP.L)
  prim : LBIso PP.L (cubeLB G ![𝟙 G, act.act H.w0] PP.L)
attribute [instance] SAB.grp SAB.comm
structure SABMap {H : Host E} {S' : Scheme.{0}} (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) where
  cm : CubeMap t'.G t.G
  cart : IsGrpPullback t'.G t.G f cm.F
  base : cm.e = f
  act : ∀ a, (t'.act.act a).left ≫ cm.F = cm.F ≫ (t.act.act a).left
  lin : cm.IsPullCubical t'.cub t.cub
abbrev SABMap.φ {H : Host E} {S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) :
    t'.G.left ⟶ t.G.left := m.cm.F
def unitOn {R : Type} [CommRing R] (u : Rˣ) : (Γ(Sp R, ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom u
section Lie
variable {k : Type} [Field k]
abbrev epsPt (t : Sp k ⟶ S) : Over S := Over.mk (spMap (algebraMap k (DualNumber k)) ≫ t)
def epsScale (c : k) : DualNumber k →+* DualNumber k :=
  (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom
def IsLieEigen {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k)
    (v : epsPt t ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk t ⟶ G).left ∧
    ∀ a, (v ≫ act.act a).left = spMap (epsScale (τ a)) ≫ v.left
def LieMult {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k)
    (n : ℕ) : Prop :=
  ∃ v : Fin n → (epsPt t ⟶ G), (∀ i, IsLieEigen act t τ (v i)) ∧ ∀ w, IsLieEigen act t τ w →
    ∃! c : Fin n → k, ∃ u : Fin n → (epsPt t ⟶ G),
      (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod
def DetCond {H : Host E} (D : Datum H) {G : Over S} [GrpObj G] (act : OAct (𝓞 E) G) (t : Sp k ⟶ S) (ρ : k) : Prop :=
  ∀ τ : 𝓞 E →+* k, (τ H.rt = ρ → LieMult act t τ D.p) ∧ (τ H.rt ≠ ρ → LieMult act t τ D.q)
end Lie
structure Base {H : Host E} (l : Level H) (B : Type) [CommRing B] where
  unit : ∀ n : ℕ, 0 < n → IsUnit (n : B)
  ρ : B
  ρ_sq : ρ ^ 2 = -(H.d : B)
  ζ : B
  ζ_prim : IsPrimitiveRoot ζ l.A
structure TateIso {H : Host E} (D : Datum H) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q)
    (e : ℕ → Q → Q → kˣ → Prop) where
  ζ : ℕ → kˣ
  ζ_prim : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n
  ζ_pow : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n
  ev : ℕ → D.La → Q
  add : ∀ n a b, ev n (a + b) = ev n a * ev n b
  lin : ∀ n (c : 𝓞 E) a, ev n (c • a) = act c (ev n a)
  ker : ∀ n, 0 < n → ∀ a, ev n a = 1 ↔ ∃ b, a = n • b
  onto : ∀ n, 0 < n → ∀ x, x ^ n = 1 ↔ ∃ a, ev n a = x
  tower : ∀ n m, 0 < n → 0 < m → ∀ a, ev (n * m) a ^ m = ev n a
  isom : ∀ n, 0 < n → ∀ a b, e n (ev n a) (ev n b) (ζ n ^ D.EF a b)
structure Obj {H : Host E} (D : Datum H) (l : Level H) {B : Type} [CommRing B] (b : Base l B) (s : S ⟶ Sp B) where
  t : SAB H S
  proper : IsProper t.G.hom
  ample : Out.RelAmple t.G t.PP.L
  ktriv : Out.KTriv t.G t.PP.L
  eta : D.La → (𝟙_ (Over S) ⟶ t.G)
  eta_add : ∀ a c, eta (a + c) = eta a * eta c
  eta_ker : ∀ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La), eta a = 1
  etaA : D.La → (𝟙_ (Over S) ⟶ t.G)
  etaA_add : ∀ a c, etaA (a + c) = etaA a * etaA c
  etaA_ker : ∀ a, etaA (l.A • a) = 1
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k), x ≫ s = spMap β →
    DetCond D t.act x (β b.ρ) ∧
    ∃ I : TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)),
      (I.ζ l.A : k) = β b.ζ ∧ (∀ a, toUnit _ ≫ etaA a = I.ev l.A a) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ eta a = I.ev l.M a
structure ObjMap {H : Host E} {D : Datum H} {l : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {S' : Scheme.{0}} {s' : S' ⟶ Sp B'} {s : S ⟶ Sp B} (o' : Obj D l b' s') (o : Obj D l b s)
    (f : S' ⟶ S) extends SABMap o'.t o.t f where
  eta : ∀ a, (o'.eta a).left ≫ cm.F = f ≫ (o.eta a).left
  etaA : ∀ a, (o'.etaA a).left ≫ cm.F = f ≫ (o.etaA a).left
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


