-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TateUniformizationInput
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_TateUniformizationInput
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T11:37:49.158115+00:00
-- url     : https://prove2.me/theorems/a9d63477-0f98-4f20-8a53-f051cd7912cd
-- title:
--   Tate Uniformization Input
-- statement:
--   Definitions and structural lemmas for Tate Uniformization Input, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/TateUniformizationInput.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_TorusGraphMaps
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps
section Points
variable {R : Type} [CommRing R] [IsDomain R] {P : DegPre R}
variable {F : Type} [Field F] [Algebra (FractionRing R) F]
def QkZero {k : ℕ} (p : QkPt P F k) : Prop :=
  ∃ z : P.X, p.y = k • z ∧ GtPtF.IsIota z p.g
def QkTower (m : ℕ) {k n : ℕ} (p : QkPt P F k) (p' : QkPt P F n) : Prop :=
  k = n * m ∧ ∃ q : QkPt P F n, q.y = p.y ∧ GtPtF.IsNsmul m p.g q.g ∧ QkPt.Equiv P F q p'
end Points
section Lie
def ringActToOAct {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {O : Type} [CommRing O]
    (ra : RingAct A O) : Geo.Tor.OAct O A where
  act := ra.act
  hom := ra.hom
  one := ra.map_one
  mul := fun a b => by rw [_root_.mul_comm, ra.map_mul]
  add := fun a b => ra.map_add a b
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def torusLieEigen (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] (k : Type) [Field k]
    (τ : 𝓞 E →+* k) : Submodule k (X →+ k) where
  carrier := {v | ∀ (a : 𝓞 E) (χ : X), v (H.bar a • χ) = τ a * v χ}
  add_mem' := fun {v w} hv hw a χ => by
    simp only [AddMonoidHom.add_apply, hv a χ, hw a χ, mul_add]
  zero_mem' := fun a χ => by simp
  smul_mem' := fun c v hv a χ => by
    simp only [AddMonoidHom.smul_apply, hv a χ, smul_eq_mul]
    ring
instance torusLieEigen_finite (H : Host E) (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] [Module (𝓞 E) X] (k : Type) [Field k] (τ : 𝓞 E →+* k) :
    Module.Finite k (torusLieEigen H X k τ) := by
  have : Module.Finite k (X →+ k) :=
    Module.Finite.equiv (addMonoidHomLequivInt (A := X) (B := k) k).symm
  infer_instance
variable {R : Type} [CommRing R] [IsDomain R]
def GtLieMult (H : Host E) {P : DegPre R} [Module (𝓞 E) P.X]
    (ac : letI := hostStar H; P.OAct (𝓞 E)) (k : Type) [Field k] [Algebra (FractionRing R) k]
    (τ : 𝓞 E →+* k) (n : ℕ) : Prop :=
  letI := hostStar H
  ∃ nB : ℕ, LieMult (ringActToOAct ac.onB.toRingAct) (DegPre.jFR (R := R) k) τ nB ∧
    nB + Module.finrank k (torusLieEigen H P.X k τ) = n
def GtDetCond {H : Host E} (D : Datum H) {P : DegPre R} [Module (𝓞 E) P.X]
    (ac : letI := hostStar H; P.OAct (𝓞 E)) (k : Type) [Field k] [Algebra (FractionRing R) k]
    (ρ : k) : Prop :=
  ∀ τ : 𝓞 E →+* k, (τ H.rt = ρ → GtLieMult H ac k τ D.p) ∧ (τ H.rt ≠ ρ → GtLieMult H ac k τ D.q)
end Lie
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
section Levels
variable {R : Type} [CommRing R] [IsDomain R]
structure QTateIso (D : Datum H) {P : DegPre R} [Module (𝓞 E) P.X]
    (ac : letI := hostStar H; P.OAct (𝓞 E)) (k : Type) [Field k] [Algebra (FractionRing R) k] where
  ζ : ℕ+ → kˣ
  ζ_prim : ∀ n : ℕ+, IsPrimitiveRoot (ζ n) (n : ℕ)
  ζ_pow : ∀ n m : ℕ+, ζ (n * m) ^ (m : ℕ) = ζ n
  ev : ∀ n : ℕ+, D.La → QkPt P k (n : ℕ)
  add : ∀ n a a', QkAdd (ev n a) (ev n a') (ev n (a + a'))
  lin : ∀ n (x : 𝓞 E) a, (letI := hostStar H; QkSmul ac x (ev n a) (ev n (x • a)))
  ker : ∀ n a, QkZero (ev n a) ↔ ∃ a', a = (n : ℕ) • a'
  onto : ∀ (n : ℕ+) (p : QkPt P k (n : ℕ)), ∃ a, QkPt.Equiv P k (ev n a) p
  tower : ∀ (n m : ℕ+) a, QkTower (m : ℕ) (ev (n * m) a) (ev n a)
  isom : ∀ (n : ℕ+) a a', WeilQkIs P k (n : ℕ) (ev n a) (ev n a') ((ζ n ^ D.EF a a' : kˣ) : k)
structure QLevel (D : Datum H) (l : Level H) {P : DegPre R} [Module (𝓞 E) P.X]
    (ac : letI := hostStar H; P.OAct (𝓞 E)) (k : Type) [Field k] [Algebra (FractionRing R) k] where
  eta : D.La → QkPt P k l.M
  eta_add : ∀ a a', QkAdd (eta a) (eta a') (eta (a + a'))
  eta_lin : ∀ (x : 𝓞 E) a, (letI := hostStar H; QkSmul ac x (eta a) (eta (x • a)))
  eta_ker : ∀ a, QkZero (eta a) ↔ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)
  eta_onto : ∀ p : QkPt P k l.M,
    (∀ x ∈ l.Mb, ∃ q : QkPt P k l.M, (letI := hostStar H; QkSmul ac x p q) ∧ QkZero q) →
    ∃ a, QkPt.Equiv P k (eta a) p
  etaA : D.La → QkPt P k l.A
  etaA_add : ∀ a a', QkAdd (etaA a) (etaA a') (etaA (a + a'))
  etaA_lin : ∀ (x : 𝓞 E) a, (letI := hostStar H; QkSmul ac x (etaA a) (etaA (x • a)))
  etaA_ker : ∀ a, QkZero (etaA a) ↔ ∃ a', a = l.A • a'
  etaA_onto : ∀ p : QkPt P k l.A, ∃ a, QkPt.Equiv P k (etaA a) p
abbrev levelM (l : Level H) : ℕ+ := ⟨l.M, lt_of_lt_of_le (by norm_num) l.three_le⟩
abbrev levelA (l : Level H) : ℕ+ := ⟨l.A, l.A_pos⟩
def QTateIso.Induces {D : Datum H} {l : Level H} {P : DegPre R} [Module (𝓞 E) P.X]
    {ac : letI := hostStar H; P.OAct (𝓞 E)} {k k' : Type} [Field k] [Algebra (FractionRing R) k]
    [Field k'] [Algebra (FractionRing R) k'] (I : QTateIso D ac k') (lv : QLevel D l ac k)
    (σ : k →ₐ[FractionRing R] k') (z : k') : Prop :=
  (I.ζ (levelA l) : k') = z ∧
    (∀ a, QkMap (k := l.A) σ (lv.etaA a) (I.ev (levelA l) a)) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      QkMap (k := l.M) σ (lv.eta a) (I.ev (levelM l) a)
end Levels
section Base
variable {l : Level H} (c : Coeff l)
def coeffRt : c.F := IntermediateField.inclusion c.le (baseKA l).ρ
def coeffZeta : c.F := IntermediateField.inclusion c.le (baseKA l).ζ
variable {c}
def IsFracImage {O : Type} [CommRing O] (β : O →+* c.F) : Prop :=
  ∀ x : c.F, ∃ a s : O, β s ≠ 0 ∧ x * β s = β a
end Base
structure ArcInput (D : Datum H) {l : Level H} (c : Coeff l) {O : Type} [CommRing O]
    (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') where

  frac : IsFracImage β

  gam : c.F →+* FractionRing O'
  gam_over : ∀ x : O, gam (β x) = algebraMap O' (FractionRing O') (b x)

  P : DegPre O'
  psi_even : P.PsiEven
  tau_bimult : P.TauBimult
  [mod : Module (𝓞 E) P.X]

  ac : letI := hostStar H; P.OAct (𝓞 E)
  nontriv : Nontrivial P.X
  psi_gen : ∀ y : P.X, PsiGenOn P y Set.univ
  through : PsiThroughHost H ac

  be : LinearMap.BilinForm ℤ P.X
  be_symm : ∀ y z, be y z = be z y
  be_pos : ∀ y, y ≠ 0 → 0 < be y y
  be_adj : ∀ (a : 𝓞 E) y z, be (a • y) z = be y (H.bar a • z)
  be_dvd : ∀ y z, (2 * l.M' : ℤ) ∣ be y z

  lev : QLevel D l ac (FractionRing O')
  det : GtDetCond D ac (AlgebraicClosure (FractionRing O'))
    (algebraMap (FractionRing O') _ (gam (coeffRt c)))
  induced : ∃ I : QTateIso D ac (AlgebraicClosure (FractionRing O')),
    I.Induces lev (Algebra.ofId (FractionRing O') _)
      (algebraMap (FractionRing O') _ (gam (coeffZeta c)))
attribute [instance] ArcInput.mod
namespace ArcInput
variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
end ArcInput
end GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput


