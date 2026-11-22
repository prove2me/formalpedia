-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:35:06.381817+00:00
-- url     : https://prove2.me/theorems/58d62d9a-1228-4b3c-85cc-541ad89ba274
-- title:
--   Hecke Ker
-- statement:
--   Definitions and structural lemmas for Hecke Ker, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/HeckeKer.lean

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
def N1ab : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H),
    1 ≤ D.p + D.q → Nonempty (Moduli D l)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
def Datum.ModN (D : Datum H) (n : ℕ) (x : D.La) : Prop := ∃ b, x = n • b
structure Sim (D : Datum H) where
  f : ℕ → D.La →ₗ[𝓞 E] D.La
  ν : ℕ → ℤ
  tower : ∀ n m, 0 < n → 0 < m → ∀ a, D.ModN n (f (n * m) a - f n a)
  inv : ∀ n, 0 < n → ∃ g : D.La →ₗ[𝓞 E] D.La, ∀ a, D.ModN n (g (f n a) - a) ∧ D.ModN n (f n (g a) - a)
  mult : ∀ n : ℕ, 0 < n → ∀ a b, (n : ℤ) ∣ D.EF (f n a) (f n b) - ν n * D.EF a b
def Sim.InGam (g : Sim D) (l l₂ : Level H) : Prop :=
  (l₂.A : ℤ) ∣ g.ν l₂.A - 1 ∧ (∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧
    ∀ a, D.ModN l.A (g.f l.A a - a)
def Sim.TrivAt (g : Sim D) (l₂ : Level H) : Prop :=
  (∀ a, g.f l₂.M a - a ∈ l₂.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧ ∀ a, D.ModN l₂.A (g.f l₂.A a - a)
def Moduli.LevAut {l : Level H} (Xo : Moduli D l) (g : Sim D) (ρ : Xo.X ≅ Xo.X) : Prop :=
  ρ.hom ≫ Xo.s = Xo.s ∧ ∃ ν : SABMap Xo.univ.t Xo.univ.t ρ.hom,
    (∀ a, (Xo.univ.eta (g.f l.M a)).left ≫ ν.φ = ρ.hom ≫ (Xo.univ.eta a).left) ∧
    ∀ a, (Xo.univ.etaA (g.f l.A a)).left ≫ ν.φ = ρ.hom ≫ (Xo.univ.etaA a).left
def ToroidalLevelCompatibility : Prop :=
  ∀ (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), l.Dvd l₂ →
    ∃ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r),
      (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧
      (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧
      (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) ∧
      (∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r) ∧
      ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F), ∃ rF : Xo₂.XF c₂ ⟶ Xo.XF c,
        rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r ∧
        rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom ∧
        IsFinite rF ∧ Etale rF ∧ Surjective rF ∧
        ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Xo₂.XF c₂), y ≫ rF = y' ≫ rF →
          (∃ (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ ∧ Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r ∧
            y' ≫ pullback.fst _ _ = y ≫ pullback.fst _ _ ≫ ρ.hom) ∧
          ∀ (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ → Xo₂.LevAut g ρ →
            y ≫ pullback.fst _ _ ≫ ρ.hom = y ≫ pullback.fst _ _ → g.TrivAt l₂
variable {S : Scheme.{0}}
def SAB.tors (t : SAB H S) (T : Over S) (I : Ideal (𝓞 E)) : Set (T ⟶ t.G) :=
  {x | ∀ a ∈ I, x ≫ t.act.act a = 1}
def SAB.HeckeKer (t : SAB H S) (T : Over S) (D : Datum H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (C : Subgroup (T ⟶ t.G)) :
    Prop :=
  (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) ∧
  (∀ J : Ideal (𝓞 E), J * 𝔓 = Ideal.span {(p : 𝓞 E)} → t.tors T J ⊆ C) ∧
  (C : Set (T ⟶ t.G)) ⊆ t.tors T (Ideal.span {(p : 𝓞 E)} * 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E)) ∧
  (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p : ℤ) ^ 2) x y 1) ∧
  Nat.card C = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) ∧
  Nat.card (t.tors T (Ideal.span {(p : 𝓞 E)})) =
    Nat.card ((C : Set (T ⟶ t.G)) ∩ t.tors T (Ideal.span {(p : 𝓞 E)}) : Set (T ⟶ t.G)) * Ideal.absNorm 𝔓 ^ i
def fibPt {X : Scheme.{0}} (G : Over X) {k : Type} [Field k] {y : Sp k ⟶ X} (x : Over.mk y ⟶ G) :
    Sp k ⟶ pullback G.hom y :=
  pullback.lift x.left (𝟙 _) (by simp [Over.w x])
def ToroidalHeckeCompatibility : Prop :=
  ∀ (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), 𝔓.IsMaximal →
    𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → p.Prime → (p : 𝓞 E) ∈ 𝔓 → ¬ p ∣ l.M' →
    ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)),
      Xo.univ.t.HeckeKer (Over.mk y) D 𝔓 p i C →
      ∃! y'' : Sp k ⟶ Xo.X, y'' ≫ Xo.s = y ≫ Xo.s ∧
        ∃ (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y'')
          (ψp : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y'' ⟶ Xo.univ.t.G)),
          ψ ≫ pullback.snd _ _ = pullback.snd _ _ ∧ (∀ x, fibPt _ x ≫ ψ = fibPt _ (ψp x)) ∧
          (∀ a x, ψp (x ≫ Xo.univ.t.act.act a) = ψp x ≫ Xo.univ.t.act.act a) ∧
          Function.Surjective ψp ∧ ψp.ker = C ∧
          (∀ (n : ℕ) (x x' : Over.mk y ⟶ Xo.univ.t.G) (c : kˣ), n.Coprime p →
            Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n x x' (unitOn c) →
            Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n (ψp x) (ψp x') (unitOn (c ^ (p ^ 2)))) ∧
          ∀ p' : ℕ, p * p' ≡ 1 [MOD l.M'] → ∀ a,
            ψp (toUnit _ ≫ Xo.univ.eta (p' • a)) = toUnit _ ≫ Xo.univ.eta a ∧
            ψp (toUnit _ ≫ Xo.univ.etaA (p' • a)) = toUnit _ ≫ Xo.univ.etaA a
def N1 : Prop :=
  N1ab ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
    1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) ∧ ToroidalHeckeCompatibility (H := H) (D := D)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


