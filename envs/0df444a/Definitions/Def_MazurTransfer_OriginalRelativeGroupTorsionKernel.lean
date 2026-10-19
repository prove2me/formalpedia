-- Prove2me | Definitions.Def_MazurTransfer_OriginalRelativeGroupTorsionKernel
-- name    : MazurTransfer_OriginalRelativeGroupTorsionKernel
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T09:50:52.263269+00:00
-- url     : https://prove2.me/theorems/f948295d-7195-4fa7-b810-7a21ed7622c4
-- title:
--   The checked original relative-group torsion and scheme-kernel constructors
-- statement:
--   Let $L$ be a relative group law on a scheme $X$ over a commutative ring $R$. The original constructors define natural-number multiplication on every relative point group, its torsion-point predicate and torsion subset, the multiplication scheme morphism, and the scheme-theoretic kernel $$\ker([m])=X\mathbin{\times}_{X}\operatorname{Spec}R,$$ where the two maps are the specified multiplication morphism and the relative identity section. The original naturality and identity formulas are retained. This module provides the same original declarations through their checked normalized source for use in proper valuation-ring torsion specialization.
-- source:
--   Complete original official Anthropic FLT Def_GoodReductionJacobian_RelativeGroupLawKernel source at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0. Reuses the already checked normalized source byte-for-byte: all nineteen original declaration bodies and seven constructor values are retained; tooling proof-strengthening options from the upstream packaging are omitted in this previously checked source. Nineteen closed types and seven data/constructor values are kernel-compared. Existing native, strict and complete frontend checks are retained without rebuilding any original proof. Design boundary: an alternative public module provider for the same canonical original kernel declarations; a consumer uses one provider path. Named downstream consumer: public proper valuation torsion specialization interoperability recovery.

/- Complete official Anthropic FLT mathematical source, Apache-2.0, pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Routine tooling aliases expanded; proof options and search metadata omitted. Design boundary: reduction kernel for invertible-order relative torsion. Named downstream consumer: actual order-13 rational Picard specialization. -/
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Mathlib.AlgebraicGeometry.Pullbacks

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian
namespace RelativeGroupLaw

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

def nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) : SchemeHomOver t f :=
  Nat.rec (G.one t) (fun _ ih => G.mul t ih x) n

@[simp]
theorem nsmul_zero (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.nsmul t 0 x = G.one t :=
  rfl

@[simp]
theorem nsmul_succ (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    G.nsmul t (n + 1) x = G.mul t (G.nsmul t n x) x :=
  rfl

theorem nsmul_one_apply (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.nsmul t 1 x = x := by
  show G.mul t (G.one t) x = x
  exact G.one_mul t x

theorem nsmul_unit (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    G.nsmul t n (G.one t) = G.one t := by
  induction n with
  | zero => rfl
  | succ n ih => rw [nsmul_succ, ih, G.mul_one]

theorem nsmul_natural (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (G.nsmul t n x) = G.nsmul t' n (schemeHomOverComp ψ hψ x) := by
  induction n with
  | zero =>
      show schemeHomOverComp ψ hψ (G.one t) = G.one t'
      exact G.one_natural t t' ψ hψ
  | succ n ih =>
      calc schemeHomOverComp ψ hψ (G.nsmul t (n + 1) x)
          = schemeHomOverComp ψ hψ (G.mul t (G.nsmul t n x) x) := rfl
        _ = G.mul t' (schemeHomOverComp ψ hψ (G.nsmul t n x)) (schemeHomOverComp ψ hψ x) :=
            G.mul_natural t t' ψ hψ _ _
        _ = G.mul t' (G.nsmul t' n (schemeHomOverComp ψ hψ x)) (schemeHomOverComp ψ hψ x) := by
            rw [ih]
        _ = G.nsmul t' (n + 1) (schemeHomOverComp ψ hψ x) := rfl

def IsTorsionPoint (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) : Prop :=
  G.nsmul t n x = G.one t

theorem isTorsionPoint_def (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    G.IsTorsionPoint t n x ↔ G.nsmul t n x = G.one t :=
  Iff.rfl

def torsionSubset (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) : Set (SchemeHomOver t f) :=
  {x | G.IsTorsionPoint t n x}

@[simp]
theorem mem_torsionSubset (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    x ∈ G.torsionSubset t n ↔ G.IsTorsionPoint t n x :=
  Iff.rfl

theorem isTorsionPoint_unit (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    G.IsTorsionPoint t n (G.one t) :=
  G.nsmul_unit t n

theorem isTorsionPoint_one_iff (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.IsTorsionPoint t 1 x ↔ x = G.one t := by
  show G.nsmul t 1 x = G.one t ↔ x = G.one t
  rw [G.nsmul_one_apply]

theorem isTorsionPoint_schemeHomOverComp (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) {x : SchemeHomOver t f}
    (hx : G.IsTorsionPoint t n x) :
    G.IsTorsionPoint t' n (schemeHomOverComp ψ hψ x) := by
  show G.nsmul t' n (schemeHomOverComp ψ hψ x) = G.one t'
  rw [← G.nsmul_natural t t' ψ hψ n x, hx]
  exact G.one_natural t t' ψ hψ

theorem mapsTo_torsionSubset_schemeHomOverComp (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) :
    Set.MapsTo (schemeHomOverComp ψ hψ) (G.torsionSubset t n) (G.torsionSubset t' n) :=
  fun _ hx => G.isTorsionPoint_schemeHomOverComp t t' ψ hψ n hx

abbrev idPoint : SchemeHomOver f f :=
  ⟨𝟙 A, Category.id_comp f⟩

def schemeNsmul (G : RelativeGroupLaw R f) (n : ℕ) : A ⟶ A :=
  (G.nsmul f n idPoint).1

theorem schemeNsmul_over (G : RelativeGroupLaw R f) (n : ℕ) :
    G.schemeNsmul n ≫ f = f :=
  (G.nsmul f n idPoint).2

abbrev schemeKer (G : RelativeGroupLaw R f) (n : ℕ) : Scheme.{u} :=
  pullback (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1

abbrev schemeKerStr (G : RelativeGroupLaw R f) (n : ℕ) :
    G.schemeKer n ⟶ Spec (CommRingCat.of R) :=
  pullback.snd (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1

end RelativeGroupLaw

end GoodReductionJacobian

end

#print axioms GoodReductionJacobian.RelativeGroupLaw.nsmul_natural


