-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Statements_PrincipalLattices_FiniteDimensionalBase
-- name    : Development_AbelianVarietyTheory_Statements_PrincipalLattices_FiniteDimensionalBase
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T13:36:53.453495+00:00
-- url     : https://prove2.me/theorems/32e896cd-dca5-4260-8a42-6066ee6a808b
-- title:
--   Finite Dimensional Base
-- statement:
--   Definitions and structural lemmas for Finite Dimensional Base, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/PrincipalLattices/FiniteDimensionalBase.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace GlobalTheory
namespace PureType
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def lat {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe) (ρ : ℂ) :
    Submodule (𝓞 E) D.La where
  carrier := {a | ∀ j, ty j (H.rt : E) ≠ ρ → Pe a j = 0}
  add_mem' {a b} ha hb j hj := by simp [ha j hj, hb j hj]
  zero_mem' j _ := by simp
  smul_mem' s a ha j hj := by rw [hP.1, ha j hj, mul_zero]
def IsThetaUnif {P : Out.PolAV (Sp ℂ)} (u : HolUnif P.A P.L P.g) : Prop :=
  ∃ (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ),
    u.IsAH Hm χ ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
    (∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧
      ∀ θ, u.IsThetaFn Hm χ n θ → ∃! s, u.IsFnPow n s θ) ∧
    (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef
def IsQuadLattice {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (d : ℕ) (c : ℂ) : Prop :=
  ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z = fun _ => c * ((m : ℂ) + n * ((1 + Complex.I * Real.sqrt d) / 2))
def IsHomFamily {D : Datum H} {R : Type} [CommRing R] (t : SAB H (Sp R)) (B : Over (Sp R)) [GrpObj B]
    (M : LB B.left) (v : epsR R ⟶ B) (L : Submodule (𝓞 E) D.La) (ρ : R) (S : Set L) (φ : L → (B ⟶ t.G)) : Prop :=
  (∀ a, IsMonHom (φ a)) ∧ (∀ a b, φ (a + b) = φ a * φ b) ∧
    (∀ (s : 𝓞 E) a, φ (s • a) = φ a ≫ t.act.act s) ∧
    (∀ a, IsLieComb ![ρ] ![v ≫ φ a] (v ≫ φ a ≫ t.act.act H.rt)) ∧
    ∀ a ∈ S, ∃ N : ℕ, 1 ≤ N ∧
      LBIso (lbPow (t.PP.L.pull (φ a).left) N) (lbPow M (N * (D.EF (H.w0 • (a : D.La)) a).natAbs))
def IsSpread {D : Datum H} {l : Level H} {Xo : Moduli D l} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) {Pe : (FU.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (FU.Di i) ty Pe) {k : IntermediateField ℚ ℂ} (hk : KA l ≤ k)
    (P₀ : Out.PolAV (Sp k)) (v₀ : epsR k ⟶ P₀.A)
    {PC : Out.PolAV (Sp ℂ)} (ψ : PC.A.left ⟶ P₀.A.left) (u₀ : HolUnif PC.A PC.L PC.g) (c : ℂ)
    (S : ∀ ε : ℤˣ, Set (lat hP (((ε : ℤ) : ℂ) * H.rt0)))
    (R : Type) [CommRing R] [Algebra k R] (j : R →ₐ[k] ℂ) : Prop :=
  ∃ (y : Sp R ⟶ Xo.X) (t : SAB H (Sp R)) (m : SABMap t Xo.univ.t y)
    (vR : epsR R ⟶ (Over.pullback (spMap (algebraMap k R))).obj P₀.A)
    (φ : ∀ ε : ℤˣ, lat hP (((ε : ℤ) : ℂ) * H.rt0) → ((Over.pullback (spMap (algebraMap k R))).obj P₀.A ⟶ t.G)),
    y ≫ Xo.s = spMap ((algebraMap k R).comp (IntermediateField.inclusion hk).toRingHom) ∧
    spMap j.toRingHom ≫ y = FU.u i Pe ∧
    IsTangent vR ∧
    vR.left ≫ pullback.fst P₀.A.hom (spMap (algebraMap k R)) = spMap (Chart.dualMapR (algebraMap k R)) ≫ v₀.left ∧
    ∀ ε : ℤˣ,
      IsHomFamily t ((Over.pullback (spMap (algebraMap k R))).obj P₀.A)
        (P₀.L.pull (pullback.fst P₀.A.hom (spMap (algebraMap k R)))) vR (lat hP (((ε : ℤ) : ℂ) * H.rt0))
        (((ε : ℤ) : R) * algebraMap k R (IntermediateField.inclusion hk (baseKA l).ρ)) (S ε) (φ ε) ∧
      ∀ (a : lat hP (((ε : ℤ) : ℂ) * H.rt0)) (z : ℂ) (x : Sp ℂ ⟶ pullback P₀.A.hom (spMap (algebraMap k R))),
        x ≫ pullback.fst _ _ = (u₀.ex fun _ => c * z).left ≫ ψ → x ≫ pullback.snd _ _ = spMap j.toRingHom →
        x ≫ (φ ε a).left ≫ m.φ = (FU.ex i Pe (z • Pe a)).left
end PureType
open PureType in

def CMPoint : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe)
    (k : IntermediateField ℚ ℂ) (hk : KA l ≤ k), FiniteDimensional ℚ k →
    ∀ (P₀ : Out.PolAV (Sp k)) (v₀ : epsR k ⟶ P₀.A), P₀.g = 1 → IsTangent v₀ →
    ∀ (PC : Out.PolAV (Sp ℂ)) (ψ : PC.A.left ⟶ P₀.A.left) (u₀ : HolUnif PC.A PC.L PC.g) (c : ℂ),
      PC.g = 1 → IsGrpPullback PC.A P₀.A (spMap (algebraMap k ℂ)) ψ → LBIso PC.L (P₀.L.pull ψ) →
      IsThetaUnif u₀ → c ≠ 0 → IsQuadLattice u₀.Λ H.d c →
    ∀ (S : ∀ ε : ℤˣ, Set (lat hP (((ε : ℤ) : ℂ) * H.rt0))), (∀ ε, (S ε).Finite) →
    ∀ R₀ : Subalgebra k ℂ, R₀.FG →
    ∃ R : Subalgebra k ℂ, R.FG ∧ R₀ ≤ R ∧ IsSpread FU i hP hk P₀ v₀ ψ u₀ c S R R.val
namespace PureType
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
section Linear
variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)
end Linear
end PureType
end GlobalTheory


