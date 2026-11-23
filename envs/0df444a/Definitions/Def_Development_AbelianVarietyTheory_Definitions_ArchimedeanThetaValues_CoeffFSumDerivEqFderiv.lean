-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
-- name    : Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:49:23.892324+00:00
-- url     : https://prove2.me/theorems/5d8e6626-11c2-4e1b-8a8d-bc5a61a50c8d
-- title:
--   Coeff FSum Deriv Eq Fderiv
-- statement:
--   Definitions and structural lemmas for Coeff FSum Deriv Eq Fderiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/CoeffFSumDerivEqFderiv.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
def perFactor (w : ℂ) (la : A.La) (v : A.V) : ℂ :=
  A.ah la.l (v.2 + A.ct la.y) * (A.psi la.y * eTwoPi (v.1 la.y) * eTwoPi (w * A.q la.y))⁻¹
def FSumDeriv (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (v z₀ : A.V) : LaurentSeries ℂ :=
  HahnSeries.ofSuppBddBelow (fun n => ∑ μ ∈ A.level j α n, fderiv ℂ (A.term j α th μ) v z₀)
    ⟨-A.be α α, fun n hn => by
      by_contra h
      exact hn (by simp only [A.level_eq_empty (not_le.1 h), Finset.sum_empty])⟩
def FSumShift (k : ℕ) [NeZero k] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (la : A.La) (z : A.V) : LaurentSeries ℂ :=
  HahnSeries.ofSuppBddBelow
    (fun n => ∑ μ ∈ A.level k (α + la.y) (n - A.be la.y α / k), A.term k α th μ (z + (k : ℂ)⁻¹ • A.P0 la))
    ⟨-A.be (α + la.y) (α + la.y) + A.be la.y α / k, fun n hn => by
      by_contra h
      exact hn (by simp only [A.level_eq_empty (j := k) (α := α + la.y) (n := n - A.be la.y α / k) (by omega),
        Finset.sum_empty])⟩
example (τ₀ w : ℂ) (v : (tate τ₀).V) :
    (tate τ₀).perFactor w (La.mk (A := tate τ₀) (1 : ℤ) 0 0) v = eTwoPi (-((τ₀ + 2 * w) / 2 + v.1 (1 : ℤ))) := by
  have h1 : (tate τ₀).ah 0 (v.2 + (tate τ₀).ct (1 : ℤ)) = 1 := by simp [ah]
  change (tate τ₀).ah 0 (v.2 + (tate τ₀).ct (1 : ℤ)) *
    ((psiInt τ₀ 1 : ℂ) * eTwoPi (v.1 (1 : ℤ)) * eTwoPi (w * ((1 : ℤ) : ℂ)))⁻¹ = _
  rw [h1, one_mul, coe_psiInt, ← e_add, ← e_add, eTwoPi, eTwoPi, ← Complex.exp_neg]
  congr 1; push_cast; ring
end AnArc
section Along
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
def IsDerivAtZero {X : Scheme.{0}} (e : V → (Sp ℂ ⟶ X)) (w : V) (v : Sp (DualNumber ℂ) ⟶ X) : Prop :=
  spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 ∧
    ∀ (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)),
      TrivSqZeroExt.snd (show DualNumber ℂ from
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE U ⊤ h).hom f)) =
        fderiv ℂ (fun z => valAt' (e z) U f) 0 w
variable {S : Scheme.{0}} {G : Over S} [GrpObj G]
def IsRigFrame (L : RigLB G) (y : Sp ℂ ⟶ S) (e : V → (Sp ℂ ⟶ G.left)) (fr : L.L.ι → V → ℂ) : Prop :=
  (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.L.U j}) ∧ (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.L.U j → fr j z ≠ 0) ∧
    (∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L.L.U j ⊓ L.L.U j') →
      fr j z = valAt' (e z) (L.L.U j ⊓ L.L.U j') (L.L.g j j').val * fr j' z) ∧
    ∀ j, ⊤ ≤ e 0 ⁻¹ᵁ L.L.U j → fr j 0 = valAt' y ((L.L.pull (eSec G)).U (fun _ => j)) (L.rig.s (fun _ => j)).val
def IsAlgebraicIn (L : RigLB G) (y : Sp ℂ ⟶ S) (e : V → (Sp ℂ ⟶ G.left)) (θ : V → ℂ) (fr : L.L.ι → V → ℂ) : Prop :=
  ∃ s : (L.L.pull (pullback.fst G.hom y)).Sec, ∀ j z (x : Sp ℂ ⟶ pullback G.hom y),
    x ≫ pullback.fst _ _ = e z → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ e z ⁻¹ᵁ L.L.U j →
    valAt' x ((L.L.pull (pullback.fst G.hom y)).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z
variable {V' : Type} [NormedAddCommGroup V'] [NormedSpace ℂ V']
end Along
end GlobalTheory


