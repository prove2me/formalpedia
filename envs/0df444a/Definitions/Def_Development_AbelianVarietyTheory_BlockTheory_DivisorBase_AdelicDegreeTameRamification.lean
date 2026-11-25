-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_AdelicDegreeTameRamification
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_AdelicDegreeTameRamification
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:29:45.480173+00:00
-- url     : https://prove2.me/theorems/49376c60-96a4-4ac3-b994-6ed4e94ac0a5
-- title:
--   Adelic Degree Tame Ramification
-- statement:
--   Definitions and structural lemmas for Adelic Degree Tame Ramification, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/AdelicDegreeTameRamification.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
abbrev quadField (H : Host E) : IntermediateField ℚ E := IntermediateField.adjoin ℚ {((H.rt : 𝓞 E) : E)}
instance (H : Host E) : Fact H.d.Prime := ⟨H.d_prime⟩
def quadChar (H : Host E) : DirichletCharacter ℂ H.d :=
  (quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ)
def logOmega (H : Host E) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.pi / (rootDiscr E / 2)) -
    (deriv (quadChar H).LFunction 1 / (quadChar H).LFunction 1).re
def TameAtRamified (H : Host E) : Prop :=
  ∀ (l : ℕ) (w : Ideal (𝓞 E)), l.Prime → (l : ℤ) ∣ discr E → w.IsMaximal → (l : 𝓞 E) ∈ w →
    w.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ w ∧
    (l ≠ H.d → ∃ a ∈ Algebra.adjoin ℤ {H.w0}, a ∈ w ∧ H.bar a ∉ w) ∧
    (l = H.d → (l : 𝓞 E) ∉ w ^ 3)
section Degree
variable (k : Type) [Field k] [NumberField k]
abbrev valRing (v : HeightOneSpectrum (𝓞 k)) : ValuationSubring k := (v.valuation k).valuationSubring
def AlmostUnit (a : HeightOneSpectrum (𝓞 k) → k) : Prop :=
  {v : HeightOneSpectrum (𝓞 k) | v.valuation k (a v) ≠ 1}.Finite
def adelicDeg (a : HeightOneSpectrum (𝓞 k) → k) (r : (k →+* ℂ) → ℝ) : ℝ :=
  (-(∑ σ : k →+* ℂ, Real.log (r σ) / 2) + ∑ᶠ v, Real.log (FinitePlace.mk v (a v))) / Module.finrank ℚ k
end Degree
section Lie
variable {H : Host E} {k : Type} [Field k] [NumberField k]
def IsEigenVec (t : SAB H (Sp k)) (χ : 𝓞 E → k) (w : epsR k ⟶ t.G) : Prop :=
  IsTangent w ∧ ∀ a, (w ≫ t.act.act a).left = spMap (epsScaleR (χ a)) ≫ w.left
def IsEigenBasis (t : SAB H (Sp k)) (χ : 𝓞 E → k) {n : ℕ} (x : Fin n → (epsR k ⟶ t.G)) : Prop :=
  (∀ i, IsEigenVec t χ (x i)) ∧ ∀ w, IsEigenVec t χ w → ∃! c : Fin n → k, IsLieComb c x w
def latticeCoords {A : Over (Sp k)} [GrpObj A] (V : ValuationSubring k) (G : Over (Sp V)) [GrpObj G]
    (φ : A.left ⟶ G.left) {n : ℕ} (x : Fin n → (epsR k ⟶ A)) : Set (Fin n → k) :=
  {c | ∃ (w : epsR k ⟶ A) (u : epsR V ⟶ G), IsLieComb c x w ∧ IsTangent u ∧
    w.left ≫ φ = spMap (Chart.dualMapR (algebraMap V k)) ≫ u.left}
def IsLocalGen (t : SAB H (Sp k)) {n : ℕ} (x : Fin n → (epsR k ⟶ t.G)) (v : HeightOneSpectrum (𝓞 k)) (a : k) : Prop :=
  ∃ (G : Over (Sp (valRing k v))) (_ : GrpObj G) (φ : t.G.left ⟶ G.left) (M : Matrix (Fin n) (Fin n) k),
    IsSemiAbelian G ∧ IsGrpPullback t.G G (spMap (algebraMap (valRing k v) k)) φ ∧
    (∀ c, c ∈ latticeCoords (valRing k v) G φ x ↔
      ∃ b : Fin n → valRing k v, c = Matrix.vecMul (fun i => (b i : k)) M) ∧
    a = M.det ∧ a ≠ 0
def IsArchNormSq (t : SAB H (Sp k)) {n : ℕ} (x : Fin n → (epsR k ⟶ t.G)) (σ : k →+* ℂ) (r : ℝ) : Prop :=
  ∃ (t' : SAB H (Sp ℂ)) (m : SABMap t' t (spMap σ)) (g : ℕ) (u : HolUnif t'.G t'.PP.L g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (α : u.Λ → ℂ) (x' : Fin n → (epsR ℂ ⟶ t'.G)) (W : Fin n → Fin g → ℂ),
    u.IsAH Hm α ∧ (∀ i, (x' i).left ≫ m.φ = spMap (Chart.dualMapR σ) ≫ (x i).left) ∧ (∀ i, u.IsDiff (W i) (x' i)) ∧
    (r : ℂ) = (Matrix.of fun i j => (Real.pi : ℂ) * (W i ⬝ᵥ Hm.mulVec (star (W j)))).det ∧ 0 < r
def IsFlatFactor (H : Host E) (χ : 𝓞 E → k) (v : HeightOneSpectrum (𝓞 k)) (b : k) : Prop :=
  b ≠ 0 ∧
    Submodule.span (valRing k v) (χ '' (differentIdeal (𝓞 (quadField H)) (𝓞 E) : Set (𝓞 E))) =
      Submodule.span (valRing k v) ((fun a : 𝓞 (quadField H) => b * χ (algebraMap _ (𝓞 E) a)) ''
        (differentIdeal ℤ (𝓞 (quadField H)) : Set (𝓞 (quadField H))))
end Lie
def embVal {H : Host E} {l : Level H} (c : Coeff l) {k : Type} [Field k] (j : c.F →+* k) (τ : E →+* ℂ) (a : 𝓞 E) : k :=
  j ⟨τ (a : E), c.conj τ a⟩
def FlatDegreeStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), IsAbelianGalois ℚ E → TameAtRamified H →
  ∀ (D : Datum H) (l : Level H) (c : Coeff l) (k : Type) [Field k] [NumberField k] (j : c.F →+* k)
    (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom))
    (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 →
  ∀ (x : Fin D.p → (epsR k ⟶ o.t.G)) (x' : Fin D.q → (epsR k ⟶ o.t.G)),
    IsEigenBasis o.t (embVal c j τ) x → IsEigenBasis o.t (embVal c j (conjEmb τ)) x' →
  ∀ (a a' : HeightOneSpectrum (𝓞 k) → k) (r r' : (k →+* ℂ) → ℝ),
    (∀ v, IsLocalGen o.t x v (a v)) → (∀ v, IsLocalGen o.t x' v (a' v)) →
    (∀ σ, IsArchNormSq o.t x σ (r σ)) → (∀ σ, IsArchNormSq o.t x' σ (r' σ)) →
    AlmostUnit k a ∧ AlmostUnit k a' ∧
    adelicDeg k a r - adelicDeg k a' r' = ((D.p : ℝ) - D.q) / 2 * logOmega H ∧
    ∀ b : HeightOneSpectrum (𝓞 k) → k, (∀ v, IsFlatFactor H (embVal c j τ) v (b v)) →
      AlmostUnit k b ∧
      ∀ c₁ : ℝ, c₁ = -adelicDeg k (fun v => b v ^ D.q * a v / a' v) (fun σ => r σ / r' σ) →
        -c₁ = ((D.p : ℝ) - D.q) / 2 * logOmega H +
          D.q * (2 * Real.log (rootDiscr (quadField H)) - Real.log (rootDiscr E)) ∧
        |c₁ + ((D.p : ℝ) - D.q) * logOmega H / 2| ≤ D.q * Real.log (rootDiscr E)
example (k : Type) [Field k] [NumberField k] : adelicDeg k (fun _ => 1) (fun _ => 1) = 0 := by
  simp [adelicDeg]
example (k : Type) [Field k] [NumberField k] (s : ℝ) : adelicDeg k (fun _ => 1) (fun _ => s ^ 2) = -Real.log s := by
  have h : (Module.finrank ℚ k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  simp [adelicDeg, Embeddings.card]
  field_simp
end GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification


