-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:00:39.079202+00:00
-- url     : https://prove2.me/theorems/ff209470-42dc-46af-99f6-3eda26cfe1c7
-- title:
--   Generic Point Section Hypotheses
-- statement:
--   Definitions and structural lemmas for Generic Point Section Hypotheses, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/GenericPointSectionHypotheses.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u v w
def FiniteSections.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (Q : LineBundle S x), x ≠ 0 →
    Module.Finite S Q.secs ∧
    (∀ c₁ : ℤ, ∃ (n : ℕ) (deg : Fin n → ℤ) (gen : Fin n → Ω),
      (∀ j, c₁ ≤ deg j ∧ gen j ∈ (Q.twist (twistSys S x (deg j))).secs) ∧
      ∀ c : ℤ, c₁ ≤ c → (Q.twist (twistSys S x c)).secs ≤ Submodule.span S {z | ∃ (j : Fin n)
        (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ (e : ℤ) + deg j = c ∧ z = aeval x f * gen j}) ∧
    ∀ (F : Type u) [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω] [IsFractionRing S F],
      Submodule.span F (Q.secs : Set Ω) = (Q.toSubSystem.extend F).secs
def FiniteTwists.Statement : Prop := TwistFinite.Statement.{u, w}
def Domination.Generic.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] [IsDomain S] (Ω : Type w) [Field Ω] [Algebra S Ω]
    (N N' : ℕ) (x : Fin (N + 1) → Ω) (x' : Fin (N' + 1) → Ω), x' ≠ 0 → IsDomination S x x' →
    (∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∀ b ∈ domRing S x x' i, ∃ s : S,
      algebraMap S Ω s ≠ 0 ∧ algebraMap S Ω s * b ∈ chartRing S x (singleChart hi)) →
    ∃ m : S, algebraMap S Ω m ≠ 0 ∧
      (∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∀ b ∈ domRing S x x' i,
        algebraMap S Ω m * b ∈ chartRing S x (singleChart hi)) ∧
      ∀ (L : LineBundle S x) (n : ℕ), ∀ z ∈ pullSecs x' (L.pow n),
        algebraMap S Ω m * z ∈ (L.pow n).secs
def Domination.Normal.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω]
    (N N' : ℕ) (x : Fin (N + 1) → Ω) (x' : Fin (N' + 1) → Ω), IsDomination S x x' →
    IsBirationalPt S x → IsBirationalPt S x' → IsNormalPt S x →
    (∀ (i : Fin (N + 1)) (hi : x i ≠ 0), domRing S x x' i = (chartRing S x (singleChart hi) : Set Ω)) ∧
      ∀ (L : LineBundle S x) (n : ℕ), pullSecs x' (L.pow n) ≤ (L.pow n).secs
def Domination.Conductor.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω]
    (N N' : ℕ) (x : Fin (N + 1) → Ω) (x' : Fin (N' + 1) → Ω), IsDomination S x x' →
    IsBirationalPt S x → IsBirationalPt S x' →
    ∃ (c : ℕ) (κ : Ω), κ ∈ (twistSys S x (c : ℤ)).secs ∧ κ ≠ 0 ∧
      ∀ (L : LineBundle S x) (n : ℕ), ∀ z ∈ pullSecs x' (L.pow n),
        κ * z ∈ ((L.pow n).twist (twistSys S x (c : ℤ))).secs
def Domination.Statement : Prop :=
  Domination.Generic.Statement.{u, w} ∧ Domination.Normal.Statement.{u, w} ∧
    Domination.Conductor.Statement.{u, w}
def SurjectiveClosed.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (Q : LineBundle S x) (J' : Ideal (Poly S N)),
    (∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J') →
    ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c → ∀ s : Chart x → Ω,
      (∀ I, s I ∈ (Q.twist (twistSys S x c)).sub I) →
      (∀ (I₁ I₂ : Chart x), I₁.1 ⊆ I₂.1 →
        s I₁ - s I₂ ∈ ((Q.twist (twistSys S x c)).twist (idealSys x J')).sub I₂) →
      ∃ t ∈ (Q.twist (twistSys S x c)).secs,
        ∀ I, t - s I ∈ ((Q.twist (twistSys S x c)).twist (idealSys x J')).sub I
namespace SubSystem
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
instance quotH.instAddCommGroup (F₁ F₂ : SubSystem S x E) (i : ℕ) : AddCommGroup (quotH F₁ F₂ i) := by
  unfold quotH; infer_instance
instance quotH.instModule (F₁ F₂ : SubSystem S x E) (i : ℕ) : Module S (quotH F₁ F₂ i) := by
  unfold quotH; infer_instance
end SubSystem
def PrimeFiltration.RestrictQuot.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (pp : Ideal (Poly S N)), pp.IsPrime →
    (∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) → primeOf (S := S) x ≤ pp →
    ∀ (j : Fin (N + 1)) (hj : x j ≠ 0), (X j : Poly S N) ∉ pp →
    ∀ (K' : Type w) [Field K'] [Algebra S K'] (ψ : chartRing S x (singleChart hj) →ₐ[S] K'),
      RingHom.ker ψ = chartPrime pp hj →
      ∀ (hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0) (Q : LineBundle S x)
        (Q' : LineBundle S (fun i => ψ (ratio hj i))) (r : Ω → K'),
        RestrictData Q.toSubSystem hxy Q'.toSubSystem r →
        ∀ (c : ℤ) (i : ℕ), Nonempty (SubSystem.quotH (Q.twist (twistSys S x c))
          ((Q.twist (twistSys S x c)).twist (idealSys x pp)) i ≃ₗ[S]
            (Q'.twist (twistSys S (fun l => ψ (ratio hj l)) c)).H i)
def ChartBundleLine.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (B : ReciprocityTheory.ChartRestriction.G.Geo.ChartBundle S x 1 Ω),
    ∃ Q : LineBundle S x,
      (∀ (i : Fin (N + 1)) (hi : x i ≠ 0), (Q.sub (singleChart hi) : Set Ω) = (B.lat i : Set Ω)) ∧
      (Q.secs : Set Ω) = (ReciprocityTheory.ChartRestriction.G.Geo.globalSec B : Set Ω)
def DimTie.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (y : Fin (N + 1) → Ω),
    y ≠ 0 → ∀ e : ℕ, IsSubvar y (primeOf (S := k) y) e ↔ dimCl k y = e
def Restriction.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Nb : LineBundle k x) (r : ℕ) (h : Fin (r + 1) → Ω), IsVeryAmpleBy Nb.toSubSystem h →
    ∀ (pp : Ideal (Poly k N)), pp.IsPrime → (∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) →
    primeOf (S := k) x ≤ pp → ∀ (j : Fin (N + 1)) (hj : x j ≠ 0), (X j : Poly k N) ∉ pp →
    ∀ (K' : Type w) [Field K'] [Algebra k K'] (ψ : chartRing k x (singleChart hj) →ₐ[k] K'),
      RingHom.ker ψ = chartPrime pp hj → ∀ hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0,
      ∃ (Q' : LineBundle k (fun i => ψ (ratio hj i))) (ρ : Ω → K'),
        RestrictData Nb.toSubSystem hxy Q'.toSubSystem ρ ∧ IsVeryAmpleBy Q'.toSubSystem (ρ ∘ h) ∧
        dimCl k (fun i => ψ (ratio hj i)) = dimCl k (ρ ∘ h)
def HilbertPoint.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (y : Fin (N + 1) → Ω),
    IsSubvar y (primeOf (S := k) y) 0 →
    FiniteDimensional k (funField (k := k) y) ∧
    (∀ᶠ n : ℕ in atTop,
      Module.finrank k ((coordGraded k y).piece (n : ℤ)) = Module.finrank k (funField (k := k) y)) ∧
    ∀ᶠ n : ℕ in atTop, (twistSys k y (n : ℤ)).secs = (coordGraded k y).piece (n : ℤ)
def HilbertPositive.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (y : Fin (N + 1) → Ω) (e : ℕ),
    1 ≤ e → IsSubvar y (primeOf (S := k) y) e →
    (∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      |(Module.finrank k ((coordGraded k y).piece (n : ℤ)) : ℝ) -
        (NumbersDVR.intNum k (primeOfOne (S := k) y) (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) : ℝ) *
          (n : ℝ) ^ e / (e.factorial : ℝ)| ≤ C * (n : ℝ) ^ (e - 1)) ∧
    0 < NumbersDVR.intNum k (primeOfOne (S := k) y) (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) ∧
    ∀ᶠ n : ℕ in atTop, (twistSys k y (n : ℤ)).secs = (coordGraded k y).piece (n : ℤ)
def SectionCount.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (Nb : LineBundle k x) (b : ℕ), IsSubvar x (primeOf (S := k) x) (d + 1) →
    IsVeryAmple Nb.toSubSystem → 1 ≤ b →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      ((interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) -
          ((d + 1 : ℕ) : ℤ) * interNum (primeOf (S := k) x)
            (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
              (fun _ : Fin d => Nb.toSubSystem)) : ℤ) : ℝ) *
          (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤
        (Module.finrank k (twistMul Nb.toSubSystem n (-((n : ℤ) * b))).secs : ℝ)
def SectionExists.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (M : LineBundle k x) (t s' : ℚ), IsSubvar x (primeOf (S := k) x) (d + 1) → Nef M.toSubSystem →
    0 < s' → s' < t / (d + 1) →
    (∃ (q : ℕ) (m : ℤ), 1 ≤ q ∧ (m : ℚ) = q * t ∧ IsVeryAmple (twistMul M.toSubSystem q m)) →
    ∃ (p : ℕ) (m c₁ : ℤ), 1 ≤ p ∧ (m : ℚ) = p * (t - s') ∧ 1 ≤ c₁ ∧
      ∃ σ ∈ (twistMul M.toSubSystem p (m - c₁)).secs, σ ≠ 0
def VeryAmpleNefPlusAmple.InDim (k : Type u) [Field k] (d : ℕ) : Prop :=
  ∀ (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (M : LineBundle k x),
    IsSubvar x (primeOf (S := k) x) d → Nef M.toSubSystem → ∀ t : ℚ, 0 < t →
    ∃ (p : ℕ) (m : ℤ), 1 ≤ p ∧ (m : ℚ) = p * t ∧ IsVeryAmple (twistMul M.toSubSystem p m)
def VeryAmpleNefPlusAmple.Statement : Prop :=
  ∀ (k : Type u) [Field k] (d : ℕ), VeryAmpleNefPlusAmple.InDim.{u, w} k d
def StepTwo.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x), (∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e) →
    ∀ (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
      (M₁ M₂ : FinGradedSub (S := k) (x := x) E), (∀ c, M₂.piece c ≤ M₁.piece c) →
      (∀ (f : Poly k N) (e : ℕ), f ∈ T.J → f.IsHomogeneous e → ∀ (a : ℤ), ∀ z ∈ M₁.piece a,
        aeval x f • z ∈ M₂.piece (a + e)) →
      ∃ c₀ : ℤ, ∀ (b : ℕ) (c : ℤ), c₀ ≤ c →
        Subsingleton (SubSystem.quotH ((M₁.tildeSys 0).twist ((T.L.pow b).twist (twistSys k x c)))
          ((M₂.tildeSys 0).twist ((T.L.pow b).twist (twistSys k x c))) 1)
def ClaimVanish.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x), (∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e) →
    ∃ c₀ : ℤ, ∀ (b : ℕ) (c : ℤ), c₀ ≤ c → Subsingleton (((T.L.pow b).twist (twistSys k x c)).H 1)
def StepThree.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x), (∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e) →
    ∃ c₂ : ℤ, ∀ b : ℕ, 1 ≤ b → ((T.L.pow b).twist (twistSys k x c₂)).Generated
def NefPlusAmple.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (M H : LineBundle k x), AmpleData k x H → Nef M.toSubSystem → ∀ ε : ℚ, 0 < ε →
    ∃ (p m : ℕ), 1 ≤ p ∧ (m : ℚ) = p * ε ∧ IsVeryAmple ((M.pow p).twist (H.pow m))
def NefProductNonneg.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (e : ℕ) (pp : Ideal (Poly k N)) (Ms : Fin e → LineBundle k x), IsSubvar x pp e →
    (∀ i, Nef (Ms i).toSubSystem) → 0 ≤ interNum pp (fun i => (Ms i).toSubSystem)
def NefGeneric.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsDedekindDomain S] (F : Type u) [Field F] [Algebra S F]
    [IsFractionRing S F] (Ω : Type w) [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (M : LineBundle S x) (𝔪 : Ideal S), 𝔪.IsMaximal →
    NefAbove M.toSubSystem (𝔪.map (C : S →+* Poly S N)) → Nef (M.toSubSystem.extend F)
open Classical in

def GenericPointSectionInput.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω),
    (∀ (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x), IsSubvar x pp n →
      ∀ᶠ c : ℕ in atTop, interSum pp (fun i => (L i).toSubSystem) c =
        interNum pp (fun i => (L i).toSubSystem)) ∧
    (∀ (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x) (σ : Equiv.Perm (Fin n)),
      IsSubvar x pp n →
      interNum pp (fun i => (L (σ i)).toSubSystem) = interNum pp (fun i => (L i).toSubSystem)) ∧
    (∀ (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x) (i : Fin n)
      (L' L'' : LineBundle k x), IsSubvar x pp n →
      interNum pp (Function.update (fun j => (L j).toSubSystem) i (L'.twist L''.toSubSystem)) =
        interNum pp (Function.update (fun j => (L j).toSubSystem) i L'.toSubSystem) +
          interNum pp (Function.update (fun j => (L j).toSubSystem) i L''.toSubSystem)) ∧
    (∀ (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x) (Lc : LineBundle k x) (s : Ω),
      IsSubvar x pp (n + 1) → s ∈ Lc.secs → (∃ I, s ∉ (Lc.twist (idealSys x pp)).sub I) →
      interNum pp (Fin.snoc (α := fun _ => SubSystem k x Ω) (fun i => (L i).toSubSystem)
          Lc.toSubSystem) =
        ∑ᶠ qq : Ideal (Poly k N),
          if h : qq ∈ (pp ⊔ zeroIdeal Lc.toSubSystem s).minimalPrimes ∧ IsSubvar x qq n then
            haveI : qq.IsPrime := h.1.1.1
            ((cutMult (pp ⊔ zeroIdeal Lc.toSubSystem s) qq).toNat : ℤ) *
              interNum qq (fun i => (L i).toSubSystem)
          else 0) ∧
    (∀ pp : Ideal (Poly k N), IsSubvar x pp 0 →
      interNum pp (![] : Fin 0 → SubSystem k x Ω) =
        (FieldNumbers.resDeg (pp.comap (oneBlock (S := k) (N := N)).toRingHom) : ℤ))
def InterNumTie.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (b : Fin n → ℤ), IsSubvar x pp n →
    interNum pp (fun i => twistSys k x (b i)) =
      NumbersDVR.intNum k (pp.comap (oneBlock (S := k) (N := N)).toRingHom) (fun i _ => b i)
section Hypotheses
variable (k : Type u) [Field k]
def lineChart0' : Chart (genericPt k 1) :=
  singleChart ((map_ne_zero_iff _ (IsFractionRing.injective (Poly k 1) (FractionRing (Poly k 1)))).mpr
    (X_ne_zero 0) : genericPt k 1 0 ≠ 0)
end Hypotheses
end
end GroundTheory.Heights₂.Heights.Kleiman


