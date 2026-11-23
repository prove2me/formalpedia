-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
-- name    : Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:27.840558+00:00
-- url     : https://prove2.me/theorems/26825850-d9a2-4972-9a66-3be539b85eb9
-- title:
--   Pl Ord Some Of Associated
-- statement:
--   Definitions and structural lemmas for Pl Ord Some Of Associated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/PlOrdSomeOfAssociated.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.SS
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw
def FrobG {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (F : End G) (q : ℕ) : Prop :=
  IsMonHom (show G ⟶ G from F) ∧ ∀ U : G.left.Opens, IsAffineOpen U → ∀ f : Γ(G.left, U), ∃ m : ℕ, 1 ≤ m ∧
    ∃ h : U = (show G ⟶ G from F ^ m).left ⁻¹ᵁ U, ((show G ⟶ G from F ^ m).left.appLE U U h.le).hom f = f ^ (q ^ m)
def AmpleCub {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) : Prop :=
  L.IsLB ∧ (∃ t : LB.Gen (Theta G L), t.IsGen) ∧
  (∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]), t.IsGen) ∧
  ∃ n : ℕ, 1 ≤ n ∧ ∀ x : G.left, ∃ s : LB.Sec (pw L n), x ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)
def PullPow {X : Scheme.{0}} (F : X ⟶ X) (L : LB X) (q : ℤ) : Prop :=
  ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![F, 𝟙 X] ![1, -q]), t.IsGen
structure Places (k K : Type) [Field k] [Field K] [Algebra k K] where
  I : Type
  O : I → ValuationSubring K
  v : I → Kˣ → ℤ
  v_mul : ∀ i x y, v i (x * y) = v i x + v i y
  mem : ∀ i (x : Kˣ), (x : K) ∈ O i ↔ 0 ≤ v i x
  const : ∀ i c, algebraMap k K c ∈ O i
  fin : ∀ x, (Function.support fun i => v i x).Finite
  sum : ∀ x, ∑ᶠ i, v i x = 0
section ProjLine
open Polynomial IsDedekindDomain
variable (k : Type) [Field k]
abbrev MonIrr : Type := {p : k[X] // p.Monic ∧ Irreducible p}
def MonIrr.prime {k : Type} [Field k] (p : MonIrr k) : HeightOneSpectrum k[X] where
  asIdeal := Ideal.span {p.1}
  isPrime := (Ideal.span_singleton_prime p.2.2.ne_zero).2 p.2.2.prime
  ne_bot := by simpa using p.2.2.ne_zero
open scoped Classical in

def plVal : Option (MonIrr k) → Valuation (RatFunc k) (WithZero (Multiplicative ℤ))
  | none => RatFunc.inftyValuation k
  | some p => p.prime.valuation (RatFunc k)
def plDeg : Option (MonIrr k) → ℕ
  | none => 1
  | some p => p.1.natDegree
def plOrd (i : Option (MonIrr k)) (x : RatFunc k) : ℤ := -(plDeg k i : ℤ) * WithZero.log (plVal k i x)
variable {k}
theorem plDeg_pos (i : Option (MonIrr k)) : 0 < plDeg k i := by
  cases i with
  | none => exact Nat.one_pos
  | some p => exact Polynomial.natDegree_pos_iff_degree_pos.2 (Polynomial.degree_pos_of_irreducible p.2.2)
theorem plOrd_mul (i : Option (MonIrr k)) {x y : RatFunc k} (hx : x ≠ 0) (hy : y ≠ 0) :
    plOrd k i (x * y) = plOrd k i x + plOrd k i y := by
  have hx' : plVal k i x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : plVal k i y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  unfold plOrd
  rw [map_mul, WithZero.log_mul hx' hy']
  ring
theorem plOrd_none {p : k[X]} (hp : p ≠ 0) :
    plOrd k none (algebraMap k[X] (RatFunc k) p) = -(p.natDegree : ℤ) := by
  classical
  have h : plVal k none (algebraMap k[X] (RatFunc k) p) = WithZero.exp (p.natDegree : ℤ) := by
    show RatFunc.inftyValuation k _ = _
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation.polynomial (F := k) hp]
  unfold plOrd
  rw [h, WithZero.log_exp]
  simp [plDeg]
theorem plOrd_some_of_not_dvd (π : MonIrr k) {p : k[X]} (h : ¬ π.1 ∣ p) :
    plOrd k (some π) (algebraMap k[X] (RatFunc k) p) = 0 := by
  classical
  have h1 : plVal k (some π) (algebraMap k[X] (RatFunc k) p) = 1 := by
    show π.prime.valuation (RatFunc k) _ = 1
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    show p ∉ Ideal.span {π.1}
    rwa [Ideal.mem_span_singleton]
  unfold plOrd
  rw [h1, WithZero.log_one, mul_zero]
theorem plOrd_some_of_associated (π : MonIrr k) {p : k[X]} (h : Associated π.1 p) :
    plOrd k (some π) (algebraMap k[X] (RatFunc k) p) = p.natDegree := by
  classical
  have hp : p ≠ 0 := by
    rintro rfl
    exact π.2.2.ne_zero ((associated_zero_iff_eq_zero _).1 h)
  have h1 : plVal k (some π) (algebraMap k[X] (RatFunc k) p) = WithZero.exp (-1 : ℤ) := by
    show π.prime.valuation (RatFunc k) _ = _
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact π.prime.intValuation_singleton hp
      (show Ideal.span {π.1} = Ideal.span {p} from Ideal.span_singleton_eq_span_singleton.2 h)
  have hd : p.natDegree = π.1.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated h).symm
  unfold plOrd
  rw [h1, WithZero.log_exp, hd]
  simp [plDeg]
def PF (x : RatFunc k) : Prop :=
  (Function.support fun i => plOrd k i x).Finite ∧ ∑ᶠ i, plOrd k i x = 0
theorem PF.mul {x y : RatFunc k} (hx : x ≠ 0) (hy : y ≠ 0) (a : PF x) (b : PF y) : PF (x * y) := by
  have e : (fun i => plOrd k i (x * y)) = fun i => plOrd k i x + plOrd k i y :=
    funext fun i => plOrd_mul i hx hy
  unfold PF at *
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  refine ⟨?_, ?_⟩
  · rw [e]
    exact (a1.union b1).subset (Function.support_add _ _)
  · rw [e, finsum_add_distrib a1 b1, a2, b2, add_zero]
theorem PF.inv {x : RatFunc k} (hx : x ≠ 0) (a : PF x) : PF x⁻¹ := by
  have e : (fun i => plOrd k i x⁻¹) = fun i => -plOrd k i x := by
    funext i
    have h1 := plOrd_mul i hx (inv_ne_zero hx)
    have h0 : plOrd k i 1 = 0 := by
      unfold plOrd
      rw [map_one, WithZero.log_one, mul_zero]
    rw [mul_inv_cancel₀ hx, h0] at h1
    linarith
  unfold PF at *
  obtain ⟨a1, a2⟩ := a
  refine ⟨?_, ?_⟩
  · rw [e]
    exact a1.subset fun i hi => by simpa [Function.mem_support] using hi
  · rw [e, finsum_neg_distrib, a2, neg_zero]
theorem pf_algebraMap_of_isUnit {u : k[X]} (hu : IsUnit u) : PF (algebraMap k[X] (RatFunc k) u) := by
  have hz : ∀ i, plOrd k i (algebraMap k[X] (RatFunc k) u) = 0 := by
    intro i
    cases i with
    | none => rw [plOrd_none hu.ne_zero, Polynomial.natDegree_eq_zero_of_isUnit hu]; simp
    | some π => exact plOrd_some_of_not_dvd π fun hd => π.2.2.not_isUnit (isUnit_of_dvd_unit hd hu)
  have e : (fun i => plOrd k i (algebraMap k[X] (RatFunc k) u)) = fun _ => 0 := funext hz
  unfold PF
  rw [e]
  exact ⟨by simp, by simp⟩
theorem pf_algebraMap_of_irreducible {q : k[X]} (hq : Irreducible q) : PF (algebraMap k[X] (RatFunc k) q) := by
  classical
  have hq0 : q ≠ 0 := hq.ne_zero
  let π₀ : MonIrr k := ⟨normalize q, Polynomial.monic_normalize hq0, (associated_normalize q).irreducible hq⟩
  have hπ₀ : Associated π₀.1 q := (associated_normalize q).symm
  have hz : ∀ i, i ≠ none → i ≠ some π₀ → plOrd k i (algebraMap k[X] (RatFunc k) q) = 0 := by
    intro i h1 h2
    cases i with
    | none => exact absurd rfl h1
    | some π =>
      apply plOrd_some_of_not_dvd
      intro hd
      apply h2
      congr 1
      exact Subtype.ext (Polynomial.eq_of_monic_of_associated π.2.1 π₀.2.1
        ((π.2.2.associated_of_dvd hq hd).trans hπ₀.symm))
  have hs : Function.support (fun i => plOrd k i (algebraMap k[X] (RatFunc k) q)) ⊆
      ((({none, some π₀} : Finset (Option (MonIrr k)))) : Set (Option (MonIrr k))) := by
    intro i hi
    by_contra hn
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or] at hn
    exact hi (hz i hn.1 hn.2)
  unfold PF
  refine ⟨(Finset.finite_toSet _).subset hs, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_pair (by simp), plOrd_none hq0,
    plOrd_some_of_associated π₀ hπ₀]
  ring
theorem pf_poly (p : k[X]) : p ≠ 0 → PF (algebraMap k[X] (RatFunc k) p) := by
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => exact fun h => absurd rfl h
  | unit u hu => exact fun _ => pf_algebraMap_of_isUnit hu
  | mul a i ha hi ih =>
    intro _
    rw [map_mul]
    exact PF.mul (RatFunc.algebraMap_ne_zero hi.ne_zero) (RatFunc.algebraMap_ne_zero ha)
      (pf_algebraMap_of_irreducible hi) (ih ha)
theorem pf_all (x : RatFunc k) : x ≠ 0 → PF x := by
  intro hx
  rw [← RatFunc.num_div_denom x, div_eq_mul_inv]
  exact PF.mul (RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hx))
    (inv_ne_zero (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero x)))
    (pf_poly _ (RatFunc.num_ne_zero hx))
    (PF.inv (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero x)) (pf_poly _ (RatFunc.denom_ne_zero x)))
variable (k)
def projLinePlaces : Places k (RatFunc k) where
  I := Option (MonIrr k)
  O := fun i => (plVal k i).valuationSubring
  v := fun i x => plOrd k i x
  v_mul := fun i x y => plOrd_mul i x.ne_zero y.ne_zero
  mem := fun i x => by
    have hx : plVal k i x ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
    have hd : (0 : ℤ) < plDeg k i := by exact_mod_cast plDeg_pos i
    rw [Valuation.mem_valuationSubring_iff, ← WithZero.log_le_log hx one_ne_zero, WithZero.log_one]
    unfold plOrd
    constructor <;> intro h <;> nlinarith
  const := fun i c => by
    classical
    rw [Valuation.mem_valuationSubring_iff]
    cases i with
    | none =>
      by_cases hc : c = 0
      · simp [hc]
      · exact (RatFunc.inftyValuation.C k hc).le
    | some π =>
      rw [IsScalarTower.algebraMap_apply k k[X] (RatFunc k)]
      exact π.prime.valuation_le_one (K := RatFunc k) _
  fin := fun x => (pf_all x.1 x.ne_zero).1
  sum := fun x => (pf_all x.1 x.ne_zero).2
end ProjLine
end GlobalTheory.SS
end


