-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_BracketDerivative
-- name    : liuyao_ca_fd889115_k1_Analysis_BracketDerivative
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:54:38.715341+00:00
-- url     : https://prove2.me/theorems/54ac1552-bf3a-4d3f-9ced-da5578957b87
-- title:
--   Computable analysis · BracketDerivative · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/BracketDerivative.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ParametrizedLimits

set_option autoImplicit true

/-! Derivatives of rational-input functions using covered parametrized limits. -/
namespace ComputableAnalysis


namespace BracketDerivative

/-- Brackets remain inside the rational domain at EVERY stage and have
strictly positive width at EVERY stage. Non-emptiness is required separately. -/
def Admissible (domain : Rat → Prop) (x A : RealCompute) : Prop :=
  x.Valid ∧ A.Valid ∧ A.Equiv x ∧
  ∀ n, (A.compute n).lo < (A.compute n).hi ∧
    ∀ r, (A.compute n).lo ≤ r → r ≤ (A.compute n).hi → domain r

/-- The two rational endpoint evaluations are the only evaluations used. -/
def secant (f : Rat → RealCompute) (a b : Rat) : RealCompute :=
  RealCompute.scaleRat (1/(b-a)) (f b-f a)

def secants (f : Rat → RealCompute) (A : RealCompute) : Nat → RealCompute :=
  fun n => secant f (A.compute n).lo (A.compute n).hi

theorem secant_valid {f : Rat → RealCompute} {a b : Rat}
    (ha : (f a).Valid) (hb : (f b).Valid) : (secant f a b).Valid :=
  RealCompute.scaleRat_valid (RealCompute.sub_valid hb ha)

theorem secants_valid {domain : Rat → Prop} {f : Rat → RealCompute} {x A : RealCompute}
    (hf : ∀ r, domain r → (f r).Valid) (hA : Admissible domain x A) :
    ∀ n, (secants f A n).Valid := by
  intro n
  have h := hA.2.2.2 n
  exact secant_valid (hf _ (h.2 _ (Rat.le_refl) (Rat.le_of_lt h.1)))
    (hf _ (h.2 _ (Rat.le_of_lt h.1) (Rat.le_refl)))

/-- A derivative is a common limit of all admissible secants, with no
irrational evaluation of the primary function and no prescribed algorithm. -/
def HasDerivativeAt (domain : Rat → Prop) (f : Rat → RealCompute) (x d : RealCompute) : Prop :=
  x.Valid ∧ d.Valid ∧ (∀ r, domain r → (f r).Valid) ∧
  (∃ A, Admissible domain x A) ∧
  ∀ A, Admissible domain x A → RawLimit.HasParametrizedLimit (secants f A) d

/-- Exact compatibility with the previously checked secant-limit interface.
The existential diagonal covers every remaining secant, so no subsequence is
silently substituted for a limit. -/
theorem hasDerivative_iff_secantLimits {domain : Rat → Prop} {f : Rat → RealCompute}
    {x d : RealCompute} : HasDerivativeAt domain f x d ↔
    x.Valid ∧ d.Valid ∧ (∀ r, domain r → (f r).Valid) ∧
      (∃ A, Admissible domain x A) ∧
      ∀ A, Admissible domain x A → RawLimit.TendsTo (secants f A) d := by
  constructor
  · intro h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,
      fun A hA => RawLimit.parametrizedLimit_iff.mp (h.2.2.2.2 A hA)⟩
  · intro h
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,
      fun A hA => RawLimit.parametrizedLimit_iff.mpr (h.2.2.2.2 A hA)⟩

theorem admissible_congr {domain : Rat → Prop} {x y A : RealCompute}
    (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) :
    Admissible domain x A ↔ Admissible domain y A := by
  constructor
  · intro h
    exact ⟨hy,h.2.1,RealCompute.equiv_trans h.2.1 hx hy h.2.2.1 hxy,h.2.2.2⟩
  · intro h
    exact ⟨hx,h.2.1,RealCompute.equiv_trans h.2.1 hy hx h.2.2.1
      (RealCompute.equiv_symm hxy),h.2.2.2⟩

theorem unique {domain : Rat → Prop} {f : Rat → RealCompute} {x d e : RealCompute}
    (hd : HasDerivativeAt domain f x d) (he : HasDerivativeAt domain f x e) : d.Equiv e := by
  obtain ⟨A,hA⟩ := hd.2.2.2.1
  exact RawLimit.HasParametrizedLimit.unique (hd.2.2.2.2 A hA) (he.2.2.2.2 A hA)

theorem congr_point {domain : Rat → Prop} {f : Rat → RealCompute} {x y d : RealCompute}
    (h : HasDerivativeAt domain f x d) (hy : y.Valid) (hxy : x.Equiv y) :
    HasDerivativeAt domain f y d := by
  refine ⟨hy,h.2.1,h.2.2.1,?_,?_⟩
  · obtain ⟨A,hA⟩ := h.2.2.2.1
    exact ⟨A,(admissible_congr h.1 hy hxy).1 hA⟩
  · intro A hA
    exact h.2.2.2.2 A ((admissible_congr h.1 hy hxy).2 hA)

theorem congr_value {domain : Rat → Prop} {f : Rat → RealCompute} {x d e : RealCompute}
    (h : HasDerivativeAt domain f x d) (he : e.Valid) (hde : d.Equiv e) :
    HasDerivativeAt domain f x e := by
  exact ⟨h.1,he,h.2.2.1,h.2.2.2.1,fun A hA =>
    RawLimit.parametrizedLimit_iff.mpr
      (RawLimit.congr_target (RawLimit.parametrizedLimit_iff.mp (h.2.2.2.2 A hA)) he hde)⟩

theorem congr_point_iff {domain : Rat → Prop} {f : Rat → RealCompute} {x y d : RealCompute}
    (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y) :
    HasDerivativeAt domain f x d ↔ HasDerivativeAt domain f y d :=
  ⟨fun h => congr_point h hy hxy,
   fun h => congr_point h hx (RealCompute.equiv_symm hxy)⟩

theorem congr_value_iff {domain : Rat → Prop} {f : Rat → RealCompute} {x d e : RealCompute}
    (hd : d.Valid) (he : e.Valid) (hde : d.Equiv e) :
    HasDerivativeAt domain f x d ↔ HasDerivativeAt domain f x e :=
  ⟨fun h => congr_value h he hde,
   fun h => congr_value h hd (RealCompute.equiv_symm hde)⟩

theorem congr_function {domain : Rat → Prop} {f g : Rat → RealCompute} {x d : RealCompute}
    (h : HasDerivativeAt domain f x d)
    (hg : ∀ r, domain r → (g r).Valid)
    (hfg : ∀ r, domain r → (f r).Equiv (g r)) :
    HasDerivativeAt domain g x d := by
  refine ⟨h.1,h.2.1,hg,h.2.2.2.1,?_⟩
  intro A hA
  apply RawLimit.parametrizedLimit_iff.mpr
  apply RawLimit.congr_sequence (RawLimit.parametrizedLimit_iff.mp (h.2.2.2.2 A hA)) (secants_valid hg hA)
  intro n
  have ha := hA.2.2.2 n
  have hlo := ha.2 _ (Rat.le_refl) (Rat.le_of_lt ha.1)
  have hhi := ha.2 _ (Rat.le_of_lt ha.1) (Rat.le_refl)
  exact RealCompute.scaleRat_equiv
    (RealCompute.sub_equiv (h.2.2.1 _ hhi) (hg _ hhi)
      (h.2.2.1 _ hlo) (hg _ hlo) (hfg _ hhi) (hfg _ hlo))

end BracketDerivative
end ComputableAnalysis


