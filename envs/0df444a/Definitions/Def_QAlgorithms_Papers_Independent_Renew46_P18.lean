-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P18
-- name    : QAlgorithms_Papers_Independent_Renew46_P18
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T20:18:41.215459+00:00
-- url     : https://prove2.me/theorems/8fc1c3dd-c5b8-430f-acd6-7b698bfc65e1
-- title:
--   Definitions for Categorified central extensions, \'etale Lie 2-groups and Lie's Third Theorem for locally exponential Lie algebras
-- statement:
--   The objects the formalized statements of *Categorified central extensions, \'etale Lie 2-groups and Lie's Third Theorem for locally exponential Lie algebras* (arXiv:0812.1673) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsLoop`: Definition II.1, PDF p. 12: a loop has a two-sided unit and bijective left and right translations. No associativity or common inverse is assumed.
--   - `IsGroupOperation`: The quotient in Lemma II.3, PDF pp. 12–13, is an actual group with these operations. Both inverse equations are included.
--   - `IsNormalizedThreeCocycle`: The normalized trivial-action group 3-cocycle equations, Conventions and Definition I.3, PDF pp. 3,5; written for an explicitly supplied group law.
--   - `IsDiscreteGeneralisedCocycle`: Definition I.3 in the discrete subgroup-coefficient case of Lemma II.3, PDF pp. 5,12. The coefficient map is the actual inclusion A into Z. Discrete smoothness adds no restrictions to these algebraic equations.
--   - `twistedMul`: Equation (1) and Lemma II.3, PDF pp. 3,12: the actual multiplication.
--   - `twistedRightInverse`: Inverse for a twisted group when the cocycle equation holds, Example IV.2, PDF p. 17. For a general loop this is only a right inverse.
--   - `quotientCocycle`: Lemma II.3, PDF p. 12: q composed with F, for the canonical quotient q.
--   - `twistedProjection`: Lemma II.3, PDF p. 12: the specified projection, not an arbitrary map.
--   - `coefficientInclusion`: Lemma II.3, PDF pp. 12–13: the actual embedded copy of A.
--   - `inflatedTheta`: The cocycle associated to II.3's prolongation is Theta inflated along ((Z/A) times H) to H, as necessary for matching the domains, PDF pp. 12–13.
--   - `IsLoopProlongation`: Remark II.2, PDF p. 12, including the assumptions AFTER (18). The associator has direction x(yz) = a((xy)z). The predicate includes surjectivity, the embedded coefficient subgroup of the kernel, all three kernel normalizations, centrality and the descended 3-cocycle. No local associativity is inserted.
--   - `IsCrossedModule`: Equations (19) and (20), Example III.3, PDF p. 15. An automorphic action is a homomorphism into MulAut H.
--   - `crossedSource`: Example III.3, PDF p. 15: source of an arrow in H semidirect G.
--   - `crossedTarget`: Example III.3, PDF p. 15: target of the same arrow.
--   - `crossedIdentity`: Example III.3, PDF p. 15: the categorical identity, distinct from both inversion operations.
--   - `crossedCompose`: Example III.3, PDF p. 15: vertical composition b after a, used only when source b equals target a. Outside that domain its value is immaterial.
--   - `crossedArrowInverse`: Categorical arrow inversion for Example III.3, PDF p. 15. Tensor inversion is instead the group inverse in the semidirect product.
--   - `IsStrictTwoGroup`: Definition III.1 and Example III.3, PDF pp. 14–15: a strict 2-group in internal-groupoid coordinates. Objects and tensor-arrows are groups. The groupoid, tensor interchange, tensor identity and tensor inversion functor equations are all explicit. The associator is the identity, so pentagon, naturality and all its normalizations are strict identities.
-- source:
--   Categorified central extensions, \'etale Lie 2-groups and Lie's Third Theorem for locally exponential Lie algebras, arXiv:0812.1673v3, https://arxiv.org/abs/0812.1673v3

import Mathlib

/-!
Algebraic statements from Wockel, arXiv:0812.1673v3.
All definitions below are local to this paper and have complete bodies.
Analytic and source-ambiguous nodes are explicitly deferred in HARD.md.
Compilation and independent moderation are pending the batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Renew46.P18

universe u v w x

/-- Definition II.1, PDF p. 12: a loop has a two-sided unit and bijective
left and right translations. No associativity or common inverse is assumed. -/
def IsLoop {X : Type u} (mu : X → X → X) (e : X) : Prop :=
  (∀ a, mu e a = a) ∧ (∀ a, mu a e = a) ∧
  (∀ a, Function.Bijective (mu a)) ∧
  (∀ a, Function.Bijective (fun b => mu b a))

/-- The quotient in Lemma II.3, PDF pp. 12–13, is an actual group with
these operations. Both inverse equations are included. -/
def IsGroupOperation {X : Type u} (mu : X → X → X) (e : X)
    (inv : X → X) : Prop :=
  (∀ a, mu e a = a) ∧ (∀ a, mu a e = a) ∧
  (∀ a b c, mu (mu a b) c = mu a (mu b c)) ∧
  (∀ a, mu (inv a) a = e) ∧ (∀ a, mu a (inv a) = e)

/-- Sanity: ordinary groups satisfy precisely the loop translation axioms. -/
example {X : Type u} [Group X] : IsLoop (fun a b : X => a * b) 1 := by
  refine ⟨one_mul, mul_one, ?_, ?_⟩
  · intro a
    exact ⟨fun b c h => mul_left_cancel h,
      fun b => ⟨a⁻¹ * b, by simp [mul_assoc]⟩⟩
  · intro a
    exact ⟨fun b c h => mul_right_cancel h,
      fun b => ⟨b * a⁻¹, by simp [mul_assoc]⟩⟩

/-- Sanity: this predicate does not omit associativity or the inverse laws. -/
example {X : Type u} [Group X] :
    IsGroupOperation (fun a b : X => a * b) 1 (fun a => a⁻¹) := by
  exact ⟨one_mul, mul_one, mul_assoc, inv_mul_cancel, mul_inv_cancel⟩

/-- The normalized trivial-action group 3-cocycle equations, Conventions
and Definition I.3, PDF pp. 3,5; written for an explicitly supplied group law. -/
def IsNormalizedThreeCocycle {H : Type u} {A : Type v} [AddCommGroup A]
    (mul : H → H → H) (e : H) (theta : H → H → H → A) : Prop :=
  (∀ g h, theta e g h = 0) ∧
  (∀ g h, theta g e h = 0) ∧
  (∀ g h, theta g h e = 0) ∧
  (∀ g h k l, theta h k l - theta (mul g h) k l +
    theta g (mul h k) l - theta g h (mul k l) + theta g h k = 0)

/-- Sanity: the zero 3-cocycle is normalized for every group law. -/
example {H : Type u} {A : Type v} [AddCommGroup A]
    (mul : H → H → H) (e : H) :
    IsNormalizedThreeCocycle mul e (fun _ _ _ => (0 : A)) := by
  simp [IsNormalizedThreeCocycle]

section DiscreteCocycles

variable {H : Type u} {Z : Type v} [Group H] [AddCommGroup Z]

/-- Definition I.3 in the discrete subgroup-coefficient case of Lemma II.3,
PDF pp. 5,12. The coefficient map is the actual inclusion A into Z.
Discrete smoothness adds no restrictions to these algebraic equations. -/
def IsDiscreteGeneralisedCocycle (A : AddSubgroup Z)
    (F : H → H → Z) (theta : H → H → H → A) : Prop :=
  (∀ g, F 1 g = 0) ∧ (∀ g, F g 1 = 0) ∧
  IsNormalizedThreeCocycle (fun g h : H => g * h) 1 theta ∧
  (∀ g h k, F h k - F (g * h) k + F g (h * k) - F g h =
    (theta g h k : Z))

/-- Equation (1) and Lemma II.3, PDF pp. 3,12: the actual multiplication. -/
def twistedMul (F : H → H → Z) (a b : Z × H) : Z × H :=
  (a.1 + b.1 + F a.2 b.2, a.2 * b.2)

/-- Inverse for a twisted group when the cocycle equation holds,
Example IV.2, PDF p. 17. For a general loop this is only a right inverse. -/
def twistedRightInverse (F : H → H → Z) (a : Z × H) : Z × H :=
  (-a.1 - F a.2 a.2⁻¹, a.2⁻¹)

/-- Lemma II.3, PDF p. 12: q composed with F, for the canonical quotient q. -/
def quotientCocycle (A : AddSubgroup Z) (F : H → H → Z) :
    H → H → Z ⧸ A :=
  fun g h => QuotientAddGroup.mk' A (F g h)

/-- Lemma II.3, PDF p. 12: the specified projection, not an arbitrary map. -/
def twistedProjection (A : AddSubgroup Z) (a : Z × H) : (Z ⧸ A) × H :=
  (QuotientAddGroup.mk' A a.1, a.2)

/-- Lemma II.3, PDF pp. 12–13: the actual embedded copy of A. -/
def coefficientInclusion (A : AddSubgroup Z) (a : A) : Z × H :=
  (a.val, 1)

/-- The cocycle associated to II.3's prolongation is Theta inflated along
((Z/A) times H) to H, as necessary for matching the domains, PDF pp. 12–13. -/
def inflatedTheta (A : AddSubgroup Z) (theta : H → H → H → A) :
    ((Z ⧸ A) × H) → ((Z ⧸ A) × H) → ((Z ⧸ A) × H) → A :=
  fun a b c => theta a.2 b.2 c.2

/-- Sanity: zero twisting gives precisely the ordinary product law. -/
example (a b : Z × H) :
    twistedMul (fun _ _ : H => (0 : Z)) a b = (a.1 + b.1, a.2 * b.2) := by
  simp [twistedMul]

/-- Sanity: zero twisting gives the ordinary product inverse. -/
example (a : Z × H) :
    twistedRightInverse (fun _ _ : H => (0 : Z)) a = (-a.1, a.2⁻¹) := by
  simp [twistedRightInverse]

/-- Sanity: quotient twisting uses the actual quotient homomorphism. -/
example (A : AddSubgroup Z) (g h : H) :
    quotientCocycle A (fun _ _ : H => (0 : Z)) g h = 0 := by
  simp [quotientCocycle]

/-- Sanity: the coefficient inclusion keeps the coefficient value exactly. -/
example (A : AddSubgroup Z) (a : A) :
    (coefficientInclusion (H := H) A a).1 = a.val := rfl

/-- Sanity: projection keeps the underlying H-coordinate. -/
example (A : AddSubgroup Z) (a : Z × H) :
    (twistedProjection A a).2 = a.2 := rfl

/-- Sanity: inflation retains the original spherical-cocycle coordinates. -/
example (A : AddSubgroup Z) (theta : H → H → H → A)
    (a b c : (Z ⧸ A) × H) : inflatedTheta A theta a b c =
    theta a.2 b.2 c.2 := rfl

/-- Sanity: the degenerate zero system satisfies all generalized equations. -/
example (A : AddSubgroup Z) :
    IsDiscreteGeneralisedCocycle A (fun _ _ : H => (0 : Z))
      (fun _ _ _ => (0 : A)) := by
  simp [IsDiscreteGeneralisedCocycle, IsNormalizedThreeCocycle]

end DiscreteCocycles

/-- Remark II.2, PDF p. 12, including the assumptions AFTER (18).
The associator has direction x(yz) = a((xy)z). The predicate includes
surjectivity, the embedded coefficient subgroup of the kernel, all three kernel normalizations,
centrality and the descended 3-cocycle. No local associativity is inserted. -/
def IsLoopProlongation {X : Type u} {B : Type v} {A : Type w} [AddCommGroup A]
    (mu : X → X → X) (e : X) (nu : B → B → B) (eb : B) (invb : B → B)
    (q : X → B) (i : A → X) (theta : B → B → B → A) : Prop :=
  IsLoop mu e ∧ IsGroupOperation nu eb invb ∧
  Function.Surjective q ∧ q e = eb ∧
  (∀ a b, q (mu a b) = nu (q a) (q b)) ∧
  Function.Injective i ∧ i 0 = e ∧
  (∀ a b, i (a + b) = mu (i a) (i b)) ∧
  (∀ c, q (i c) = eb) ∧
  (∀ a b c, mu a (mu b c) =
    mu (i (theta (q a) (q b) (q c))) (mu (mu a b) c)) ∧
  (∀ k a b, q k = eb →
    i (theta (q k) (q a) (q b)) = e ∧
    i (theta (q a) (q k) (q b)) = e ∧
    i (theta (q a) (q b) (q k)) = e) ∧
  (∀ k a b c, q k = eb →
    mu k (i (theta (q a) (q b) (q c))) =
      mu (i (theta (q a) (q b) (q c))) k) ∧
  (∀ a c, mu a (i c) = mu (i c) a) ∧
  IsNormalizedThreeCocycle nu eb theta

/-- Sanity: the one-element loop, base, and coefficient give a prolongation;
thus the full collection of axioms has a nonempty instance. -/
example : IsLoopProlongation
    (fun _ _ : PUnit => PUnit.unit) PUnit.unit
    (fun _ _ : PUnit => PUnit.unit) PUnit.unit (fun _ => PUnit.unit)
    (fun _ => PUnit.unit) (fun _ : PUnit => PUnit.unit)
    (fun _ _ _ => (0 : PUnit)) := by
  simp [IsLoopProlongation, IsLoop, IsGroupOperation,
    IsNormalizedThreeCocycle, Function.Surjective, Function.Injective,
    Function.Bijective]

section CrossedModules

variable {H : Type u} {G : Type v} [Group H] [Group G]

/-- Equations (19) and (20), Example III.3, PDF p. 15.
An automorphic action is a homomorphism into MulAut H. -/
def IsCrossedModule (tau : H →* G) (rho : G →* MulAut H) : Prop :=
  (∀ g h, tau (rho g h) = g * tau h * g⁻¹) ∧
  (∀ h k, rho (tau h) k = h * k * h⁻¹)

/-- Example III.3, PDF p. 15: source of an arrow in H semidirect G. -/
def crossedSource (rho : G →* MulAut H) (a : SemidirectProduct H G rho) : G :=
  a.right

/-- Example III.3, PDF p. 15: target of the same arrow. -/
def crossedTarget (tau : H →* G) (rho : G →* MulAut H)
    (a : SemidirectProduct H G rho) : G :=
  tau a.left * a.right

/-- Example III.3, PDF p. 15: the categorical identity, distinct from
both inversion operations. -/
def crossedIdentity (rho : G →* MulAut H) (g : G) : SemidirectProduct H G rho :=
  ⟨1, g⟩

/-- Example III.3, PDF p. 15: vertical composition b after a, used only
when source b equals target a. Outside that domain its value is immaterial. -/
def crossedCompose (rho : G →* MulAut H)
    (b a : SemidirectProduct H G rho) : SemidirectProduct H G rho :=
  ⟨b.left * a.left, a.right⟩

/-- Categorical arrow inversion for Example III.3, PDF p. 15.
Tensor inversion is instead the group inverse in the semidirect product. -/
def crossedArrowInverse (tau : H →* G) (rho : G →* MulAut H)
    (a : SemidirectProduct H G rho) : SemidirectProduct H G rho :=
  ⟨a.left⁻¹, tau a.left * a.right⟩

/-- Sanity: a trivial action on trivial groups gives an actual crossed module. -/
example : IsCrossedModule (MonoidHom.id PUnit)
    (1 : PUnit →* MulAut PUnit) := by
  constructor <;> intro a b <;> exact Subsingleton.elim _ _

/-- Sanity: source, target and vertical inverse retain the intended coordinates. -/
example (tau : H →* G) (rho : G →* MulAut H)
    (a : SemidirectProduct H G rho) :
    crossedSource rho a = a.right ∧
    crossedTarget tau rho a = tau a.left * a.right ∧
    (crossedArrowInverse tau rho a).left = a.left⁻¹ := ⟨rfl, rfl, rfl⟩

/-- Sanity: identities and composition use vertical rather than tensor laws. -/
example (rho : G →* MulAut H) (g : G) (a b : SemidirectProduct H G rho) :
    (crossedIdentity rho g).left = 1 ∧
    (crossedCompose rho b a).left = b.left * a.left := ⟨rfl, rfl⟩

end CrossedModules

/-- Definition III.1 and Example III.3, PDF pp. 14–15: a strict 2-group
in internal-groupoid coordinates. Objects and tensor-arrows are groups.
The groupoid, tensor interchange, tensor identity and tensor inversion
functor equations are all explicit. The associator is the identity, so
pentagon, naturality and all its normalizations are strict identities. -/
def IsStrictTwoGroup {O : Type u} {K : Type v} [Group O] [Group K]
    (s t : K → O) (identity : O → K) (comp : K → K → K)
    (arrowInv : K → K) : Prop :=
  (∀ a, s (identity a) = a ∧ t (identity a) = a) ∧
  (∀ a b, s b = t a → s (comp b a) = s a ∧ t (comp b a) = t b) ∧
  (∀ a, comp (identity (t a)) a = a ∧ comp a (identity (s a)) = a) ∧
  (∀ a b c, s b = t a → s c = t b →
    comp c (comp b a) = comp (comp c b) a) ∧
  (∀ a, s (arrowInv a) = t a ∧ t (arrowInv a) = s a ∧
    comp (arrowInv a) a = identity (s a) ∧
    comp a (arrowInv a) = identity (t a)) ∧
  s 1 = 1 ∧ t 1 = 1 ∧ identity 1 = 1 ∧
  (∀ a b, s (a * b) = s a * s b ∧ t (a * b) = t a * t b) ∧
  (∀ a b, identity (a * b) = identity a * identity b) ∧
  (∀ a b c d, s b = t a → s d = t c →
    comp (b * d) (a * c) = comp b a * comp d c) ∧
  (∀ a, s a⁻¹ = (s a)⁻¹ ∧ t a⁻¹ = (t a)⁻¹) ∧
  (∀ a, identity a⁻¹ = (identity a)⁻¹) ∧
  (∀ a b, s b = t a → comp b⁻¹ a⁻¹ = (comp b a)⁻¹)

/-- Sanity: the singleton strict 2-group has both inversion operations
and satisfies every categorical and tensor equation. -/
example : IsStrictTwoGroup (fun _ : PUnit => PUnit.unit)
    (fun _ : PUnit => PUnit.unit) (fun _ => PUnit.unit)
    (fun _ _ => PUnit.unit) (fun _ => PUnit.unit) := by
  simp [IsStrictTwoGroup]

end QAlgorithms.Papers.Independent.Renew46.P18


