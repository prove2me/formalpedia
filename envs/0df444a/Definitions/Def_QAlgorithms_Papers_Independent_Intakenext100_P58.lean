-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P58
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P58
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T06:46:49.771978+00:00
-- url     : https://prove2.me/theorems/1d6956c6-7437-46f6-a0c7-7a8dd2bf559a
-- title:
--   Definitions for G-gerbes, principal 2-group bundles and characteristic classes
-- statement:
--   The objects the formalized statements of *G-gerbes, principal 2-group bundles and characteristic classes* (arXiv:0801.1238) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `GroupoidData`: Definition 2.3 and Example 2.5, PDF pp. 5–6: groupoid operations. `mul a b` means a after b, and is only constrained when `s a = t b`. The inverse and both unit laws are included, also for an empty groupoid.
--   - `composablePairs`: The composable-pair locus, with the same multiplication order as the paper.
--   - `pointGroupoid`: The trivial groupoid on one point is a nonvacuous small instance.
--   - `IsLieGroupoid`: Remark 2.2 and Example 2.5, PDF pp. 5–6: smooth Lie groupoid data on finite-dimensional, boundaryless real manifolds. Multiplication is smooth on its embedded composable-pair locus; its total value elsewhere is unused. Source and target are surjective smooth submersions, not merely smooth maps.
--   - `Loops`: Example 2.5, PDF p. 6: all closed arrows, without a smoothness assertion.
--   - `loopBase`: The family map sends a closed arrow to its common endpoint.
--   - `loopInclusion`: The crossed-module map is the actual inclusion of closed arrows.
--   - `loopUnit`: The identity loop over an object.
--   - `loopInverse`: Inversion in each isotropy group.
--   - `loopMultiply`: Multiplication is used on loops over the same object. The arbitrary value on unequal fibres is never used in the family-of-groups axioms.
--   - `loopConjugate`: Definition 2.3, equations (2),(3), and Example 2.5, PDF pp. 5–6: the right action is x to gamma inverse times x times gamma, with its exact source/target domain. Values off that domain are not part of the action.
--   - `IsGroupFamily`: Definition 2.3, PDF p. 5: a family of groups over M. There is no multiplication between different fibres. All unit, associative and inverse laws, and preservation of the base by the operations, are explicit.
--   - `IsRightCrossedModule`: Definition 2.3, PDF p. 5: algebraic crossed modules with the paper's RIGHT action convention. The action is by group automorphisms (inverse arrows give inverse actions); rho is an identity-on-objects functor. The last two clauses are exactly equations (2) and (3).
-- source:
--   G-gerbes, principal 2-group bundles and characteristic classes, arXiv:0801.1238v3, https://arxiv.org/abs/0801.1238v3

import Mathlib

/-!
Statements from Ginot–Stienon, arXiv:0801.1238v3.
Example 2.5 is algebraic on the underlying groupoids; no manifold structure
on the set of loops is asserted. Other nodes and their missing geometric
interfaces are recorded individually in HARD.md and GAPS.json.
Compilation is pending the authorized batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Intakenext100.P58

open scoped Manifold ContDiff

universe u v w

/-- Definition 2.3 and Example 2.5, PDF pp. 5–6: groupoid operations.
`mul a b` means a after b, and is only constrained when `s a = t b`.
The inverse and both unit laws are included, also for an empty groupoid. -/
structure GroupoidData (M : Type u) (A : Type v) where
  s : A → M
  t : A → M
  unit : M → A
  inv : A → A
  mul : A → A → A
  s_unit : ∀ m, s (unit m) = m
  t_unit : ∀ m, t (unit m) = m
  s_inv : ∀ a, s (inv a) = t a
  t_inv : ∀ a, t (inv a) = s a
  s_mul : ∀ a b, s a = t b → s (mul a b) = s b
  t_mul : ∀ a b, s a = t b → t (mul a b) = t a
  unit_left : ∀ a, mul (unit (t a)) a = a
  unit_right : ∀ a, mul a (unit (s a)) = a
  inv_left : ∀ a, mul (inv a) a = unit (s a)
  inv_right : ∀ a, mul a (inv a) = unit (t a)
  assoc : ∀ a b c, s a = t b → s b = t c →
    mul (mul a b) c = mul a (mul b c)

/-- The composable-pair locus, with the same multiplication order as the paper. -/
def composablePairs {M : Type u} {A : Type v} (D : GroupoidData M A) : Set (A × A) :=
  {p | D.s p.1 = D.t p.2}

/-- The trivial groupoid on one point is a nonvacuous small instance. -/
def pointGroupoid : GroupoidData PUnit PUnit where
  s := id
  t := id
  unit := id
  inv := id
  mul := fun _ _ => PUnit.unit
  s_unit := fun _ => rfl
  t_unit := fun _ => rfl
  s_inv := fun _ => rfl
  t_inv := fun _ => rfl
  s_mul := fun _ _ _ => Subsingleton.elim _ _
  t_mul := fun _ _ _ => Subsingleton.elim _ _
  unit_left := fun _ => Subsingleton.elim _ _
  unit_right := fun _ => Subsingleton.elim _ _
  inv_left := fun _ => Subsingleton.elim _ _
  inv_right := fun _ => Subsingleton.elim _ _
  assoc := fun _ _ _ _ _ => Subsingleton.elim _ _

/-- Sanity: the unique pair really is composable. -/
example : (PUnit.unit, PUnit.unit) ∈ composablePairs pointGroupoid := rfl

/-- Remark 2.2 and Example 2.5, PDF pp. 5–6: smooth Lie groupoid data on
finite-dimensional, boundaryless real manifolds. Multiplication is smooth
on its embedded composable-pair locus; its total value elsewhere is unused.
Source and target are surjective smooth submersions, not merely smooth maps. -/
def IsLieGroupoid {n0 n1 : ℕ} {M : Type u} {A : Type v}
    [TopologicalSpace M] [TopologicalSpace A]
    [ChartedSpace (EuclideanSpace ℝ (Fin n0)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n1)) A]
    (D : GroupoidData M A) : Prop :=
  IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n0))) ∞ M ∧
  IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n1))) ∞ A ∧
  Function.Surjective D.s ∧ Function.Surjective D.t ∧
  Manifold.IsSubmersion (𝓘(ℝ, EuclideanSpace ℝ (Fin n1)))
    (𝓘(ℝ, EuclideanSpace ℝ (Fin n0))) ∞ D.s ∧
  Manifold.IsSubmersion (𝓘(ℝ, EuclideanSpace ℝ (Fin n1)))
    (𝓘(ℝ, EuclideanSpace ℝ (Fin n0))) ∞ D.t ∧
  ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n0)))
    (𝓘(ℝ, EuclideanSpace ℝ (Fin n1))) ∞ D.unit ∧
  ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n1)))
    (𝓘(ℝ, EuclideanSpace ℝ (Fin n1))) ∞ D.inv ∧
  ContMDiffOn ((𝓘(ℝ, EuclideanSpace ℝ (Fin n1))).prod
    (𝓘(ℝ, EuclideanSpace ℝ (Fin n1))))
    (𝓘(ℝ, EuclideanSpace ℝ (Fin n1))) ∞
    (fun p : A × A => D.mul p.1 p.2) (composablePairs D)

/-- Example 2.5, PDF p. 6: all closed arrows, without a smoothness assertion. -/
def Loops {M : Type u} {A : Type v} (D : GroupoidData M A) :=
  {a : A // D.s a = D.t a}

/-- The family map sends a closed arrow to its common endpoint. -/
def loopBase {M : Type u} {A : Type v} (D : GroupoidData M A) : Loops D → M :=
  fun x => D.s x.val

/-- The crossed-module map is the actual inclusion of closed arrows. -/
def loopInclusion {M : Type u} {A : Type v} (D : GroupoidData M A) : Loops D → A :=
  Subtype.val

/-- The identity loop over an object. -/
def loopUnit {M : Type u} {A : Type v} (D : GroupoidData M A) (m : M) : Loops D :=
  ⟨D.unit m, (D.s_unit m).trans (D.t_unit m).symm⟩

/-- Inversion in each isotropy group. -/
def loopInverse {M : Type u} {A : Type v} (D : GroupoidData M A)
    (x : Loops D) : Loops D :=
  ⟨D.inv x.val, by rw [D.s_inv, D.t_inv]; exact x.property.symm⟩

/-- Multiplication is used on loops over the same object. The arbitrary
value on unequal fibres is never used in the family-of-groups axioms. -/
noncomputable def loopMultiply {M : Type u} {A : Type v} (D : GroupoidData M A)
    (x y : Loops D) : Loops D := by
  classical
  exact if h : D.s x.val = D.t y.val then
    ⟨D.mul x.val y.val, by
      rw [D.s_mul _ _ h, D.t_mul _ _ h]
      exact y.property.trans (h.symm.trans x.property)⟩
    else x

/-- Definition 2.3, equations (2),(3), and Example 2.5, PDF pp. 5–6:
the right action is x to gamma inverse times x times gamma, with its exact
source/target domain. Values off that domain are not part of the action. -/
noncomputable def loopConjugate {M : Type u} {A : Type v} (D : GroupoidData M A)
    (x : Loops D) (gamma : A) : Loops D := by
  classical
  exact if h : D.s x.val = D.t gamma then
    ⟨D.mul (D.inv gamma) (D.mul x.val gamma), by
      have hcomp : D.s (D.inv gamma) = D.t (D.mul x.val gamma) := by
        rw [D.s_inv, D.t_mul _ _ h]
        exact h.symm.trans x.property
      rw [D.s_mul _ _ hcomp, D.t_mul _ _ hcomp, D.s_mul _ _ h, D.t_inv]⟩
    else x

/-- Definition 2.3, PDF p. 5: a family of groups over M. There is no
multiplication between different fibres. All unit, associative and inverse
laws, and preservation of the base by the operations, are explicit. -/
def IsGroupFamily {M : Type u} {X : Type w} (p : X → M)
    (unit : M → X) (inv : X → X) (mul : X → X → X) : Prop :=
  (∀ m, p (unit m) = m) ∧
  (∀ x, p (inv x) = p x) ∧
  (∀ x y, p x = p y → p (mul x y) = p x) ∧
  (∀ x, mul (unit (p x)) x = x ∧ mul x (unit (p x)) = x) ∧
  (∀ x, mul (inv x) x = unit (p x) ∧ mul x (inv x) = unit (p x)) ∧
  (∀ x y z, p x = p y → p y = p z → mul (mul x y) z = mul x (mul y z))

/-- Definition 2.3, PDF p. 5: algebraic crossed modules with the paper's
RIGHT action convention. The action is by group automorphisms (inverse
arrows give inverse actions); rho is an identity-on-objects functor.
The last two clauses are exactly equations (2) and (3). -/
def IsRightCrossedModule {M : Type u} {A : Type v} {X : Type w}
    (D : GroupoidData M A) (p : X → M) (unit : M → X)
    (inv : X → X) (mul : X → X → X) (rho : X → A)
    (act : X → A → X) : Prop :=
  IsGroupFamily p unit inv mul ∧
  (∀ x, D.s (rho x) = p x ∧ D.t (rho x) = p x) ∧
  (∀ m, rho (unit m) = D.unit m) ∧
  (∀ x y, p x = p y → rho (mul x y) = D.mul (rho x) (rho y)) ∧
  (∀ x, rho (inv x) = D.inv (rho x)) ∧
  (∀ x gamma, p x = D.t gamma → p (act x gamma) = D.s gamma) ∧
  (∀ x, act x (D.unit (p x)) = x) ∧
  (∀ x gamma delta, p x = D.t gamma → D.s gamma = D.t delta →
    act (act x gamma) delta = act x (D.mul gamma delta)) ∧
  (∀ gamma, act (unit (D.t gamma)) gamma = unit (D.s gamma)) ∧
  (∀ x y gamma, p x = p y → p x = D.t gamma →
    act (mul x y) gamma = mul (act x gamma) (act y gamma)) ∧
  (∀ x gamma, p x = D.t gamma → act (inv x) gamma = inv (act x gamma)) ∧
  (∀ x gamma, p x = D.t gamma →
    rho (act x gamma) = D.mul (D.inv gamma) (D.mul (rho x) gamma)) ∧
  (∀ x y, p x = p y → act x (rho y) = mul (inv y) (mul x y))

/-- Sanity: the loop family of the one-point groupoid has exactly one element. -/
example (x : Loops pointGroupoid) : x = loopUnit pointGroupoid PUnit.unit := by
  apply Subtype.ext
  exact Subsingleton.elim _ _

/-- Sanity: inclusion really includes the identity loop; it is not a free functor. -/
example {M : Type u} {A : Type v} (D : GroupoidData M A) (m : M) :
    loopInclusion D (loopUnit D m) = D.unit m := rfl

/-- Sanity: the family lies over exactly the source endpoint of its loop. -/
example {M : Type u} {A : Type v} (D : GroupoidData M A) (x : Loops D) :
    loopBase D x = D.s (loopInclusion D x) := rfl

/-- Sanity: all the family, functor, action and Peiffer axioms admit the
actual singleton-loop instance; no axiom requires a nontrivial fibre. -/
example : IsRightCrossedModule pointGroupoid (loopBase pointGroupoid)
    (loopUnit pointGroupoid) (loopInverse pointGroupoid)
    (loopMultiply pointGroupoid) (loopInclusion pointGroupoid)
    (loopConjugate pointGroupoid) := by
  letI : Subsingleton (Loops pointGroupoid) := ⟨fun x y => by
    apply Subtype.ext
    exact Subsingleton.elim _ _⟩
  simp only [IsRightCrossedModule, IsGroupFamily]
  repeat' first | constructor | intro
  all_goals exact Subsingleton.elim _ _

end QAlgorithms.Papers.Independent.Intakenext100.P58


