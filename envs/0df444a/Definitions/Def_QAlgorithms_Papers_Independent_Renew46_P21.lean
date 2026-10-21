-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P21
-- name    : QAlgorithms_Papers_Independent_Renew46_P21
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T20:24:59.393071+00:00
-- url     : https://prove2.me/theorems/626f9d91-8d3d-4016-86cb-32f57a4d2920
-- title:
--   Definitions for On the irreducible representations of a finite semigroup
-- statement:
--   The objects the formalized statements of *On the irreducible representations of a finite semigroup* (arXiv:0712.2076) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `principalIdeal`: The two-sided ideal S¹sS¹, with an identity adjoined even when S has one (p. 2).
--   - `greenClass`: Green's J-class of an element, by equality of principal two-sided ideals (p. 2).
--   - `JClass`: An actual J-class, rather than an arbitrary subset of S (p. 2).
--   - `classIdeal`: I_J consists of the elements not J-above the class J (p. 2).
--   - `RegularClass`: A regular class contains an idempotent; in finite S this is Fact 2 (p. 2).
--   - `RightSemigroupAction`: A K-linear right S-action, equivalently a right action of the possibly nonunital semigroup algebra KS (pp. 2--3). Simplicity below includes nonzero algebra action; for such modules any identity of KS necessarily acts as the identity.
--   - `SemigroupInvariant`: The K-submodules stable under the right S-action are exactly KS-submodules (p. 3).
--   - `SemigroupSimple`: Simple means MA ≠ 0 and no proper nonzero submodules, as in the paper (p. 3). The nonzero-action clause excludes both the zero module and zero representations.
--   - `semigroupAnnihilator`: The semigroup annihilator Ann_S(M), not the annihilator ideal in KS (p. 3).
--   - `HasApex`: Definition 4: a regular J-class with Ann_S(M) = I_J (p. 3).
--   - `scalarCharacter`: The scalar character of (2.2): zero on I_J and one on its complement (p. 7). Multiplicativity is a conclusion of the classification, not part of this definition.
--   - `ScalarModel`: Isomorphism to the one-dimensional right representation of (2.2). The linear equivalence, rather than equality of carriers, expresses module isomorphism (p. 7).
--   - `OnlyTrivialSubgroups`: Every subgroup is trivial, including groups embedded at nonidentity idempotents (p. 8). An injective multiplicative map from a group has precisely a subgroup as its image; no identity of S is required. The group universe can equal that of its image in S.
--   - `RightAlgebraAction`: A K-linear right action of a possibly nonunital associative algebra A (pp. 2--4). The conditional unit law imposes the paper's unital-module convention whenever A has an identity, without adjoining an identity to A.
--   - `AlgebraInvariant`: A-submodules are K-submodules invariant under every right action map (p. 4).
--   - `cornerAnnihilator`: N(M) = {m | mAe = 0}, as an intersection of kernels of K-linear maps (p. 4).
--   - `cornerGenerated`: L(M) = MeA means the K-span of all (me)a, not just the raw product set (p. 4).
-- source:
--   On the irreducible representations of a finite semigroup, arXiv:0712.2076v2, https://arxiv.org/abs/0712.2076v2

import Mathlib

/-!
Statements from Ganyushkin--Mazorchuk--Steinberg, arXiv:0712.2076v2.
Local definitions use actual K-linear right actions, including nonunital actions.
The induction/coinduction and coordinate nodes are explicitly deferred in HARD.md.
-/

namespace QAlgorithms.Papers.Independent.Renew46.P21

universe u v w

/-- The two-sided ideal S¹sS¹, with an identity adjoined even when S has one (p. 2). -/
def principalIdeal {S : Type v} [Semigroup S] (s : S) : Set S :=
  {t | ∃ a b : WithOne S, (t : WithOne S) = a * (s : WithOne S) * b}

/-- Green's J-class of an element, by equality of principal two-sided ideals (p. 2). -/
def greenClass {S : Type v} [Semigroup S] (s : S) : Set S :=
  {t | principalIdeal t = principalIdeal s}

/-- An actual J-class, rather than an arbitrary subset of S (p. 2). -/
def JClass (S : Type v) [Semigroup S] :=
  {J : Set S // ∃ s : S, J = greenClass s}

/-- I_J consists of the elements not J-above the class J (p. 2). -/
def classIdeal {S : Type v} [Semigroup S] (J : JClass S) : Set S :=
  {s | ¬ J.val ⊆ principalIdeal s}

/-- A regular class contains an idempotent; in finite S this is Fact 2 (p. 2). -/
def RegularClass {S : Type v} [Semigroup S] (J : JClass S) : Prop :=
  ∃ e : S, e ∈ J.val ∧ e * e = e

/-- A K-linear right S-action, equivalently a right action of the possibly nonunital
semigroup algebra KS (pp. 2--3). Simplicity below includes nonzero algebra action;
for such modules any identity of KS necessarily acts as the identity. -/
structure RightSemigroupAction (K : Type u) (S : Type v) (M : Type w)
    [CommRing K] [Semigroup S] [AddCommGroup M] [Module K M] where
  act : S → Module.End K M
  mul_apply : ∀ (s t : S) (m : M), act (s * t) m = act t (act s m)

/-- The K-submodules stable under the right S-action are exactly KS-submodules (p. 3). -/
def SemigroupInvariant {K : Type u} {S : Type v} {M : Type w}
    [CommRing K] [Semigroup S] [AddCommGroup M] [Module K M]
    (rho : RightSemigroupAction K S M) (U : Submodule K M) : Prop :=
  ∀ (s : S) (m : M), m ∈ U → rho.act s m ∈ U

/-- Simple means MA ≠ 0 and no proper nonzero submodules, as in the paper (p. 3).
The nonzero-action clause excludes both the zero module and zero representations. -/
def SemigroupSimple {K : Type u} {S : Type v} {M : Type w}
    [CommRing K] [Semigroup S] [AddCommGroup M] [Module K M]
    (rho : RightSemigroupAction K S M) : Prop :=
  (∃ (s : S) (m : M), rho.act s m ≠ 0) ∧
    ∀ U : Submodule K M, SemigroupInvariant rho U → U = ⊥ ∨ U = ⊤

/-- The semigroup annihilator Ann_S(M), not the annihilator ideal in KS (p. 3). -/
def semigroupAnnihilator {K : Type u} {S : Type v} {M : Type w}
    [CommRing K] [Semigroup S] [AddCommGroup M] [Module K M]
    (rho : RightSemigroupAction K S M) : Set S :=
  {s | ∀ m : M, rho.act s m = 0}

/-- Definition 4: a regular J-class with Ann_S(M) = I_J (p. 3). -/
def HasApex {K : Type u} {S : Type v} {M : Type w}
    [CommRing K] [Semigroup S] [AddCommGroup M] [Module K M]
    (rho : RightSemigroupAction K S M) (J : JClass S) : Prop :=
  RegularClass J ∧ semigroupAnnihilator rho = classIdeal J

/-- The scalar character of (2.2): zero on I_J and one on its complement (p. 7).
Multiplicativity is a conclusion of the classification, not part of this definition. -/
noncomputable def scalarCharacter (K : Type u) {S : Type v}
    [CommRing K] [Semigroup S] (J : JClass S) : S → K := by
  classical
  exact fun s => if s ∈ classIdeal J then 0 else 1

/-- Isomorphism to the one-dimensional right representation of (2.2).
The linear equivalence, rather than equality of carriers, expresses module isomorphism (p. 7). -/
def ScalarModel {K : Type u} {S : Type v} {M : Type w}
    [Field K] [Semigroup S] [AddCommGroup M] [Module K M]
    (rho : RightSemigroupAction K S M) (J : JClass S) : Prop :=
  ∃ f : M ≃ₗ[K] K, ∀ (s : S) (m : M),
    f (rho.act s m) = scalarCharacter K J s * f m

/-- Every subgroup is trivial, including groups embedded at nonidentity idempotents (p. 8).
An injective multiplicative map from a group has precisely a subgroup as its image;
no identity of S is required. The group universe can equal that of its image in S. -/
def OnlyTrivialSubgroups (S : Type v) [Semigroup S] : Prop :=
  ∀ (G : Type v) [Group G] (f : G →ₙ* S), Function.Injective f → Subsingleton G

/-- The scalar formula retains the zero branch at every element of I_J. -/
example {K : Type u} {S : Type v} [CommRing K] [Semigroup S]
    (J : JClass S) (s : S) (hs : s ∈ classIdeal J) : scalarCharacter K J s = 0 := by
  classical
  simp [scalarCharacter, hs]

/-- The scalar formula retains the one branch on the complement of I_J. -/
example {K : Type u} {S : Type v} [CommRing K] [Semigroup S]
    (J : JClass S) (s : S) (hs : s ∉ classIdeal J) : scalarCharacter K J s = 1 := by
  classical
  simp [scalarCharacter, hs]

/-- Every s belongs to its S¹-generated ideal, including in a nonunital semigroup. -/
example {S : Type v} [Semigroup S] (s : S) : s ∈ principalIdeal s := by
  exact ⟨1, 1, by simp⟩

/-- The class of an idempotent is regular, without a finiteness assumption. -/
example {S : Type v} [Semigroup S] (e : S) (he : e * e = e) :
    RegularClass (⟨greenClass e, ⟨e, rfl⟩⟩ : JClass S) := by
  exact ⟨e, rfl, he⟩

/-- A right action composes in the opposite order from left endomorphism multiplication. -/
example {K : Type u} {S : Type v} {M : Type w}
    [CommRing K] [Semigroup S] [AddCommGroup M] [Module K M]
    (rho : RightSemigroupAction K S M) (s t : S) (m : M) :
    rho.act t (rho.act s m) = rho.act (s * t) m := by
  exact (rho.mul_apply s t m).symm

/-- The paper's simplicity convention excludes the zero module. -/
example {K : Type u} {S : Type v} {M : Type w}
    [CommRing K] [Semigroup S] [AddCommGroup M] [Module K M] [Subsingleton M]
    (rho : RightSemigroupAction K S M) : ¬ SemigroupSimple rho := by
  rintro ⟨⟨s, m, h⟩, _⟩
  exact h (Subsingleton.elim _ _)

/-- A K-linear right action of a possibly nonunital associative algebra A (pp. 2--4).
The conditional unit law imposes the paper's unital-module convention whenever
A has an identity, without adjoining an identity to A. -/
structure RightAlgebraAction (K : Type u) (A : Type v) (M : Type w)
    [CommRing K] [NonUnitalRing A] [Module K A] [AddCommGroup M] [Module K M] where
  act : A →ₗ[K] Module.End K M
  mul_apply : ∀ (a b : A) (m : M), act (a * b) m = act b (act a m)
  unit_apply : ∀ u : A, (∀ a : A, u * a = a ∧ a * u = a) → ∀ m : M, act u m = m

/-- A-submodules are K-submodules invariant under every right action map (p. 4). -/
def AlgebraInvariant {K : Type u} {A : Type v} {M : Type w}
    [CommRing K] [NonUnitalRing A] [Module K A] [AddCommGroup M] [Module K M]
    (rho : RightAlgebraAction K A M) (U : Submodule K M) : Prop :=
  ∀ (a : A) (m : M), m ∈ U → rho.act a m ∈ U

/-- N(M) = {m | mAe = 0}, as an intersection of kernels of K-linear maps (p. 4). -/
def cornerAnnihilator {K : Type u} {A : Type v} {M : Type w}
    [CommRing K] [NonUnitalRing A] [Module K A] [AddCommGroup M] [Module K M]
    (rho : RightAlgebraAction K A M) (e : A) : Submodule K M :=
  ⨅ a : A, LinearMap.ker (rho.act (a * e))

/-- L(M) = MeA means the K-span of all (me)a, not just the raw product set (p. 4). -/
def cornerGenerated {K : Type u} {A : Type v} {M : Type w}
    [CommRing K] [NonUnitalRing A] [Module K A] [AddCommGroup M] [Module K M]
    (rho : RightAlgebraAction K A M) (e : A) : Submodule K M :=
  Submodule.span K (Set.range (fun p : M × A => rho.act p.2 (rho.act e p.1)))

/-- At the zero idempotent every element is annihilated by Ae. -/
example {K : Type u} {A : Type v} {M : Type w}
    [CommRing K] [NonUnitalRing A] [Module K A] [AddCommGroup M] [Module K M]
    (rho : RightAlgebraAction K A M) : cornerAnnihilator rho 0 = ⊤ := by
  ext m
  simp [cornerAnnihilator]

end QAlgorithms.Papers.Independent.Renew46.P21


