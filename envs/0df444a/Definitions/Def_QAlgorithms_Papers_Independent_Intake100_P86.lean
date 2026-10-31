-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P86
-- name    : QAlgorithms_Papers_Independent_Intake100_P86
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T15:27:14.667177+00:00
-- url     : https://prove2.me/theorems/f47e685a-4297-4044-a1e0-a65a2c6e0793
-- title:
--   Definitions for Constructing cell data for diagram algebras
-- statement:
--   The objects the formalized statements of *Constructing cell data for diagram algebras* (arXiv:math/0503751) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IntegralHypergroup`: Integral hypergroups, Definition 1.2.1, PDF p.9. H3 has the bar on the rightmost factor. The distinguished basis is an actual free Z-basis.
--   - `BasedRingHom`: Unital based homomorphisms, Definition 1.3.1, PDF p.10. Ring homomorphisms preserve the canonical integral algebra structure. Basis elements may be sent to zero.
--   - `BasedRingAutomorphism`: Based automorphisms, Definition 1.3.1, PDF p.10. The ring equivalence permutes the entire distinguished basis, even at infinite rank.
--   - `BasedRingAntiAutomorphism`: Based anti-automorphisms, Definition 1.3.1, PDF pp.10–12. The additive equivalence reverses multiplication and preserves the unit and basis. Its square is not required to be the identity.
--   - `barredAutomorphism`: The map bar(g)=bar composed with g, Definition 1.3.4, PDF p.11.
--   - `integerHypergroup`: The rank-one hypergroup Z with basis {1}, Definition 1.2.1, PDF p.9.
--   - `basedRingIdentity`: Identity based homomorphism, Definition 1.3.1, PDF p.10.
--   - `basedAutomorphismIdentity`: Identity based automorphism, Definition 1.3.1, PDF p.10.
--   - `TabularScalars`: Coefficient ring L=Z[v,v^{-1}], Definition 2.1.1, PDF p.12.
--   - `HypergroupPackage`: A hypergroup with its carrier and basis index, Definition 1.2.1, PDF p.9. Neither of these types is required to be finite.
--   - `TableCandidate`: The candidate tuple (Lambda,Gamma,B,M,C,star), PDF pp.12–14. No A1–A5 equation is assumed here. Labels and half-index sets are finite, as required in Definition 2.1.1; middle bases need not be finite.
--   - `TableIndex`: The disjoint union indexing C in A1, PDF p.12.
--   - `integralCell`: Extend C in its middle integral argument, axiom A2, PDF p.12. The map is computed from the hypergroup coordinates.
--   - `lowerTableSpan`: The strictly lower layer span A(<lambda), axiom A3, PDF pp.12–13.
--   - `IsTableDatum`: A1–A3 for the specified distinguished idempotent family, Definition 2.1.1, PDF pp.12–13. A3 coefficients are chosen before T and g. Finitely supported L-valued middle coordinates represent exactly L tensor_Z Gamma(lambda), since the hypergroup has a free Z-basis.
--   - `topDegreeTriple`: The top-degree triples of A4, PDF p.13. The three entries must lie in the same layer with matching half indices.
--   - `negativeLaurent`: Membership in v^{-1} Z[v^{-1}], axiom A5, PDF p.14: all coefficients at nonnegative exponents vanish.
--   - `HasTabularTrace`: A4–A5, Definition 2.1.3, PDF pp.13–14. The coordinate isomorphism sends the specified C to the coordinate basis. The integer a is an attained maximum bounding every structure coefficient; no default-valued supremum occurs. A5 retains the printed positive exponent in tau(v^{a(X)} X).
--   - `TableSubdatum`: S1–S3 for the given restricted tuple, Definition 2.1.4, PDF p.14. The displayed C spans an actual subalgebra. Neither its A3 condition nor its A4–A5 conditions are assumed.
-- source:
--   Constructing cell data for diagram algebras, arXiv:math/0503751v3, https://arxiv.org/abs/math/0503751v3

import Mathlib

/-!
Green and Martin, Constructing cell data for diagram algebras,
arXiv:math/0503751v3. All substrate below is local to this paper.
Hypergroups are integral normalized table algebras, with possibly infinite
bases. Tabularity uses Laurent scalars and strictly lower layers.
Deferred nodes are recorded in HARD.md and GAPS.json. Compilation and
independent moderation remain pending under the batch handoff.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P86

/-- Integral hypergroups, Definition 1.2.1, PDF p.9. H3 has the bar on
the rightmost factor. The distinguished basis is an actual free Z-basis. -/
structure IntegralHypergroup (A I : Type*) [Ring A] where
  basis : Module.Basis I ℤ A
  oneIndex : I
  basis_one : basis oneIndex = 1
  nonnegative : ∀ i j k, 0 ≤ basis.repr (basis i * basis j) k
  bar : A →ₗ[ℤ] A
  bar_involutive : Function.Involutive bar
  bar_mul : ∀ x y, bar (x * y) = bar y * bar x
  bar_basis : ∀ i, ∃ j, bar (basis i) = basis j
  reciprocity : ∀ i j m,
    basis.repr (basis i * basis j) m = basis.repr (basis m * bar (basis j)) i

/-- Unital based homomorphisms, Definition 1.3.1, PDF p.10.
Ring homomorphisms preserve the canonical integral algebra structure.
Basis elements may be sent to zero. -/
structure BasedRingHom {A I A2 I2 : Type*} [Ring A] [Ring A2]
    (H : IntegralHypergroup A I) (H2 : IntegralHypergroup A2 I2) where
  hom : A →+* A2
  basis_image : ∀ i, hom (H.basis i) = 0 ∨ ∃ j, hom (H.basis i) = H2.basis j

/-- Based automorphisms, Definition 1.3.1, PDF p.10. The ring
equivalence permutes the entire distinguished basis, even at infinite rank. -/
structure BasedRingAutomorphism {A I : Type*} [Ring A]
    (H : IntegralHypergroup A I) where
  equiv : A ≃+* A
  basis_image : Set.range (fun i => equiv (H.basis i)) = Set.range H.basis

/-- Based anti-automorphisms, Definition 1.3.1, PDF pp.10–12.
The additive equivalence reverses multiplication and preserves the unit
and basis. Its square is not required to be the identity. -/
structure BasedRingAntiAutomorphism {A I : Type*} [Ring A]
    (H : IntegralHypergroup A I) where
  equiv : A ≃+ A
  map_one : equiv 1 = 1
  map_mul : ∀ x y, equiv (x * y) = equiv y * equiv x
  basis_image : Set.range (fun i => equiv (H.basis i)) = Set.range H.basis

/-- The map bar(g)=bar composed with g, Definition 1.3.4, PDF p.11. -/
def barredAutomorphism {A I : Type*} [Ring A] (H : IntegralHypergroup A I)
    (g : BasedRingAutomorphism H) (x : A) : A :=
  H.bar (g.equiv x)

/-- The rank-one hypergroup Z with basis {1}, Definition 1.2.1, PDF p.9. -/
def integerHypergroup : IntegralHypergroup ℤ Unit where
  basis := Module.Basis.singleton Unit ℤ
  oneIndex := ()
  basis_one := by simp
  nonnegative := by intro i j k; simp
  bar := LinearMap.id
  bar_involutive := fun _ => rfl
  bar_mul := by intro x y; exact mul_comm x y
  bar_basis := fun i => ⟨i, rfl⟩
  reciprocity := by intro i j m; simp

/-- Identity based homomorphism, Definition 1.3.1, PDF p.10. -/
def basedRingIdentity {A I : Type*} [Ring A] (H : IntegralHypergroup A I) :
    BasedRingHom H H where
  hom := RingHom.id A
  basis_image := fun i => Or.inr ⟨i, rfl⟩

/-- Identity based automorphism, Definition 1.3.1, PDF p.10. -/
def basedAutomorphismIdentity {A I : Type*} [Ring A] (H : IntegralHypergroup A I) :
    BasedRingAutomorphism H where
  equiv := RingEquiv.refl A
  basis_image := rfl

/-- Rank-one normalization: bar fixes every integer. -/
example (z : ℤ) : integerHypergroup.bar z = z := rfl

/-- The homomorphism actually preserves the unit. -/
example {A I : Type*} [Ring A] (H : IntegralHypergroup A I) :
    (basedRingIdentity H).hom 1 = 1 := rfl

/-- The twist has the composition order specified in Definition 1.3.4. -/
example {A I : Type*} [Ring A] (H : IntegralHypergroup A I) (x : A) :
    barredAutomorphism H (basedAutomorphismIdentity H) x = H.bar x := rfl

/-- Coefficient ring L=Z[v,v^{-1}], Definition 2.1.1, PDF p.12. -/
abbrev TabularScalars := LaurentPolynomial ℤ

universe u

/-- A hypergroup with its carrier and basis index, Definition 1.2.1,
PDF p.9. Neither of these types is required to be finite. -/
structure HypergroupPackage where
  Carrier : Type u
  ring : Ring Carrier
  Index : Type u
  data : letI := ring; IntegralHypergroup Carrier Index

attribute [instance] HypergroupPackage.ring

/-- The candidate tuple (Lambda,Gamma,B,M,C,star), PDF pp.12–14.
No A1–A5 equation is assumed here. Labels and half-index sets are finite,
as required in Definition 2.1.1; middle bases need not be finite. -/
structure TableCandidate (A : Type u) [Ring A] [Algebra TabularScalars A] where
  Label : Type u
  labelOrder : PartialOrder Label
  labelFinite : Fintype Label
  gamma : Label → HypergroupPackage.{u}
  Half : Label → Type u
  halfFinite : ∀ l, Fintype (Half l)
  C : (Σ l, Half l × (gamma l).Index × Half l) → A
  star : A →ₗ[TabularScalars] A

attribute [instance] TableCandidate.labelOrder TableCandidate.labelFinite
attribute [instance] TableCandidate.halfFinite

/-- The disjoint union indexing C in A1, PDF p.12. -/
abbrev TableIndex {A : Type u} [Ring A] [Algebra TabularScalars A]
    (D : TableCandidate A) := Σ l, D.Half l × (D.gamma l).Index × D.Half l

/-- Extend C in its middle integral argument, axiom A2, PDF p.12.
The map is computed from the hypergroup coordinates. -/
def integralCell {A : Type u} [Ring A] [Algebra TabularScalars A]
    (D : TableCandidate A) (l : D.Label) (S : D.Half l)
    (g : (D.gamma l).Carrier) (T : D.Half l) : A :=
  ((D.gamma l).data.basis.repr g).sum fun b c => c • D.C ⟨l, S, b, T⟩

/-- The strictly lower layer span A(<lambda), axiom A3, PDF pp.12–13. -/
def lowerTableSpan {A : Type u} [Ring A] [Algebra TabularScalars A]
    (D : TableCandidate A) (l : D.Label) : Submodule TabularScalars A :=
  Submodule.span TabularScalars {a | ∃ z : TableIndex D, z.1 < l ∧ a = D.C z}

/-- A1–A3 for the specified distinguished idempotent family,
Definition 2.1.1, PDF pp.12–13. A3 coefficients are chosen before T and g.
Finitely supported L-valued middle coordinates represent exactly
L tensor_Z Gamma(lambda), since the hypergroup has a free Z-basis. -/
def IsTableDatum {A E : Type u} [Ring A] [Algebra TabularScalars A]
    (D : TableCandidate A) (e : E → A) : Prop :=
  Function.Injective D.C ∧
  LinearIndependent TabularScalars D.C ∧
  Submodule.span TabularScalars (Set.range D.C) = ⊤ ∧
  (∀ i, e i ∈ Set.range D.C) ∧
  (∀ i, e i * e i = e i) ∧
  (∀ i j, i ≠ j → e i * e j = 0) ∧
  Submodule.span TabularScalars {a | ∃ i j x, a = e i * x * e j} = ⊤ ∧
  (∀ z, ∃ i j, D.C z = e i * D.C z * e j) ∧
  Function.Involutive D.star ∧
  (∀ x y, D.star (x * y) = D.star y * D.star x) ∧
  (∀ l (S T : D.Half l) b,
    D.star (D.C ⟨l, S, b, T⟩) =
      integralCell D l T ((D.gamma l).data.bar ((D.gamma l).data.basis b)) S) ∧
  (∀ l (a : A) (S : D.Half l),
    ∃ r : D.Half l → (D.gamma l).Index →₀ TabularScalars,
      ∀ (T : D.Half l) (g : (D.gamma l).Carrier),
        a * integralCell D l S g T -
          ∑ U : D.Half l, (r U).sum (fun b c =>
            c • integralCell D l U ((D.gamma l).data.basis b * g) T)
          ∈ lowerTableSpan D l)

/-- The top-degree triples of A4, PDF p.13. The three entries must
lie in the same layer with matching half indices. -/
def topDegreeTriple {A : Type u} [Ring A] [Algebra TabularScalars A]
    (D : TableCandidate A) (x y z : TableIndex D) : Prop :=
  ∃ (l : D.Label) (S T V : D.Half l) (b c d : (D.gamma l).Index),
    x = ⟨l, S, b, T⟩ ∧ y = ⟨l, T, c, V⟩ ∧ z = ⟨l, S, d, V⟩ ∧
      (D.gamma l).data.basis.repr
        ((D.gamma l).data.basis b * (D.gamma l).data.basis c) d ≠ 0

/-- Membership in v^{-1} Z[v^{-1}], axiom A5, PDF p.14:
all coefficients at nonnegative exponents vanish. -/
def negativeLaurent (p : TabularScalars) : Prop :=
  ∀ k : ℤ, 0 ≤ k → p.coeff k = 0

/-- A4–A5, Definition 2.1.3, PDF pp.13–14. The coordinate isomorphism
sends the specified C to the coordinate basis. The integer a is an attained
maximum bounding every structure coefficient; no default-valued supremum
occurs. A5 retains the printed positive exponent in tau(v^{a(X)} X). -/
def HasTabularTrace {A : Type u} [Ring A] [Algebra TabularScalars A]
    (D : TableCandidate A) : Prop :=
  ∃ coord : A ≃ₗ[TabularScalars] (TableIndex D →₀ TabularScalars),
    (∀ z, coord (D.C z) = Finsupp.single z 1) ∧
    ∃ a : TableIndex D → ℤ,
      (∀ x y z, LaurentPolynomial.degree (coord (D.C x * D.C y) z) ≤
        (a z : WithBot ℤ)) ∧
      (∀ z, ∃ x y, LaurentPolynomial.degree (coord (D.C x * D.C y) z) =
        (a z : WithBot ℤ)) ∧
      (∀ x y z, LaurentPolynomial.degree (coord (D.C x * D.C y) z) =
        (a z : WithBot ℤ) ↔ topDegreeTriple D x y z) ∧
      (∀ l (S T V : D.Half l),
        let b := (D.gamma l).data.oneIndex
        (coord (D.C ⟨l, S, b, T⟩ * D.C ⟨l, T, b, V⟩) ⟨l, S, b, V⟩).coeff
          (a ⟨l, S, b, V⟩) = 1) ∧
      ∃ tau : A →ₗ[TabularScalars] TabularScalars,
        (∀ x, tau x = tau (D.star x)) ∧
        (∀ x y, tau (x * y) = tau (y * x)) ∧
        (∀ l (S T : D.Half l) (b : (D.gamma l).Index),
          negativeLaurent (tau ((LaurentPolynomial.T (a ⟨l, S, b, T⟩) : TabularScalars) •
            D.C ⟨l, S, b, T⟩) - if S = T ∧ b = (D.gamma l).data.oneIndex then 1 else 0))

/-- S1–S3 for the given restricted tuple, Definition 2.1.4, PDF p.14.
The displayed C spans an actual subalgebra. Neither its A3 condition nor
its A4–A5 conditions are assumed. -/
structure TableSubdatum {A : Type u} [Ring A] [Algebra TabularScalars A]
    (D : TableCandidate A) (A2 : Subalgebra TabularScalars A)
    (D2 : TableCandidate A2) where
  label : D2.Label ↪o D.Label
  half : ∀ l, D2.Half l ↪ D.Half (label l)
  middle : ∀ l, BasedRingHom (D2.gamma l).data (D.gamma (label l)).data
  middle_injective : ∀ l, Function.Injective (middle l).hom
  middleIndex : ∀ l, (D2.gamma l).Index ↪ (D.gamma (label l)).Index
  middle_basis : ∀ l b,
    (middle l).hom ((D2.gamma l).data.basis b) =
      (D.gamma (label l)).data.basis (middleIndex l b)
  C_restrict : ∀ l (S T : D2.Half l) b,
    (D2.C ⟨l, S, b, T⟩ : A) = D.C ⟨label l, half l S, middleIndex l b, half l T⟩
  star_restrict : ∀ x : A2, (D2.star x : A) = D.star (x : A)
  span : Submodule.span TabularScalars (Set.range D2.C) = ⊤

/-- The middle-coordinate extension sends zero to zero. -/
example {A : Type u} [Ring A] [Algebra TabularScalars A]
    (D : TableCandidate A) (l : D.Label) (S T : D.Half l) :
    integralCell D l S 0 T = 0 := by
  simp [integralCell]

/-- Zero satisfies the strictly negative-power remainder condition. -/
example : negativeLaurent 0 := by
  intro k hk
  simp

/-- A constant unit is not an admissible negative-power remainder. -/
example : ¬ negativeLaurent 1 := by
  intro h
  have h0 := h 0 le_rfl
  simpa using h0

/-- A minimal layer has no lower cells: the order direction is fixed. -/
example {A : Type u} [Ring A] [Algebra TabularScalars A]
    (D : TableCandidate A) (l : D.Label) (hl : ∀ m : D.Label, ¬ m < l) :
    lowerTableSpan D l = ⊥ := by
  have h : {a : A | ∃ z : TableIndex D, z.1 < l ∧ a = D.C z} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨z, hz, _⟩ := ha
    exact hl z.1 hz
  rw [lowerTableSpan, h, Submodule.span_empty]

end QAlgorithms.Papers.Independent.Intake100.P86


