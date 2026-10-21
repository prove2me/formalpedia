-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08
-- name    : QAlgorithms_Papers_Independent_Support21_P08
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T04:19:01.538012+00:00
-- url     : https://prove2.me/theorems/321d322a-be27-471f-8937-28952e0408bc
-- title:
--   Definitions for Seminormal forms and Gram determinants for cellular algebras
-- statement:
--   The objects the formalized statements of *Seminormal forms and Gram determinants for cellular algebras* (arXiv:math/0604108) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CellTableau`: Tableaux retain their shape: the disjoint union on PDF p.3.
--   - `higherSpan`: Higher cell span A^lambda, Definition 2.1(b), PDF p.3.
--   - `CellDatum`: Exact cellular datum, Definition 2.1, PDF pp.2–3. The multiplication coefficients are independent of the row index.
--   - `cellAct`: Right cell-module action computed from the basis coordinates, PDF p.3. On an empty cell the coordinate space is zero and this returns zero.
--   - `gramEntry`: Cell Gram entry computed by (2.3), PDF p.3; no form is postulated.
--   - `cellForm`: The symmetric bilinear cell form (2.3), in its original cell basis.
--   - `gramDet`: The Gram determinant in the original cellular basis, PDF p.12.
--   - `JMFamily`: The JM axioms of Definition 2.4, PDF pp.3–4; nothing jmSpectralProjector is assumed.
--   - `tabDominates`: Global weak dominance on tableaux, PDF p.3; higher shapes dominate.
--   - `separatesComparable`: Printed comparable-pair separation, Definition 2.8, PDF p.4.
--   - `separatesAll`: Injective complete content sequences: the stronger reading used on PDF p.10.
--   - `pairDominates`: Strict componentwise pair dominance, PDF p.9.
--   - `IsCellularFamily`: A displayed family is a cellular basis for the same involution and cell order. This is a conclusion predicate, not an extra hypothesis.
--   - `ZeroCellRadical`: Zero radical of the computed cell form, PDF p.3.
--   - `IrreducibleCell`: Irreducibility for the actual right action, rather than just a dimension.
--   - `contents`: Distinct possible contents at one position, PDF p.9.
--   - `jmSpectralProjector`: Spectral product F_t, Definition 3.1, PDF p.9. All scalar denominators exclude the matching content. Products are ordered lists because A need not be commutative; the JM axioms make the order immaterial.
--   - `seminormal`: f_st = F_s a_st F_t, Definition 3.1, PDF p.9.
--   - `seminormalGamma`: Gamma_t is a computed structure coefficient, not a free scalar satisfying Theorem 3.7: unitriangularity identifies this a_tt coefficient with the f_tt coefficient in f_tt squared, PDF p.11.
--   - `cellVector`: The original coordinate vector a_t of a cell module.
--   - `seminormalVector`: The seminormal vector a_t F_t in the original cell module, PDF p.12.
--   - `seminormalBasis`: A fallback only off the basis locus. Under Lemma 3.3 this is the uniquely indexed seminormal basis; it is not assumed in any theorem.
--   - `extendedForm`: Extension of the cell forms by mutually orthogonal row summands, Remark 3.13, PDF p.13. Each row sends f_st to the computed vector a_t F_t.
--   - `rightIdealSpan`: The right ideal f A as a K-subspace.
--   - `CellRightIso`: Right-module isomorphism C(lambda) ≅ I, explicitly including the action.
--   - `SplitSemisimple`: Split semisimple means a finite product of full matrix K-algebras. A mere semisimple-ring predicate would lose the split conclusion.
--   - `Central`: Centrality is literal commutation with every algebra element.
--   - `PrimitiveCentralIdempotent`: Nonzero primitive CENTRAL idempotent: decompositions are central too.
--   - `CompleteOrthogonalIdempotents`: Completeness and both directions of orthogonality.
--   - `shapeProjector`: Shape projector, Theorem 3.16(b), PDF p.13.
--   - `jmAlgebra`: The generated JM subalgebra, paragraph 2.6, PDF p.4.
--   - `MaximalAbelian`: Commutativity and maximality among commutative K-subalgebras.
--   - `jmGenerator`: The generator viewed inside the generated subalgebra, paragraph 2.6.
--   - `IrreducibleRepresentation`: Irreducibility of a representation means nonzero and no proper nonzero invariant K-subspace. No finite-dimensional restriction is silently added.
--   - `newtonPolynomial`: The literal monic defining polynomial of Example 2.14, PDF p.6.
--   - `NewtonAlgebra`: The canonical quotient R[X]/prod(X-c_i) of Example 2.14.
--   - `newtonVector`: a_{i+1}=prod_{j<i}(x-c_{j+1}); i=n includes the zero boundary vector. No arbitrary quotient basis is substituted for this computed family.
--   - `sameResidue`: Complete residue-sequence equality uses the canonical quotient map, Definition 4.1, PDF p.15.
--   - `ModularSystem`: A modular system with the SAME cellular R-form, its fraction-field form, and canonical residue specialization. Module.Basis compatibility pins both scalar extensions; coefficient compatibility pins the canonical reduction.
--   - `genericClassSum`: The actual generic class sum, before asserting its integrality.
--   - `integralLift`: Lift through the inclusion only on its image. The zero fallback off that image is explicit; 4.2 proves that it is never used for class sums.
--   - `reducedClassProjector`: G_[t] is reduced from the generic class SUM after integrality (4.2), not from individual potentially nonintegral F_t. Definition 4.3, p.16.
--   - `reducedCellVector`: The cell vector g_t=a_t G_[t] in the ORIGINAL specialized cell module. This is the interpretation used in the proof of 4.9, PDF pp.18–19; it does not identify an arbitrary possibly scaled fixed-row quotient with C(lambda).
--   - `residuallyLinked`: Residual linkage is the EQUIVALENCE CLOSURE of sharing a residue class, not just the one-step sharing relation. Definition 4.1(b), PDF p.15.
--   - `CellsSameBlock`: Cell modules in the same block are nonzero modules supported by the same primitive CENTRAL idempotent. This does not confuse blocks with arbitrary residue-linkage components, which need not be indecomposable.
--   - `orderedPolynomialEval`: Ordered monomial evaluation in a possibly noncommutative target. The reduced JM elements commute, so this is the usual polynomial evaluation.
--   - `SymmetricPolynomial`: Symmetry under EVERY permutation of the variables.
--   - `HasShape`: Matrix shape J, Soriano Appendix §1, PDF p.24. Nonempty J is part of this predicate; support is contained in the interval-union u_J.
--   - `TriangularSystem`: The represented upper triangular operators of Appendix §1, PDF pp.23–24. No pairwise commutation or faithful original representation is imposed.
--   - `triangularDiagonalEntry`: Diagonal residues, tied to the actual represented matrix.
--   - `UnitSeparating`: Appendix separating condition (S), PDF p.25: unit differences, not merely distinct residues over a domain.
--   - `SeparatingChoices`: Fixed separating choices and an ordered list of factors at each i. They are construction data; idempotence is not assumed. Appendix §3, p.25.
--   - `interpolation`: Ordered interpolation product Z_i, Appendix §3, PDF p.25. Only the represented matrices are multiplied.
--   - `directedProjector`: E^i = Z_i^d, Appendix §3, PDF p.25.
--   - `DirectedFamily`: Directedness has the larger index on the LEFT, Definition 3.2, p.26.
--   - `linked`: Local linkage is equality of the full triangularDiagonalEntry residue sequence, Appendix Definition 5.1, PDF pp.27–28.
--   - `linkageClass`: The actual nonempty linkage class of a basis index.
--   - `linkagePartition`: Distinct classes form the quotient index set; repeated classes are removed.
--   - `representedAlgebra`: Appendix projectors live in the MATRIX algebra generated by the represented operators. This does not pull them back through a nonfaithful representation.
--   - `ClassProjectors`: Full class-projector conclusion in Appendix 6.1–6.2: shaped, generated, complete and orthogonal. No defective printed nonsingleton Z_J is used.
--   - `regularMatrix`: The left regular representation relative to a chosen basis. This is used only when conclusions are about the ORIGINAL algebra, Appendix Remark 6.2.
--   - `regularSystem`: An explicitly triangular regular family, with no assumption on its centre.
--   - `epsilon`: Epsilon_N(x) = sum_{i=0}^{N-1} binom(2N-1,i) x^(2N-1-i)(1-x)^i, Appendix §2, PDF pp.24–25. Natural coefficients are central in every ring.
--   - `TwoSidedNilpotent`: Two-sidedness and I^N=0, expressed directly in an arbitrary unital ring. Products of N elements of I vanish. No commutative ideal instance is used.
--   - `OrthogonalStage`: The two sets in Appendix Lemma 4.1, PDF p.26, encoded as prefix/tail. The tail is directed; the prefix is orthogonal in both directions.
--   - `orthogonalStep`: One exact noncommutative Gram–Schmidt step, Appendix Lemma 4.1.
-- source:
--   Seminormal forms and Gram determinants for cellular algebras, arXiv:math/0604108v4, https://arxiv.org/abs/math/0604108v4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P16
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P12

/-!
Statements from Mathas, arXiv:math/0604108v4, with Soriano's appendix.
The cell-index type and primitive-idempotent predicate are imported from the
pinned accepted library; all remaining substrate below is local to this paper. Cell modules are coordinate spaces
with their computed RIGHT action; module isomorphisms explicitly intertwine
that action. Field-level statements use the scalar-extended cell datum, so the
coefficient domain can be taken to be the field itself. Integral conclusions
also carry the original domain, its fraction field, and a basis-compatible map.

`separatesComparable` is printed Definition 2.8. `separatesAll` is the stronger
injectivity reading actually used on p.10. Every affected theorem discloses it.
The invalid full Theorem 3.12 and modular claims 4.4 and 4.8 are not asserted.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)
open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

/-- Tableaux retain their shape: the disjoint union on PDF p.3. -/
abbrev CellTableau (Shape : Type*) (T : Shape → Type*) := Σ l, T l

section CellularDefinitions

variable {R A Shape : Type*} [CommRing R] [Ring A] [Algebra R A]
variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}
variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]

/-- Higher cell span A^lambda, Definition 2.1(b), PDF p.3. -/
def higherSpan (a : CellIndex Shape T → A) (l : Shape) : Submodule R A :=
  Submodule.span R {x | ∃ (m : Shape) (s t : T m), l < m ∧ x = a ⟨m, (s, t)⟩}

/-- Exact cellular datum, Definition 2.1, PDF pp.2–3.
The multiplication coefficients are independent of the row index. -/
structure CellDatum {R A Shape : Type*} [CommRing R] [Ring A] [Algebra R A]
    [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}
    [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)] where
  basis : Module.Basis (CellIndex Shape T) R A
  star : A →ₗ[R] A
  star_involutive : Function.Involutive star
  star_mul : ∀ x y, star (x * y) = star y * star x
  star_basis : ∀ l (s t : T l), star (basis ⟨l, (s, t)⟩) = basis ⟨l, (t, s)⟩
  multiplication : ∀ l (t : T l) (x : A), ∃ r : T l → R, ∀ s : T l,
    basis ⟨l, (s, t)⟩ * x - ∑ v : T l, r v • basis ⟨l, (s, v)⟩ ∈
      higherSpan (R := R) basis l

/-- Right cell-module action computed from the basis coordinates, PDF p.3.
On an empty cell the coordinate space is zero and this returns zero. -/
def cellAct (D : CellDatum (R := R) (A := A) (T := T)) (l : Shape)
    (v : T l → R) (x : A) : T l → R := by
  classical
  exact if h : Nonempty (T l) then
    fun u => ∑ t : T l, v t *
      D.basis.repr (D.basis ⟨l, (Classical.choice h, t)⟩ * x)
        ⟨l, (Classical.choice h, u)⟩
  else 0

/-- Cell Gram entry computed by (2.3), PDF p.3; no form is postulated. -/
def gramEntry (D : CellDatum (R := R) (A := A) (T := T)) (l : Shape)
    (t u : T l) : R :=
  D.basis.repr (D.basis ⟨l, (t, t)⟩ * D.basis ⟨l, (u, t)⟩) ⟨l, (t, t)⟩

/-- The symmetric bilinear cell form (2.3), in its original cell basis. -/
def cellForm (D : CellDatum (R := R) (A := A) (T := T)) (l : Shape)
    (v w : T l → R) : R :=
  ∑ t : T l, ∑ u : T l, v t * w u * gramEntry D l t u

/-- The Gram determinant in the original cellular basis, PDF p.12. -/
def gramDet (D : CellDatum (R := R) (A := A) (T := T)) (l : Shape) : R :=
  Matrix.det (gramEntry D l)

/-- The JM axioms of Definition 2.4, PDF pp.3–4; nothing jmSpectralProjector is assumed. -/
structure JMFamily (D : CellDatum (R := R) (A := A) (T := T)) (M : ℕ) where
  L : Fin M → A
  content : CellTableau Shape T → Fin M → R
  commuting : ∀ i j, L i * L j = L j * L i
  fixed : ∀ i, D.star (L i) = L i
  triangular : ∀ l (t : T l) i, ∃ r : T l → R, ∀ s : T l,
    D.basis ⟨l, (s, t)⟩ * L i - content ⟨l, t⟩ i • D.basis ⟨l, (s, t)⟩ -
      ∑ v ∈ Finset.univ.filter (fun v : T l => t < v),
        r v • D.basis ⟨l, (s, v)⟩ ∈ higherSpan (R := R) D.basis l

/-- Global weak dominance on tableaux, PDF p.3; higher shapes dominate. -/
def tabDominates (x y : CellTableau Shape T) : Prop :=
  y.1 < x.1 ∨ ∃ (l : Shape) (s t : T l), x = ⟨l, s⟩ ∧ y = ⟨l, t⟩ ∧ t ≤ s

/-- Printed comparable-pair separation, Definition 2.8, PDF p.4. -/
def separatesComparable {D : CellDatum (R := R) (A := A) (T := T)} {M : ℕ}
    (J : JMFamily D M) : Prop :=
  ∀ s t, tabDominates s t → s ≠ t → ∃ i, J.content s i ≠ J.content t i

/-- Injective complete content sequences: the stronger reading used on PDF p.10. -/
def separatesAll {D : CellDatum (R := R) (A := A) (T := T)} {M : ℕ}
    (J : JMFamily D M) : Prop := Function.Injective J.content

/-- Strict componentwise pair dominance, PDF p.9. -/
def pairDominates (x y : CellIndex Shape T) : Prop :=
  tabDominates ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩ ∧
  tabDominates ⟨x.1, x.2.2⟩ ⟨y.1, y.2.2⟩ ∧ x ≠ y

/-- A displayed family is a cellular basis for the same involution and cell order.
This is a conclusion predicate, not an extra hypothesis. -/
def IsCellularFamily (D : CellDatum (R := R) (A := A) (T := T))
    (a : CellIndex Shape T → A) : Prop :=
  ∃ E : CellDatum (R := R) (A := A) (T := T),
    (∀ z, E.basis z = a z) ∧ E.star = D.star

/-- Zero radical of the computed cell form, PDF p.3. -/
def ZeroCellRadical (D : CellDatum (R := R) (A := A) (T := T)) (l : Shape) : Prop :=
  ∀ v : T l → R, (∀ w, cellForm D l v w = 0) → v = 0

/-- Irreducibility for the actual right action, rather than just a dimension. -/
def IrreducibleCell (D : CellDatum (R := R) (A := A) (T := T)) (l : Shape) : Prop :=
  (∃ v : T l → R, v ≠ 0) ∧
  ∀ S : Submodule R (T l → R),
    (∀ v ∈ S, ∀ x : A, cellAct D l v x ∈ S) → S = ⊥ ∨ S = ⊤

end CellularDefinitions

section SeparatedDefinitions

variable {K A Shape : Type*} [Field K] [Ring A] [Algebra K A]
variable [Fintype Shape] [PartialOrder Shape] {T : Shape → Type*}
variable [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]
variable {D : CellDatum (R := K) (A := A) (T := T)} {M : ℕ}

/-- Distinct possible contents at one position, PDF p.9. -/
def contents (J : JMFamily D M) (i : Fin M) : Finset K := by
  classical
  exact Finset.univ.image (fun t => J.content t i)

/-- Spectral product F_t, Definition 3.1, PDF p.9.
All scalar denominators exclude the matching content. Products are ordered
lists because A need not be commutative; the JM axioms make the order immaterial. -/
def jmSpectralProjector (J : JMFamily D M) (t : CellTableau Shape T) : A := by
  classical
  exact (List.ofFn (fun i : Fin M =>
    (((contents J i).erase (J.content t i)).toList.map (fun c =>
      (J.content t i - c)⁻¹ • (J.L i - algebraMap K A c))).prod)).prod

/-- f_st = F_s a_st F_t, Definition 3.1, PDF p.9. -/
def seminormal (J : JMFamily D M) (z : CellIndex Shape T) : A :=
  jmSpectralProjector J ⟨z.1, z.2.1⟩ * D.basis z * jmSpectralProjector J ⟨z.1, z.2.2⟩

/-- Gamma_t is a computed structure coefficient, not a free scalar satisfying
Theorem 3.7: unitriangularity identifies this a_tt coefficient with the f_tt
coefficient in f_tt squared, PDF p.11. -/
def seminormalGamma (J : JMFamily D M) (t : CellTableau Shape T) : K :=
  D.basis.repr (seminormal J ⟨t.1, (t.2, t.2)⟩ *
    seminormal J ⟨t.1, (t.2, t.2)⟩) ⟨t.1, (t.2, t.2)⟩

/-- The original coordinate vector a_t of a cell module. -/
def cellVector (l : Shape) (t : T l) : T l → K := by
  classical
  exact fun u => if u = t then 1 else 0

/-- The seminormal vector a_t F_t in the original cell module, PDF p.12. -/
def seminormalVector (J : JMFamily D M) (l : Shape) (t : T l) : T l → K :=
  cellAct D l (cellVector l t) (jmSpectralProjector J ⟨l, t⟩)

/-- A fallback only off the basis locus. Under Lemma 3.3 this is the uniquely
indexed seminormal basis; it is not assumed in any theorem. -/
def seminormalBasis (J : JMFamily D M) : Module.Basis (CellIndex Shape T) K A := by
  classical
  exact if h : ∃ b : Module.Basis (CellIndex Shape T) K A, ∀ z, b z = seminormal J z
    then Classical.choose h else D.basis

/-- Extension of the cell forms by mutually orthogonal row summands,
Remark 3.13, PDF p.13. Each row sends f_st to the computed vector a_t F_t. -/
def extendedForm (J : JMFamily D M) (x y : A) : K :=
  ∑ l : Shape, ∑ s : T l, ∑ t : T l, ∑ u : T l,
    (seminormalBasis J).repr x ⟨l, (s, t)⟩ *
    (seminormalBasis J).repr y ⟨l, (s, u)⟩ *
    cellForm D l (seminormalVector J l t) (seminormalVector J l u)

/-- The right ideal f A as a K-subspace. -/
def rightIdealSpan (f : A) : Submodule K A :=
  Submodule.span K {y | ∃ a : A, y = f * a}

/-- Right-module isomorphism C(lambda) ≅ I, explicitly including the action. -/
def CellRightIso (l : Shape) (I : Submodule K A) : Prop :=
  ∃ e : (T l → K) ≃ₗ[K] I,
    ∀ v a, (e (cellAct D l v a) : A) = (e v : A) * a

/-- Split semisimple means a finite product of full matrix K-algebras.
A mere semisimple-ring predicate would lose the split conclusion. -/
def SplitSemisimple : Prop :=
  ∃ (r : ℕ) (d : Fin r → ℕ), (∀ i, 0 < d i) ∧
    Nonempty (A ≃ₐ[K] ∀ i : Fin r, Matrix (Fin (d i)) (Fin (d i)) K)

/-- Centrality is literal commutation with every algebra element. -/
def Central (e : A) : Prop := ∀ a : A, e * a = a * e

/-- Nonzero primitive CENTRAL idempotent: decompositions are central too. -/
def PrimitiveCentralIdempotent (e : A) : Prop :=
  e ≠ 0 ∧ e * e = e ∧ Central e ∧
  ∀ p q : A, Central p → Central q → p * p = p → q * q = q →
    p * q = 0 → q * p = 0 → e = p + q → p = 0 ∨ q = 0

/-- Completeness and both directions of orthogonality. -/
def CompleteOrthogonalIdempotents {I : Type*} [Fintype I] (e : I → A) : Prop :=
  (∀ i, e i * e i = e i) ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧ ∑ i, e i = 1

/-- Shape projector, Theorem 3.16(b), PDF p.13. -/
def shapeProjector (J : JMFamily D M) (l : Shape) : A :=
  ∑ t : T l, jmSpectralProjector J ⟨l, t⟩

/-- The generated JM subalgebra, paragraph 2.6, PDF p.4. -/
def jmAlgebra (J : JMFamily D M) : Subalgebra K A :=
  Algebra.adjoin K (Set.range J.L)

/-- Commutativity and maximality among commutative K-subalgebras. -/
def MaximalAbelian (B : Subalgebra K A) : Prop :=
  (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧
  ∀ C : Subalgebra K A, B ≤ C →
    (∀ x ∈ C, ∀ y ∈ C, x * y = y * x) → C = B

/-- Sanity check: zero JM operators give the empty jmSpectralProjector product 1. -/
example (J : JMFamily D 0) (t : CellTableau Shape T) : jmSpectralProjector J t = 1 := by
  simp [jmSpectralProjector]

/-- Sanity check: the computed cell form vanishes at the zero vector. -/
example (l : Shape) (w : T l → K) : cellForm D l 0 w = 0 := by
  simp [cellForm]

/-- The generator viewed inside the generated subalgebra, paragraph 2.6. -/
def jmGenerator (J : JMFamily D M) (i : Fin M) : jmAlgebra J :=
  ⟨J.L i, Algebra.subset_adjoin ⟨i, rfl⟩⟩

/-- Irreducibility of a representation means nonzero and no proper nonzero
invariant K-subspace. No finite-dimensional restriction is silently added. -/
def IrreducibleRepresentation {B V : Type*} [Ring B] [Algebra K B]
    [AddCommGroup V] [Module K V] (rho : B →ₐ[K] Module.End K V) : Prop :=
  (∃ v : V, v ≠ 0) ∧ ∀ U : Submodule K V,
    (∀ b : B, ∀ v ∈ U, rho b v ∈ U) → U = ⊥ ∨ U = ⊤

end SeparatedDefinitions

section WedderburnExample

end WedderburnExample

section NewtonExample

variable {R : Type*} [CommRing R] [newtonDomain : IsDomain R]

/-- The literal monic defining polynomial of Example 2.14, PDF p.6. -/
def newtonPolynomial {n : ℕ} (c : Fin n → R) : Polynomial R :=
  ∏ i, (Polynomial.X - Polynomial.C (c i))

/-- The canonical quotient R[X]/prod(X-c_i) of Example 2.14. -/
abbrev NewtonAlgebra {n : ℕ} (c : Fin n → R) := AdjoinRoot (newtonPolynomial c)

/-- a_{i+1}=prod_{j<i}(x-c_{j+1}); i=n includes the zero boundary vector.
No arbitrary quotient basis is substituted for this computed family. -/
def newtonVector {n : ℕ} (c : Fin n → R) (i : ℕ) : NewtonAlgebra c :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i),
    (AdjoinRoot.root (newtonPolynomial c) - algebraMap R (NewtonAlgebra c) (c j))

/-- Sanity check: the initial Newton vector is the empty product 1. -/
example {n : ℕ} (c : Fin n → R) : newtonVector c 0 = 1 := by
  simp [newtonVector]

end NewtonExample

section IntegralForm

variable {R K AR AK Shape : Type*} [CommRing R] [integralDomain : IsDomain R] [Field K]
variable [Algebra R K] [integralFraction : IsFractionRing R K]
variable [Ring AR] [Algebra R AR] [Ring AK] [Algebra K AK] [Algebra R AK]
variable [integralTower : IsScalarTower R K AK] [Fintype Shape] [PartialOrder Shape]
variable {T : Shape → Type*} [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]
variable (DR : CellDatum (R := R) (A := AR) (T := T))
variable (DK : CellDatum (R := K) (A := AK) (T := T))

end IntegralForm

section ResidueIntegrality

variable {R K AR AK Shape : Type*} [CommRing R] [modularDomain : IsDomain R]
variable [modularDVR : IsDiscreteValuationRing R] [Field K] [Algebra R K] [modularFraction : IsFractionRing R K]
variable [Ring AR] [Algebra R AR] [Ring AK] [Algebra K AK] [Algebra R AK]
variable [modularTower : IsScalarTower R K AK] [Fintype Shape] [PartialOrder Shape]
variable {T : Shape → Type*} [∀ l, Fintype (T l)] [∀ l, PartialOrder (T l)]

/-- Complete residue-sequence equality uses the canonical quotient map,
Definition 4.1, PDF p.15. -/
def sameResidue {DR : CellDatum (R := R) (A := AR) (T := T)} {M : ℕ}
    (J : JMFamily DR M) (s t : CellTableau Shape T) : Prop :=
  ∀ i, IsLocalRing.residue R (J.content s i) = IsLocalRing.residue R (J.content t i)

/-- Sanity check: the canonical full-residue relation is reflexive. -/
example {DR : CellDatum (R := R) (A := AR) (T := T)} {M : ℕ}
    (J : JMFamily DR M) (t : CellTableau Shape T) : sameResidue J t t := by
  intro i
  rfl

/-- A modular system with the SAME cellular R-form, its fraction-field form,
and canonical residue specialization. Module.Basis compatibility pins both scalar
extensions; coefficient compatibility pins the canonical reduction. -/
structure ModularSystem (B : Type*) [Ring B] [Algebra (IsLocalRing.ResidueField R) B]
    (M : ℕ) where
  integral : CellDatum (R := R) (A := AR) (T := T)
  generic : CellDatum (R := K) (A := AK) (T := T)
  special : CellDatum (R := IsLocalRing.ResidueField R) (A := B) (T := T)
  integralJM : JMFamily integral M
  genericJM : JMFamily generic M
  inclusion : AR →ₐ[R] AK
  reduction : AR →+* B
  inclusion_basis : ∀ z, inclusion (integral.basis z) = generic.basis z
  reduction_basis : ∀ z, reduction (integral.basis z) = special.basis z
  reduction_scalars : ∀ r : R, reduction (algebraMap R AR r) =
    algebraMap (IsLocalRing.ResidueField R) B (IsLocalRing.residue R r)
  inclusion_jm : ∀ i, inclusion (integralJM.L i) = genericJM.L i
  inclusion_content : ∀ t i,
    algebraMap R K (integralJM.content t i) = genericJM.content t i

variable {B : Type*} [Ring B] [Algebra (IsLocalRing.ResidueField R) B] {M : ℕ}

/-- The actual generic class sum, before asserting its integrality. -/
def genericClassSum (S : ModularSystem (R := R) (K := K) (AR := AR) (AK := AK) (T := T) B M)
    (t : CellTableau Shape T) : AK :=
  ∑ u ∈ Finset.univ.filter (sameResidue S.integralJM t), jmSpectralProjector S.genericJM u

/-- Lift through the inclusion only on its image. The zero fallback off that
image is explicit; 4.2 proves that it is never used for class sums. -/
def integralLift (S : ModularSystem (R := R) (K := K) (AR := AR) (AK := AK) (T := T) B M)
    (x : AK) : AR := by
  classical
  exact if h : ∃ a : AR, S.inclusion a = x then Classical.choose h else 0

/-- G_[t] is reduced from the generic class SUM after integrality (4.2),
not from individual potentially nonintegral F_t. Definition 4.3, p.16. -/
def reducedClassProjector
    (S : ModularSystem (R := R) (K := K) (AR := AR) (AK := AK) (T := T) B M)
    (t : CellTableau Shape T) : B :=
  S.reduction (integralLift S (genericClassSum S t))

/-- The cell vector g_t=a_t G_[t] in the ORIGINAL specialized cell module.
This is the interpretation used in the proof of 4.9, PDF pp.18–19; it does
not identify an arbitrary possibly scaled fixed-row quotient with C(lambda). -/
def reducedCellVector
    (S : ModularSystem (R := R) (K := K) (AR := AR) (AK := AK) (T := T) B M)
    (l : Shape) (t : T l) : T l → IsLocalRing.ResidueField R :=
  cellAct S.special l (cellVector l t) (reducedClassProjector S ⟨l, t⟩)

/-- Residual linkage is the EQUIVALENCE CLOSURE of sharing a residue class,
not just the one-step sharing relation. Definition 4.1(b), PDF p.15. -/
def residuallyLinked
    (S : ModularSystem (R := R) (K := K) (AR := AR) (AK := AK) (T := T) B M)
    (l m : Shape) : Prop :=
  Relation.EqvGen (fun a b => ∃ (s : T a) (t : T b),
    sameResidue S.integralJM ⟨a, s⟩ ⟨b, t⟩) l m

/-- Cell modules in the same block are nonzero modules supported by the
same primitive CENTRAL idempotent. This does not confuse blocks with
arbitrary residue-linkage components, which need not be indecomposable. -/
def CellsSameBlock
    (S : ModularSystem (R := R) (K := K) (AR := AR) (AK := AK) (T := T) B M)
    (l m : Shape) : Prop :=
  (∃ v : T l → IsLocalRing.ResidueField R, v ≠ 0) ∧
  (∃ v : T m → IsLocalRing.ResidueField R, v ≠ 0) ∧
  ∃ p : B, PrimitiveCentralIdempotent p ∧
    (∀ v, cellAct S.special l v p = v) ∧ (∀ v, cellAct S.special m v p = v)

/-- Ordered monomial evaluation in a possibly noncommutative target.
The reduced JM elements commute, so this is the usual polynomial evaluation. -/
def orderedPolynomialEval {F C : Type*} [CommRing F] [Ring C] [Algebra F C]
    {n : ℕ} (p : MvPolynomial (Fin n) F) (L : Fin n → C) : C :=
  ∑ m ∈ p.support, algebraMap F C (p.coeff m) * (List.ofFn (fun i : Fin n => L i ^ m i)).prod

/-- Symmetry under EVERY permutation of the variables. -/
def SymmetricPolynomial {F : Type*} [CommRing F] {n : ℕ}
    (p : MvPolynomial (Fin n) F) : Prop :=
  ∀ sigma : Equiv.Perm (Fin n), MvPolynomial.rename sigma p = p

section ModularStatements

include modularDomain modularDVR modularFraction modularTower

end ModularStatements

end ResidueIntegrality

section AppendixDefinitions

variable {R : Type*} [CommRing R]

/-- Matrix shape J, Soriano Appendix §1, PDF p.24. Nonempty J is part of
this predicate; support is contained in the interval-union u_J. -/
def HasShape {d : ℕ} (Z : Matrix (Fin d) (Fin d) R) (J : Finset (Fin d)) : Prop :=
  J.Nonempty ∧
  (∀ a b, Z a b ≠ 0 → ∃ i ∈ J, a ≤ i ∧ i ≤ b) ∧
  (∀ i, Z i i = if i ∈ J then 1 else 0)

/-- The represented upper triangular operators of Appendix §1, PDF pp.23–24.
No pairwise commutation or faithful original representation is imposed. -/
structure TriangularSystem (R : Type*) [CommRing R] (d n : ℕ) where
  L : Fin n → Matrix (Fin d) (Fin d) R
  upper : ∀ k a b, b < a → L k a b = 0

/-- Diagonal residues, tied to the actual represented matrix. -/
def triangularDiagonalEntry {d n : ℕ} (S : TriangularSystem R d n) (k : Fin n) (i : Fin d) : R :=
  S.L k i i

/-- Appendix separating condition (S), PDF p.25: unit differences, not
merely distinct residues over a domain. -/
def UnitSeparating {d n : ℕ} (S : TriangularSystem R d n) : Prop :=
  ∀ i j : Fin d, i ≠ j → ∃ k : Fin n, IsUnit (triangularDiagonalEntry S k i - triangularDiagonalEntry S k j)

/-- Fixed separating choices and an ordered list of factors at each i.
They are construction data; idempotence is not assumed. Appendix §3, p.25. -/
structure SeparatingChoices {d n : ℕ} (S : TriangularSystem R d n) where
  position : ∀ i j : Fin d, i ≠ j → Fin n
  denominator : ∀ i j : Fin d, i ≠ j → Rˣ
  denominator_value : ∀ i j (h : i ≠ j),
    (denominator i j h : R) =
      triangularDiagonalEntry S (position i j h) i - triangularDiagonalEntry S (position i j h) j
  order : Fin d → List (Fin d)
  nodup : ∀ i, (order i).Nodup
  members : ∀ i j, j ∈ order i ↔ j ≠ i

/-- Ordered interpolation product Z_i, Appendix §3, PDF p.25.
Only the represented matrices are multiplied. -/
def interpolation {d n : ℕ} (S : TriangularSystem R d n)
    (C : SeparatingChoices S) (i : Fin d) : Matrix (Fin d) (Fin d) R :=
  ((C.order i).map (fun j => if h : i ≠ j then
    ((C.denominator i j h)⁻¹ : Rˣ).val •
      (S.L (C.position i j h) -
        algebraMap R (Matrix (Fin d) (Fin d) R) (triangularDiagonalEntry S (C.position i j h) j))
    else 1)).prod

/-- E^i = Z_i^d, Appendix §3, PDF p.25. -/
def directedProjector {d n : ℕ} (S : TriangularSystem R d n)
    (C : SeparatingChoices S) (i : Fin d) : Matrix (Fin d) (Fin d) R :=
  interpolation S C i ^ d

/-- Directedness has the larger index on the LEFT, Definition 3.2, p.26. -/
def DirectedFamily {H : Type*} [Ring H] {d : ℕ} (e : Fin d → H) : Prop :=
  (∀ i, e i * e i = e i) ∧ ∀ i j, i < j → e j * e i = 0

/-- Local linkage is equality of the full triangularDiagonalEntry residue sequence,
Appendix Definition 5.1, PDF pp.27–28. -/
def linked {d n : ℕ} [IsLocalRing R] (S : TriangularSystem R d n) (i j : Fin d) : Prop :=
  ∀ k, IsLocalRing.residue R (triangularDiagonalEntry S k i) =
    IsLocalRing.residue R (triangularDiagonalEntry S k j)

/-- The actual nonempty linkage class of a basis index. -/
def linkageClass {d n : ℕ} [IsLocalRing R] (S : TriangularSystem R d n) (i : Fin d) :
    Finset (Fin d) := Finset.univ.filter (linked S i)

/-- Distinct classes form the quotient index set; repeated classes are removed. -/
def linkagePartition {d n : ℕ} [IsLocalRing R] (S : TriangularSystem R d n) :
    Finset (Finset (Fin d)) := Finset.univ.image (linkageClass S)

/-- Appendix projectors live in the MATRIX algebra generated by the represented
operators. This does not pull them back through a nonfaithful representation. -/
def representedAlgebra {d n : ℕ} (S : TriangularSystem R d n) :
    Subalgebra R (Matrix (Fin d) (Fin d) R) := Algebra.adjoin R (Set.range S.L)

/-- Full class-projector conclusion in Appendix 6.1–6.2: shaped, generated,
complete and orthogonal. No defective printed nonsingleton Z_J is used. -/
def ClassProjectors {d n : ℕ} [IsLocalRing R] (S : TriangularSystem R d n)
    (e : Finset (Fin d) → Matrix (Fin d) (Fin d) R) : Prop :=
  (∀ J ∈ linkagePartition S, HasShape (e J) J ∧ e J ∈ representedAlgebra S ∧ e J * e J = e J) ∧
  (∀ J ∈ linkagePartition S, ∀ U ∈ linkagePartition S, J ≠ U → e J * e U = 0) ∧
  ∑ J ∈ linkagePartition S, e J = 1

/-- The left regular representation relative to a chosen basis. This is used
only when conclusions are about the ORIGINAL algebra, Appendix Remark 6.2. -/
def regularMatrix {A : Type*} [Ring A] [Algebra R A] {d : ℕ}
    (b : Module.Basis (Fin d) R A) (x : A) : Matrix (Fin d) (Fin d) R :=
  fun i j => b.repr (x * b j) i

/-- An explicitly triangular regular family, with no assumption on its centre. -/
def regularSystem {A : Type*} [Ring A] [Algebra R A] {d n : ℕ}
    (b : Module.Basis (Fin d) R A) (L : Fin n → A)
    (h : ∀ k i j, j < i → regularMatrix b (L k) i j = 0) : TriangularSystem R d n :=
  ⟨fun k => regularMatrix b (L k), h⟩

/-- Sanity check: shape is never assigned to the empty set. -/
example {d : ℕ} (Z : Matrix (Fin d) (Fin d) R) : ¬ HasShape Z ∅ := by
  simp [HasShape]

end AppendixDefinitions

section RingAppendix

variable {H : Type*} [Ring H]

/-- Epsilon_N(x) = sum_{i=0}^{N-1} binom(2N-1,i) x^(2N-1-i)(1-x)^i,
Appendix §2, PDF pp.24–25. Natural coefficients are central in every ring. -/
def epsilon (N : ℕ) (x : H) : H :=
  ∑ i ∈ Finset.range N,
    (Nat.choose (2 * N - 1) i : H) * x ^ (2 * N - 1 - i) * (1 - x) ^ i

/-- Two-sidedness and I^N=0, expressed directly in an arbitrary unital ring.
Products of N elements of I vanish. No commutative ideal instance is used. -/
def TwoSidedNilpotent (I : AddSubgroup H) (N : ℕ) : Prop :=
  (∀ a : H, ∀ x ∈ I, a * x ∈ I ∧ x * a ∈ I) ∧
  ∀ xs : List H, xs.length = N → (∀ x ∈ xs, x ∈ I) → xs.prod = 0

/-- The two sets in Appendix Lemma 4.1, PDF p.26, encoded as prefix/tail.
The tail is directed; the prefix is orthogonal in both directions. -/
def OrthogonalStage {d : ℕ} (f : Fin d → H) (k : ℕ) : Prop :=
  (∀ i, f i * f i = f i) ∧
  (∀ i j : Fin d, i.val < k → j.val < k → i ≠ j → f i * f j = 0) ∧
  (∀ i j : Fin d, k ≤ i.val → i < j → f j * f i = 0) ∧
  (∀ i j : Fin d, i.val < k → k ≤ j.val → f i * f j = 0 ∧ f j * f i = 0)

/-- One exact noncommutative Gram–Schmidt step, Appendix Lemma 4.1. -/
def orthogonalStep {d : ℕ} (f : Fin d → H) (k : ℕ) : Fin d → H :=
  fun i => if i.val ≤ k then f i else
    (1 - ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val ≤ k), f j) * f i

/-- Sanity check: zero factors in the defining epsilon sum give zero. -/
example (x : H) : epsilon 0 x = 0 := by
  simp [epsilon]

/-- Sanity check in the stated N>=2 regime: epsilon_2 fixes zero. -/
example : epsilon 2 (0 : H) = 0 := by
  norm_num [epsilon, Finset.sum_range_succ]

/-- Sanity check in the stated N>=2 regime: epsilon_2 fixes the identity. -/
example : epsilon 2 (1 : H) = 1 := by
  norm_num [epsilon, Finset.sum_range_succ]

end RingAppendix

end QAlgorithms.Papers.Independent.Support21.P08


