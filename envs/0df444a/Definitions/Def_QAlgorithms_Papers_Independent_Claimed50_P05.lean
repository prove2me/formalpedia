-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05
-- name    : QAlgorithms_Papers_Independent_Claimed50_P05
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T08:59:15.82434+00:00
-- url     : https://prove2.me/theorems/40f01dd7-3cbe-41d8-8724-93dd36b11985
-- title:
--   Definitions for The Functional Calculus Approach to the Spectral Theorem
-- statement:
--   The objects the formalized statements of *The Functional Calculus Approach to the Spectral Theorem* (arXiv:2003.06130) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Symbol`: Finite measurable functions, with pointwise equality (p.4).
--   - `Relation`: Graph carrier; linearity, closedness and functionality are specified below.
--   - `boundedGraph`: Full boundedGraph of a bounded operator.
--   - `identity`: Everywhere-defined identity.
--   - `zeroGraph`: Everywhere-defined zero.
--   - `graphDomain`: Actual operator graphDomain.
--   - `kernel`: Kernel includes membership in the operator graphDomain.
--   - `rangeOf`: Actual boundedGraph range.
--   - `add`: Sum on the intersection of the two domains.
--   - `mul`: Composition: B is applied first.
--   - `scale`: Scalar multiplication retains the graphDomain, even at zero.
--   - `inverse`: Inverse on the range, without asserting bounded invertibility.
--   - `graphAdjoint`: Adjoint relation for Mathlib's starSymbol-linear-first inner product.
--   - `ClosedOperator`: C(H): closed functional linear graphs (pp.3–4).
--   - `BoundedOperator`: Bounded means an everywhere-defined continuous linear map.
--   - `NormBound`: Operator norm bound, also asserting boundedness.
--   - `InjectiveOperator`: Injectivity of a functional boundedGraph.
--   - `value`: Output selector, used only with explicit graphDomain membership or boundedness.
--   - `Normal`: Closed dense normal operator, including graphAdjoint-product graphDomain equality.
--   - `SelfAdjoint`: Closed densely defined self-graphAdjoint operator.
--   - `Symmetric`: Symmetry of the boundedGraph.
--   - `GraphPositive`: Nonnegative diagonal pairings.
--   - `restrictGraph`: Restriction to a graphDomain set.
--   - `GraphCore`: A core is boundedGraph dense, not merely norm dense.
--   - `constant`: Constant measurable symbol.
--   - `plus`: Pointwise sum.
--   - `times`: Pointwise product.
--   - `scalar`: Scalar multiple.
--   - `starSymbol`: Pointwise conjugation.
--   - `reciprocal`: Total pointwise reciprocal; relevant results exclude zeros explicitly.
--   - `absolute`: Absolute value, embedded in k.
--   - `indicator`: Scalar indicator of a measurable set.
--   - `BoundedSymbol`: Bounded symbol, allowing an empty base.
--   - `symbolNorm`: Supremum norm, used only on bounded symbols; zero on an empty base.
--   - `Pointwise`: Pointwise sequential convergence.
--   - `BP`: Bounded-pointwise convergence, with one bound before both n and x.
--   - `Strong`: Strong operator convergence, with full-graphDomain boundedness built in.
--   - `Weak`: Weak operator convergence on all pairs of vectors.
--   - `ProtoCalculus`: MFC1–MFC3, with the product-graphDomain equality, not only boundedGraph inclusion.
--   - `Calculus`: Precisely MFC1–MFC5 (pp.4–5). MFC4 conjugates the symbol.
--   - `RealValued`: Reality in either scalar field.
--   - `RealLE`: Real order, used with real-valued inputs.
--   - `regularizer`: Canonical regularizer from §2.4.
--   - `quadraticRegularizer`: Squared-modulus regularizer in Theorem 5.3.
--   - `compose`: Measurable composition.
--   - `push`: Concrete push-forward calculus.
--   - `SymbolHom`: Unital scalar-preserving star homomorphism on symbol algebras.
--   - `Null`: Null measurable sets are those with zero indicator operator.
--   - `Almost`: Calculus almost-everywhere predicate.
--   - `Concentrated`: Concentration includes measurability.
--   - `calculusSupport`: Complement of the union of open null sets, as in §3.3.
--   - `essentialRange`: Essential range uses non-null inverse images of closed epsilon balls.
--   - `resolventShift`: Lambda I minus A, on A's graphDomain.
--   - `resolventSet`: Resolvent set: inverse is everywhere-defined and bounded.
--   - `spectrumOf`: Spectrum for unbounded closed operators.
--   - `pointSpectrum`: Point spectrum, with a nonzero graphDomain vector.
--   - `approximateSpectrum`: Approximate point spectrum with normalized vectors in the graphDomain.
--   - `OrthogonalProjection`: Full-graphDomain orthogonal projection.
--   - `ProjectionOnto`: Orthogonal projection with a specified range.
--   - `PVM`: PVM1–PVM3, with strong countable additivity on pairwise disjoint sets.
--   - `Intertwines`: Intertwining means the full boundedGraph inclusion, with possibly different Hilbert spaces.
--   - `realMax`: Maximum, used only when both functions are real-valued.
--   - `realMin`: Minimum, used only when both functions are real-valued.
--   - `EightProperties`: All eight closure properties of Theorem 5.3, without a uniform bound in property 4.
--   - `graphPower`: Genuine iterated partial-operator powers.
--   - `sumGraphs`: Finite sum with a full-graphDomain zero for the empty list.
--   - `productGraphs`: Ordered finite product with identity for the empty list.
--   - `polynomialGraph`: Polynomial evaluation retains all zero-coefficient terms and their domains.
--   - `polynomialSymbol`: Polynomial evaluated pointwise on a symbol.
--   - `tupleSum`: Finite pointwise sum.
--   - `tupleProduct`: Finite pointwise product.
--   - `restrictedCoordinate`: Coordinates on an arbitrary subset with the trace Borel sigma algebra.
--   - `squaredTupleNorm`: Euclidean squared tuple norm, not the Pi sup norm.
--   - `tupleRegularizer`: Quadratic tuple regularizer.
--   - `tupleRootCoordinate`: Square-root-regularized restrictedCoordinate.
--   - `fullCoordinate`: Full-space restrictedCoordinate.
--   - `scalarIdentity`: Scalar identity function.
--   - `transformT`: Canonical T_A = (I + A* A)^-1.
--   - `transformS`: Canonical S_A = A T_A.
--   - `StronglyCommute`: All four transforms commute pairwise, exactly the definition on p.34.
--   - `SpectralAdmissible`: Normal, and self-graphAdjoint in the real case.
--   - `CalculusFor`: A full Borel calculus for a specified operator boundedGraph.
--   - `operatorCalculus`: A choice of calculus, used only for admissible operators after Theorem 7.6.
--   - `spectralValue`: Borel spectral evaluation.
--   - `transformZ`: Bounded transform defined by the prescribed symbol, p.35.
--   - `multiplication`: Multiplication on L2: equality of representatives almost everywhere.
--   - `Semifinite`: Semifinite, with no sigma-finiteness assumption.
--   - `EssentiallyBounded`: Essential boundedness.
--   - `essentialNorm`: ENNReal L-infinity norm, preserving infinity.
--   - `measureEssentialRange`: Measure essential range.
--   - `unitaryGraphTransport`: Correctly typed unitary unitaryGraphTransport of a boundedGraph.
--   - `cyclic`: Closed cyclic subspace generated by bounded symbols at x.
--   - `BoundedRestrictionHom`: The star algebra of calculus-bounded symbols and its unital star representation.
--   - `part`: Part of a boundedGraph in a closed Hilbert subspace (§2.5).
--   - `extendZero`: Canonical zero extension from a measurable subset (§3.2).
--   - `restrictBase`: Restriction of the base, using the source's zero-extension construction.
--   - `extendBase`: Extension from a subset by restricting the symbols.
--   - `BoundedSymbols`: The bounded measurable symbol algebra as a subtype.
--   - `BoundedHom`: A unital scalar-linear star homomorphism on bounded symbols. Proof arguments merely name their boundedness and do not restrict the algebraic identities.
--   - `BoundedWeakBP`: Weak bp continuity of a bounded-symbol representation.
--   - `algebraicExtension`: Canonical algebraic extension from p.25, using e=(1+|f|)^-1. The fallback is irrelevant since both symbols in the test are bounded for every f.
--   - `ContinuousHom`: Unital scalar-linear star homomorphism on continuous functions.
--   - `continuousSymbol`: Continuous symbols in the Borel algebra.
--   - `ExtendsContinuous`: Agreement with a given continuous representation.
--   - `RegularExtension`: The precise regularity property of Theorem 6.4. On a compact space every continuous function has compact calculusSupport, so the supremum ranges over C(X).
--   - `baire`: The Baire algebra generated by continuous scalar functions (p.28).
--   - `continuousBaireSymbol`: Continuous functions are measurable for the explicitly generated Baire algebra.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, https://arxiv.org/abs/2003.06130v2

import Mathlib

/-! Haase, arXiv:2003.06130v2. Paper-local operator graph and symbol definitions.
Graphs retain actual operator domains. Symbols are pointwise functions, not
measure classes. Compilation is pending the batch handoff. -/

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Finite measurable functions, with pointwise equality (p.4). -/
abbrev Symbol (X k : Type*) [MeasurableSpace X] [RCLike k] := {f : X → k // Measurable f}

/-- Graph carrier; linearity, closedness and functionality are specified below. -/
abbrev Relation (H : Type*) := Set (H × H)

/-- Full boundedGraph of a bounded operator. -/
def boundedGraph (T : H →L[k] H) : Relation H := {p | p.2 = T p.1}

/-- Everywhere-defined identity. -/
def identity : Relation H := {p | p.2 = p.1}

/-- Everywhere-defined zero. -/
def zeroGraph : Relation H := {p | p.2 = 0}

/-- Actual operator graphDomain. -/
def graphDomain (A : Relation H) : Set H := {x | ∃ y, (x, y) ∈ A}

/-- Kernel includes membership in the operator graphDomain. -/
def kernel (A : Relation H) : Set H := {x | (x, 0) ∈ A}

/-- Actual boundedGraph range. -/
def rangeOf (A : Relation H) : Set H := {y | ∃ x, (x, y) ∈ A}

/-- Sum on the intersection of the two domains. -/
def add (A B : Relation H) : Relation H :=
  {p | ∃ a b, (p.1, a) ∈ A ∧ (p.1, b) ∈ B ∧ p.2 = a + b}

/-- Composition: B is applied first. -/
def mul (A B : Relation H) : Relation H :=
  {p | ∃ z, (p.1, z) ∈ B ∧ (z, p.2) ∈ A}

/-- Scalar multiplication retains the graphDomain, even at zero. -/
def scale (c : k) (A : Relation H) : Relation H :=
  {p | ∃ y, (p.1, y) ∈ A ∧ p.2 = c • y}

/-- Inverse on the range, without asserting bounded invertibility. -/
def inverse (A : Relation H) : Relation H := {p | (p.2, p.1) ∈ A}

/-- Adjoint relation for Mathlib's starSymbol-linear-first inner product. -/
def graphAdjoint (A : Relation H) : Relation H :=
  {p | ∀ x y, (x, y) ∈ A → inner k x p.2 = inner k y p.1}

/-- C(H): closed functional linear graphs (pp.3–4). -/
def ClosedOperator (A : Relation H) : Prop :=
  CompleteSpace H ∧ IsClosed A ∧ (0, 0) ∈ A ∧
  (∀ x y x2 y2, (x, y) ∈ A → (x2, y2) ∈ A → (x + x2, y + y2) ∈ A) ∧
  (∀ c : k, ∀ x y, (x, y) ∈ A → (c • x, c • y) ∈ A) ∧
  (∀ x y z, (x, y) ∈ A → (x, z) ∈ A → y = z)

/-- Bounded means an everywhere-defined continuous linear map. -/
def BoundedOperator (A : Relation H) : Prop := ∃ T : H →L[k] H, A = boundedGraph T

/-- Operator norm bound, also asserting boundedness. -/
def NormBound (A : Relation H) (c : ℝ) : Prop :=
  ∃ T : H →L[k] H, A = boundedGraph T ∧ ‖T‖ ≤ c

/-- Injectivity of a functional boundedGraph. -/
def InjectiveOperator (A : Relation H) : Prop :=
  ∀ x z y, (x, y) ∈ A → (z, y) ∈ A → x = z

/-- Output selector, used only with explicit graphDomain membership or boundedness. -/
def value (A : Relation H) (x : H) : H :=
  if h : ∃ y, (x, y) ∈ A then Classical.choose h else 0

/-- Closed dense normal operator, including graphAdjoint-product graphDomain equality. -/
def Normal (A : Relation H) : Prop :=
  ClosedOperator (k := k) A ∧ Dense (graphDomain A) ∧
  mul (graphAdjoint (k := k) A) A = mul A (graphAdjoint (k := k) A)

/-- Closed densely defined self-graphAdjoint operator. -/
def SelfAdjoint (A : Relation H) : Prop :=
  ClosedOperator (k := k) A ∧ Dense (graphDomain A) ∧ graphAdjoint (k := k) A = A

/-- Symmetry of the boundedGraph. -/
def Symmetric (A : Relation H) : Prop := A ⊆ graphAdjoint (k := k) A

/-- Nonnegative diagonal pairings. -/
def GraphPositive (A : Relation H) : Prop :=
  ∀ x y, (x, y) ∈ A → 0 ≤ RCLike.re (inner k x y)

/-- Restriction to a graphDomain set. -/
def restrictGraph (A : Relation H) (D : Set H) : Relation H := {p | p ∈ A ∧ p.1 ∈ D}

/-- A core is boundedGraph dense, not merely norm dense. -/
def GraphCore (A : Relation H) (D : Set H) : Prop := D ⊆ graphDomain A ∧ closure (restrictGraph A D) = A

/-- Constant measurable symbol. -/
def constant (c : k) : Symbol X k := ⟨fun _ => c, measurable_const⟩

/-- Pointwise sum. -/
def plus (f g : Symbol X k) : Symbol X k := ⟨fun x => f.val x + g.val x, f.property.add g.property⟩

/-- Pointwise product. -/
def times (f g : Symbol X k) : Symbol X k := ⟨fun x => f.val x * g.val x, f.property.mul g.property⟩

/-- Scalar multiple. -/
def scalar (c : k) (f : Symbol X k) : Symbol X k :=
  ⟨fun x => c * f.val x, measurable_const.mul f.property⟩

/-- Pointwise conjugation. -/
def starSymbol (f : Symbol X k) : Symbol X k := ⟨fun x => star (f.val x), by have hf := f.property; fun_prop⟩

/-- Total pointwise reciprocal; relevant results exclude zeros explicitly. -/
def reciprocal (f : Symbol X k) : Symbol X k := ⟨fun x => (f.val x)⁻¹, by have hf := f.property; fun_prop⟩

/-- Absolute value, embedded in k. -/
def absolute (f : Symbol X k) : Symbol X k := ⟨fun x => (‖f.val x‖ : k), by have hf := f.property; fun_prop⟩

/-- Scalar indicator of a measurable set. -/
def indicator (A : Set X) (hA : MeasurableSet A) : Symbol X k :=
  ⟨A.indicator (fun _ => (1 : k)), measurable_const.indicator hA⟩

/-- Bounded symbol, allowing an empty base. -/
def BoundedSymbol (f : Symbol X k) : Prop := ∃ c : ℝ, ∀ x, ‖f.val x‖ ≤ c

/-- Supremum norm, used only on bounded symbols; zero on an empty base. -/
def symbolNorm (f : Symbol X k) : ℝ := sSup (Set.range fun x => ‖f.val x‖)

/-- Pointwise sequential convergence. -/
def Pointwise (f : ℕ → Symbol X k) (g : Symbol X k) : Prop :=
  ∀ x, Tendsto (fun n => (f n).val x) atTop (𝓝 (g.val x))

/-- Bounded-pointwise convergence, with one bound before both n and x. -/
def BP (f : ℕ → Symbol X k) (g : Symbol X k) : Prop :=
  Pointwise f g ∧ ∃ c : ℝ, ∀ n x, ‖(f n).val x‖ ≤ c

/-- Strong operator convergence, with full-graphDomain boundedness built in. -/
def Strong (A : ℕ → Relation H) (B : Relation H) : Prop :=
  (∀ n, BoundedOperator (k := k) (A n)) ∧ BoundedOperator (k := k) B ∧
  ∀ x, Tendsto (fun n => value (A n) x) atTop (𝓝 (value B x))

/-- Weak operator convergence on all pairs of vectors. -/
def Weak (A : ℕ → Relation H) (B : Relation H) : Prop :=
  (∀ n, BoundedOperator (k := k) (A n)) ∧ BoundedOperator (k := k) B ∧
  ∀ x y, Tendsto (fun n => inner k x (value (A n) y)) atTop (𝓝 (inner k x (value B y)))

/-- MFC1–MFC3, with the product-graphDomain equality, not only boundedGraph inclusion. -/
def ProtoCalculus (F : Symbol X k → Relation H) : Prop :=
  F (constant 1) = identity ∧
  (∀ f g, add (F f) (F g) ⊆ F (plus f g)) ∧
  (∀ c f, scale c (F f) ⊆ F (scalar c f)) ∧
  (∀ f g, mul (F f) (F g) ⊆ F (times f g)) ∧
  (∀ f g, graphDomain (mul (F f) (F g)) = graphDomain (F g) ∩ graphDomain (F (times f g)))

/-- Precisely MFC1–MFC5 (pp.4–5). MFC4 conjugates the symbol. -/
def Calculus (F : Symbol X k → Relation H) : Prop :=
  (∀ f, ClosedOperator (k := k) (F f)) ∧ ProtoCalculus F ∧
  (∀ f, BoundedSymbol f → BoundedOperator (k := k) (F f) ∧ graphAdjoint (k := k) (F f) = F (starSymbol f)) ∧
  (∀ fn f, BP fn f → Weak (k := k) (fun n => F (fn n)) (F f))

/-- Reality in either scalar field. -/
def RealValued (f : Symbol X k) : Prop := ∀ x, star (f.val x) = f.val x

/-- Real order, used with real-valued inputs. -/
def RealLE (f g : Symbol X k) : Prop := ∀ x, RCLike.re (f.val x) ≤ RCLike.re (g.val x)

/-- Canonical regularizer from §2.4. -/
def regularizer (f : Symbol X k) : Symbol X k :=
  ⟨fun x => ((1 + ‖f.val x‖ : ℝ)⁻¹ : k), by have hf := f.property; fun_prop⟩

/-- Squared-modulus regularizer in Theorem 5.3. -/
def quadraticRegularizer (f : Symbol X k) : Symbol X k :=
  ⟨fun x => ((1 + ‖f.val x‖ ^ 2 : ℝ)⁻¹ : k), by have hf := f.property; fun_prop⟩

/-- Measurable composition. -/
def compose (g : Symbol Y k) (p : X → Y) (hp : Measurable p) : Symbol X k :=
  ⟨g.val ∘ p, g.property.comp hp⟩

/-- Concrete push-forward calculus. -/
def push (F : Symbol X k → Relation H) (p : X → Y) (hp : Measurable p) :
    Symbol Y k → Relation H := fun g => F (compose g p hp)

/-- Unital scalar-preserving star homomorphism on symbol algebras. -/
def SymbolHom (T : Symbol Y k → Symbol X k) : Prop :=
  (∀ c, T (constant c) = constant c) ∧
  (∀ f g, T (plus f g) = plus (T f) (T g)) ∧
  (∀ f g, T (times f g) = times (T f) (T g)) ∧
  (∀ f, T (starSymbol f) = starSymbol (T f))

/-- Null measurable sets are those with zero indicator operator. -/
def Null (F : Symbol X k → Relation H) (A : Set X) : Prop :=
  ∃ hA : MeasurableSet A, F (indicator A hA) = zeroGraph

/-- Calculus almost-everywhere predicate. -/
def Almost (F : Symbol X k → Relation H) (P : X → Prop) : Prop := Null F {x | ¬ P x}

/-- Concentration includes measurability. -/
def Concentrated (F : Symbol X k → Relation H) (A : Set X) : Prop := MeasurableSet A ∧ Null F Aᶜ

/-- Complement of the union of open null sets, as in §3.3. -/
def calculusSupport [TopologicalSpace X] (F : Symbol X k → Relation H) : Set X :=
  (⋃₀ {U : Set X | IsOpen U ∧ Null F U})ᶜ

/-- Essential range uses non-null inverse images of closed epsilon balls. -/
def essentialRange (F : Symbol X k → Relation H) (f : Symbol X k) : Set k :=
  {c | ∀ e : ℝ, 0 < e → ¬ Null F {x | ‖f.val x - c‖ ≤ e}}

/-- Lambda I minus A, on A's graphDomain. -/
def resolventShift (c : k) (A : Relation H) : Relation H := add (scale c identity) (scale (-1 : k) A)

/-- Resolvent set: inverse is everywhere-defined and bounded. -/
def resolventSet (A : Relation H) : Set k := {c | BoundedOperator (k := k) (inverse (resolventShift c A))}

/-- Spectrum for unbounded closed operators. -/
def spectrumOf (A : Relation H) : Set k := (resolventSet (k := k) A)ᶜ

/-- Point spectrum, with a nonzero graphDomain vector. -/
def pointSpectrum (A : Relation H) : Set k := {c | ∃ x : H, x ≠ 0 ∧ (x, c • x) ∈ A}

/-- Approximate point spectrum with normalized vectors in the graphDomain. -/
def approximateSpectrum (A : Relation H) : Set k :=
  {c | ∀ e : ℝ, 0 < e → ∃ x y, (x, y) ∈ A ∧ ‖x‖ = 1 ∧ ‖y - c • x‖ < e}

/-- Full-graphDomain orthogonal projection. -/
def OrthogonalProjection (A : Relation H) : Prop :=
  BoundedOperator (k := k) A ∧ graphAdjoint (k := k) A = A ∧ mul A A = A

/-- Orthogonal projection with a specified range. -/
def ProjectionOnto (A : Relation H) (D : Set H) : Prop :=
  OrthogonalProjection (k := k) A ∧ rangeOf A = D

/-- PVM1–PVM3, with strong countable additivity on pairwise disjoint sets. -/
def PVM (E : {A : Set X // MeasurableSet A} → Relation H) : Prop :=
  CompleteSpace H ∧ (∀ A, OrthogonalProjection (k := k) (E A)) ∧
  E ⟨Set.univ, MeasurableSet.univ⟩ = identity ∧
  ∀ (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n)),
    Pairwise (fun i j => Disjoint (A i) (A j)) →
    ∀ x, Tendsto (fun n => ∑ j ∈ Finset.range n, value (E ⟨A j, hA j⟩) x) atTop
      (𝓝 (value (E ⟨⋃ n, A n, MeasurableSet.iUnion hA⟩) x))

/-- Intertwining means the full boundedGraph inclusion, with possibly different Hilbert spaces. -/
def Intertwines (F : Symbol X k → Relation H) (G : Symbol X k → Relation K)
    (T : H →L[k] K) (f : Symbol X k) : Prop :=
  ∀ x y, (x, y) ∈ F f → (T x, T y) ∈ G f

/-- Maximum, used only when both functions are real-valued. -/
def realMax (f g : Symbol X k) : Symbol X k :=
  ⟨fun x => ((max (RCLike.re (f.val x)) (RCLike.re (g.val x)) : ℝ) : k), by have hf := f.property; have hg := g.property; fun_prop⟩

/-- Minimum, used only when both functions are real-valued. -/
def realMin (f g : Symbol X k) : Symbol X k :=
  ⟨fun x => ((min (RCLike.re (f.val x)) (RCLike.re (g.val x)) : ℝ) : k), by have hf := f.property; have hg := g.property; fun_prop⟩

/-- All eight closure properties of Theorem 5.3, without a uniform bound in property 4. -/
def EightProperties (E : Set (Symbol X k)) : Prop :=
  ((∀ c, constant c ∈ E) ∧
   (∀ f g, f ∈ E → g ∈ E → plus f g ∈ E ∧ times f g ∈ E) ∧
   (∀ f, f ∈ E → starSymbol f ∈ E)) ∧
  (∀ f, f ∈ E → (∀ x, f.val x ≠ 0) → reciprocal f ∈ E) ∧
  (∀ f, f ∈ E ↔ times f (quadraticRegularizer f) ∈ E ∧ quadraticRegularizer f ∈ E) ∧
  (∀ fn f, (∀ n, fn n ∈ E) → Pointwise fn f → f ∈ E) ∧
  (∀ f, f ∈ E → absolute f ∈ E) ∧
  (∀ f g, f ∈ E → g ∈ E → RealValued f → RealValued g → realMax f g ∈ E ∧ realMin f g ∈ E) ∧
  ((indicator Set.univ MeasurableSet.univ ∈ E) ∧
   (∀ A (hA : MeasurableSet A), indicator A hA ∈ E → indicator Aᶜ hA.compl ∈ E) ∧
   (∀ (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n)),
     (∀ n, indicator (A n) (hA n) ∈ E) → indicator (⋃ n, A n) (MeasurableSet.iUnion hA) ∈ E)) ∧
  (∀ f, f ∈ E → ∀ B : Set k, ∀ hB : MeasurableSet B,
    indicator (f.val ⁻¹' B) (hB.preimage f.property) ∈ E)

/-- Genuine iterated partial-operator powers. -/
def graphPower (A : Relation H) : ℕ → Relation H
  | 0 => identity
  | n + 1 => mul A (graphPower A n)

/-- Finite sum with a full-graphDomain zero for the empty list. -/
def sumGraphs : List (Relation H) → Relation H
  | [] => zeroGraph
  | A :: As => add A (sumGraphs As)

/-- Ordered finite product with identity for the empty list. -/
def productGraphs : List (Relation H) → Relation H
  | [] => identity
  | A :: As => mul A (productGraphs As)

/-- Polynomial evaluation retains all zero-coefficient terms and their domains. -/
def polynomialGraph (p : Polynomial k) (A : Relation H) : Relation H :=
  sumGraphs ((List.range (p.natDegree + 1)).map fun j => scale (p.coeff j) (graphPower A j))

/-- Polynomial evaluated pointwise on a symbol. -/
def polynomialSymbol (p : Polynomial k) (f : Symbol X k) : Symbol X k :=
  ⟨fun x => p.eval (f.val x), p.continuous.measurable.comp f.property⟩

/-- Finite pointwise sum. -/
def tupleSum {d : ℕ} (f : Fin d → Symbol X k) : Symbol X k :=
  ⟨fun x => ∑ j, (f j).val x, by
    have hf : ∀ j, Measurable (f j).val := fun j => (f j).property
    fun_prop⟩

/-- Finite pointwise product. -/
def tupleProduct {d : ℕ} (f : Fin d → Symbol X k) : Symbol X k :=
  ⟨fun x => ∏ j, (f j).val x, by
    have hf : ∀ j, Measurable (f j).val := fun j => (f j).property
    fun_prop⟩

/-- Coordinates on an arbitrary subset with the trace Borel sigma algebra. -/
def restrictedCoordinate {d : ℕ} (S : Set (Fin d → k)) (j : Fin d) : Symbol S k :=
  ⟨fun x => x.val j, (measurable_pi_apply j).comp measurable_subtype_coe⟩

/-- Euclidean squared tuple norm, not the Pi sup norm. -/
def squaredTupleNorm {d : ℕ} (z : Fin d → k) : ℝ := ∑ j, ‖z j‖ ^ 2

/-- Quadratic tuple regularizer. -/
def tupleRegularizer {d : ℕ} (S : Set (Fin d → k)) : Symbol S k :=
  ⟨fun x => ((1 + squaredTupleNorm x.val : ℝ)⁻¹ : k), by
    have hc : ∀ j : Fin d, Measurable (fun x : S => x.val j) :=
      fun j => (measurable_pi_apply j).comp measurable_subtype_coe
    have hs : Measurable (fun x : S => squaredTupleNorm x.val) := by
      unfold squaredTupleNorm
      exact Finset.measurable_sum Finset.univ (fun j _ => (hc j).norm.pow_const 2)
    have hreal : Measurable (fun x : S => (1 + squaredTupleNorm x.val : ℝ)⁻¹) :=
      (measurable_const.add hs).inv
    simpa only [Function.comp_def, RCLike.ofReal_inv] using
      (RCLike.measurable_ofReal (𝕜 := k)).comp hreal⟩

/-- Square-root-regularized restrictedCoordinate. -/
def tupleRootCoordinate {d : ℕ} (S : Set (Fin d → k)) (j : Fin d) : Symbol S k :=
  ⟨fun x => x.val j / (Real.sqrt (1 + squaredTupleNorm x.val) : k), by
    have hc : ∀ j : Fin d, Measurable (fun x : S => x.val j) :=
      fun j => (measurable_pi_apply j).comp measurable_subtype_coe
    have hs : Measurable (fun x : S => squaredTupleNorm x.val) := by
      unfold squaredTupleNorm
      exact Finset.measurable_sum Finset.univ (fun j _ => (hc j).norm.pow_const 2)
    exact (hc j).div (RCLike.measurable_ofReal.comp ((measurable_const.add hs).sqrt))⟩

/-- Full-space restrictedCoordinate. -/
def fullCoordinate {d : ℕ} (j : Fin d) : Symbol (Fin d → k) k :=
  ⟨fun x => x j, measurable_pi_apply j⟩

/-- Scalar identity function. -/
def scalarIdentity : Symbol k k := ⟨id, measurable_id⟩

/-- Canonical T_A = (I + A* A)^-1. -/
def transformT (A : Relation H) : Relation H := inverse (add identity (mul (graphAdjoint (k := k) A) A))

/-- Canonical S_A = A T_A. -/
def transformS (A : Relation H) : Relation H := mul A (transformT (k := k) A)

/-- All four transforms commute pairwise, exactly the definition on p.34. -/
def StronglyCommute (A B : Relation H) : Prop :=
  let L := [transformT (k := k) A, transformS (k := k) A,
    transformT (k := k) B, transformS (k := k) B]
  ∀ C ∈ L, ∀ D ∈ L, mul C D = mul D C

/-- Normal, and self-graphAdjoint in the real case. -/
def SpectralAdmissible (A : Relation H) : Prop :=
  Normal (k := k) A ∧ ((∀ z : k, star z = z) → SelfAdjoint (k := k) A)

/-- A full Borel calculus for a specified operator boundedGraph. -/
def CalculusFor (A : Relation H) (F : Symbol k k → Relation H) : Prop :=
  Calculus F ∧ F scalarIdentity = A

/-- A choice of calculus, used only for admissible operators after Theorem 7.6. -/
def operatorCalculus (A : Relation H) : Symbol k k → Relation H :=
  if h : ∃ F, CalculusFor (k := k) A F then Classical.choose h else fun _ => zeroGraph

/-- Borel spectral evaluation. -/
def spectralValue (A : Relation H) (f : Symbol k k) : Relation H := operatorCalculus (k := k) A f

/-- Bounded transform defined by the prescribed symbol, p.35. -/
def transformZ (A : Relation H) : Relation H :=
  spectralValue (k := k) A ⟨fun z => z / (Real.sqrt (1 + ‖z‖ ^ 2) : k), by fun_prop⟩

/-- Multiplication on L2: equality of representatives almost everywhere. -/
def multiplication (mu : Measure X) (a : Symbol X k) : Relation (Lp k 2 mu) :=
  {p | ∀ᵐ x ∂mu, p.2 x = a.val x * p.1 x}

/-- Semifinite, with no sigma-finiteness assumption. -/
def Semifinite (mu : Measure X) : Prop :=
  ∀ A : Set X, MeasurableSet A → mu A = ⊤ →
    ∃ B : Set X, MeasurableSet B ∧ B ⊆ A ∧ 0 < mu B ∧ mu B < ⊤

/-- Essential boundedness. -/
def EssentiallyBounded (mu : Measure X) (a : Symbol X k) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ᵐ x ∂mu, ‖a.val x‖ ≤ c

/-- ENNReal L-infinity norm, preserving infinity. -/
def essentialNorm (mu : Measure X) (a : Symbol X k) : ℝ≥0∞ :=
  essSup (fun x => ENNReal.ofReal ‖a.val x‖) mu

/-- Measure essential range. -/
def measureEssentialRange (mu : Measure X) (a : Symbol X k) : Set k :=
  {c | ∀ e : ℝ, 0 < e → mu {x | ‖a.val x - c‖ ≤ e} ≠ 0}

/-- Correctly typed unitary unitaryGraphTransport of a boundedGraph. -/
def unitaryGraphTransport (U : H ≃ₗᵢ[k] K) (A : Relation H) : Relation K :=
  {p | (U.symm p.1, U.symm p.2) ∈ A}

/-- Closed cyclic subspace generated by bounded symbols at x. -/
def cyclic (F : Symbol X k → Relation H) (x : H) : Submodule k H :=
  (Submodule.span k {y | ∃ f, BoundedSymbol f ∧ y = value (F f) x}).topologicalClosure

example (x : H) : (x, x) ∈ (identity : Relation H) := rfl

example (A : Relation H) : graphDomain (scale (0 : k) A) = graphDomain A := by
  ext x
  simp only [graphDomain, scale, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, y, hy, _⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨0, y, hy, by simp⟩

example : graphDomain (zeroGraph : Relation H) = Set.univ := by
  ext x
  simp [graphDomain, zeroGraph]

example (mu : Measure X) (a : Symbol X k) (u v : Lp k 2 mu) :
    (u, v) ∈ multiplication mu a ↔ (∀ᵐ x ∂mu, v x = a.val x * u x) := Iff.rfl

example {d : ℕ} (z : Fin d → k) : squaredTupleNorm z = ∑ j, ‖z j‖ ^ 2 := rfl

/-- The star algebra of calculus-bounded symbols and its unital star representation. -/
def BoundedRestrictionHom (F : Symbol X k → Relation H) : Prop :=
  (∀ c, F (constant c) = scale c identity ∧ BoundedOperator (k := k) (F (constant c))) ∧
  (∀ f g, BoundedOperator (k := k) (F f) → BoundedOperator (k := k) (F g) →
    BoundedOperator (k := k) (F (plus f g)) ∧ BoundedOperator (k := k) (F (times f g)) ∧
    F (plus f g) = add (F f) (F g) ∧ F (times f g) = mul (F f) (F g)) ∧
  (∀ c f, BoundedOperator (k := k) (F f) →
    BoundedOperator (k := k) (F (scalar c f)) ∧ F (scalar c f) = scale c (F f)) ∧
  (∀ f, BoundedOperator (k := k) (F f) →
    BoundedOperator (k := k) (F (starSymbol f)) ∧ F (starSymbol f) = graphAdjoint (k := k) (F f))

/-- Part of a boundedGraph in a closed Hilbert subspace (§2.5). -/
def part (F : Symbol X k → Relation H) (S : Submodule k H) : Symbol X k → Relation S :=
  fun f => {p | (p.1.val, p.2.val) ∈ F f}

/-- Canonical zero extension from a measurable subset (§3.2). -/
def extendZero (S : Set X) (hS : MeasurableSet S) (f : Symbol S k) : Symbol X k :=
  ⟨Function.extend (Subtype.val : S → X) f.val (fun _ => 0),
    (MeasurableEmbedding.subtype_coe hS).measurable_extend f.property measurable_const⟩

/-- Restriction of the base, using the source's zero-extension construction. -/
def restrictBase (F : Symbol X k → Relation H) (S : Set X) (hS : MeasurableSet S) :
    Symbol S k → Relation H := fun f => F (extendZero S hS f)

/-- Extension from a subset by restricting the symbols. -/
def extendBase {S : Set X} (F : Symbol S k → Relation H) : Symbol X k → Relation H :=
  fun f => F (compose f Subtype.val measurable_subtype_coe)

/-- The bounded measurable symbol algebra as a subtype. -/
abbrev BoundedSymbols (X k : Type*) [MeasurableSpace X] [RCLike k] :=
  {f : Symbol X k // BoundedSymbol f}

/-- A unital scalar-linear star homomorphism on bounded symbols. Proof arguments
merely name their boundedness and do not restrict the algebraic identities. -/
def BoundedHom (L : BoundedSymbols X k → H →L[k] H) : Prop :=
  CompleteSpace H ∧
  (∀ c (hc : BoundedSymbol (constant (X := X) c)), L ⟨constant c, hc⟩ = c • ContinuousLinearMap.id k H) ∧
  (∀ f g (hf : BoundedSymbol f) (hg : BoundedSymbol g)
      (ha : BoundedSymbol (plus f g)) (hm : BoundedSymbol (times f g)),
    L ⟨plus f g, ha⟩ = L ⟨f, hf⟩ + L ⟨g, hg⟩ ∧
    L ⟨times f g, hm⟩ = (L ⟨f, hf⟩).comp (L ⟨g, hg⟩)) ∧
  (∀ f (hf : BoundedSymbol f) (hs : BoundedSymbol (starSymbol f)),
    boundedGraph (L ⟨starSymbol f, hs⟩) = graphAdjoint (k := k) (boundedGraph (L ⟨f, hf⟩)))

/-- Weak bp continuity of a bounded-symbol representation. -/
def BoundedWeakBP (L : BoundedSymbols X k → H →L[k] H) : Prop :=
  ∀ fn f (hfn : ∀ n, BoundedSymbol (fn n)) (hf : BoundedSymbol f), BP fn f →
    ∀ x y, Tendsto (fun n => inner k x (L ⟨fn n, hfn n⟩ y)) atTop (𝓝 (inner k x (L ⟨f, hf⟩ y)))

/-- Canonical algebraic extension from p.25, using e=(1+|f|)^-1. The fallback is
irrelevant since both symbols in the test are bounded for every f. -/
def algebraicExtension (L : BoundedSymbols X k → H →L[k] H) (f : Symbol X k) : Relation H :=
  if h : BoundedSymbol (regularizer f) ∧ BoundedSymbol (times (regularizer f) f) then
    mul (inverse (boundedGraph (L ⟨regularizer f, h.1⟩)))
      (boundedGraph (L ⟨times (regularizer f) f, h.2⟩))
  else zeroGraph

/-- Unital scalar-linear star homomorphism on continuous functions. -/
def ContinuousHom [TopologicalSpace X] (L : C(X, k) → H →L[k] H) : Prop :=
  CompleteSpace H ∧ L 1 = ContinuousLinearMap.id k H ∧
  (∀ (c : k) (f : C(X, k)), L (c • f) = c • L f) ∧
  (∀ f g, L (f + g) = L f + L g ∧ L (f * g) = (L f).comp (L g)) ∧
  (∀ f, boundedGraph (L (star f)) = graphAdjoint (k := k) (boundedGraph (L f)))

/-- Continuous symbols in the Borel algebra. -/
def continuousSymbol [TopologicalSpace X] [BorelSpace X] (f : C(X, k)) : Symbol X k :=
  ⟨f, f.continuous.measurable⟩

/-- Agreement with a given continuous representation. -/
def ExtendsContinuous [TopologicalSpace X] [BorelSpace X]
    (F : Symbol X k → Relation H) (L : C(X, k) → H →L[k] H) : Prop :=
  ∀ f, F (continuousSymbol f) = boundedGraph (L f)

/-- The precise regularity property of Theorem 6.4. On a compact space every
continuous function has compact calculusSupport, so the supremum ranges over C(X). -/
def RegularExtension [TopologicalSpace X] [BorelSpace X]
    (F : Symbol X k → Relation H) (L : C(X, k) → H →L[k] H) : Prop :=
  ∀ f : Symbol X k, BoundedSymbol f → RealValued f →
    (∀ t, 0 ≤ RCLike.re (f.val t)) → LowerSemicontinuous (fun t => RCLike.re (f.val t)) →
    ∀ x : H, inner k x (value (F f) x) =
      ((sSup {r : ℝ | ∃ g : C(X, k),
        (∀ t, star (g t) = g t) ∧ (∀ t, 0 ≤ RCLike.re (g t) ∧ RCLike.re (g t) ≤ RCLike.re (f.val t)) ∧
        r = RCLike.re (inner k x (L g x))} : ℝ) : k)

/-- The Baire algebra generated by continuous scalar functions (p.28). -/
def baire (k : Type*) [RCLike k] (Z : Type*) [TopologicalSpace Z] : MeasurableSpace Z :=
  ⨆ f : C(Z, k), MeasurableSpace.comap f (borel k)

/-- Continuous functions are measurable for the explicitly generated Baire algebra. -/
def continuousBaireSymbol {Z : Type*} [TopologicalSpace Z] (f : C(Z, k)) :
    @Symbol Z k (baire k Z) _ :=
  ⟨f, Measurable.of_comap_le (le_iSup (fun g : C(Z, k) => MeasurableSpace.comap g (borel k)) f)⟩

example {Z : Type*} [TopologicalSpace Z] (f : C(Z, k)) :
    (continuousBaireSymbol f).val = f := rfl

end QAlgorithms.Papers.Independent.Claimed50.P05


