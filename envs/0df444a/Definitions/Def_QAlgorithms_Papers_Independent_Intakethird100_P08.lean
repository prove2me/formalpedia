-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P08
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P08
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T04:24:59.888649+00:00
-- url     : https://prove2.me/theorems/866ef046-6c60-44bb-baaf-78d4dfa21bec
-- title:
--   Definitions for On Cohomology theory for topological groups
-- statement:
--   The objects the formalized statements of *On Cohomology theory for topological groups* (arXiv:1009.4519) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ContinuousModule`: A continuous action by additive automorphisms (PDF p. 5, Section 2). The identity and composition laws express the homomorphism explicitly: Mathlib gives AddAut A an additive group law, so A ≃+ A is not a multiplicative monoid suitable as the target of G →* (A ≃+ A).
--   - `IsCrossedHom`: Pointwise, everywhere-defined crossed homomorphisms (PDF p. 11).
--   - `IsLocallyContinuousMeasurable`: Borel measurability and continuity on an open identity neighborhood (PDF p. 8).
--   - `locallyContinuousOneCocycles`: The actual locally continuous measurable one-cocycles, not their quotient (PDF p. 11).
--   - `continuousOneCocycles`: The continuous one-cocycles, with the action retained (PDF p. 11).
--   - `IsLocallySplitSequence`: Closed kernel embedding, open quotient, algebraic exactness, and an actual continuous local section (PDF pp. 9--10, Definition 2).
--   - `LocalCocycle`: Normalized coordinates for a locally continuous measurable two-cocycle. All Section 4 standing hypotheses are explicit parameters (PDF pp. 12--14). Normalization is only for this representative, not for the source cochain complex.
--   - `ExtensionPoint`: Separate carrier for the twisted extension; it does not inherit the global product topology or a topological-group instance (PDF pp. 12--14).
--   - `actionTwistedMul`: The explicit twisted multiplication with the fixed coefficient action (PDF p. 14). Renew46.P18.twistedMul has trivial action and cannot replace this operation for a general continuous G-module.
--   - `twistedInv`: The corrected inverse (PDF p. 14). Printed: second coordinate e_G and an inconsistent variable s. Changed to g^-1 and -g^-1.(a+F(g,g^-1)), forced by multiplication; even F=0,a=0 contradicts the printed second coordinate.
--   - `identityPoint`: Identity in normalized twisted coordinates (PDF pp. 12--14).
--   - `kernelInclusion`: Kernel inclusion (PDF p. 13).
--   - `quotientProjection`: Quotient projection (PDF p. 13).
--   - `extensionCoordinates`: Underlying coordinate bijection, used only for the product sigma algebra in Proposition 4(v), not for a global product topology (PDF p. 14).
--   - `translatedRectangles`: All left translates of the local rectangular neighborhood base, exactly as in Sections 4.1--4.2 (PDF pp. 12--13).
--   - `innerConjugation`: Inner conjugation in the explicit algebraic coordinates (PDF p. 13).
--   - `IsNonnegativeTest`: Real nonnegative continuous functions of compact support (PDF p. 14). Compact support is the closure of the nonzero locus.
--   - `leftTranslate`: The source translation convention f_x(s)=f(xs) (PDF p. 14).
--   - `coverCosts`: Costs of all finite domination covers, allowing nonnegative coefficients as in Definition 4 (PDF p. 14). The empty cover is allowed.
--   - `approximateIntegral`: Approximate integral (f;g), on the nonnegative cone only (Definition 4, PDF p. 14). Theorems require a nonzero denominator test. Outside that domain sInf is Lean's total operation; its default value has no analytic meaning.
--   - `normalizedIntegral`: I_phi(f)=(f;phi)/(g;phi), with g fixed (Definition 5, PDF p. 14). All uses below require both g and phi to be nonzero nonnegative test functions.
--   - `IsPositiveInvariantIntegral`: A nonzero positive real linear integral on C_c(E), invariant under every source left translation (PDF pp. 14, 17). The translated test is required to exist, so the invariance condition cannot hold vacuously.
--   - `IsLeftInvariantMeasure`: The left-invariant locally finite Borel measure properties explicitly used in Remark 4 (PDF p. 17). No product-Haar assertion is included.
--   - `IsLocalSteinhausSet`: Every hypothesis of Proposition 6 (PDF p. 18), including symmetry, relative compactness, both closure factors, identity membership and finite positive mass. Measures take values in ENNReal.
--   - `localConvolution`: The actual local convolution mass (PDF p. 19). On the Proposition 6 domain, every mass is finite before conversion to a real number.
-- source:
--   On Cohomology theory for topological groups, arXiv:1009.4519v1, https://arxiv.org/abs/1009.4519v1

import Mathlib

/-!
Statements from Khedekar--Rajan, arXiv:1009.4519v1.
The local definitions below are specific to this paper. In particular, the topology
on the twisted extension is constructed from translated rectangles; continuity of
its group operations is never a hypothesis. See HARD.md for deferred nodes.
-/

namespace QAlgorithms.Papers.Independent.Intakethird100.P08

open Set MeasureTheory
open scoped BigOperators Topology CompactlySupported

/-- A continuous action by additive automorphisms (PDF p. 5, Section 2).
The identity and composition laws express the homomorphism explicitly:
Mathlib gives AddAut A an additive group law, so A ≃+ A is not a
multiplicative monoid suitable as the target of G →* (A ≃+ A). -/
structure ContinuousModule (G A : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] where
  action : G → (A ≃+ A)
  action_one : action 1 = AddEquiv.refl A
  action_mul : ∀ g h, action (g * h) = (action h).trans (action g)
  continuous_action : Continuous (fun p : G × A => action p.1 p.2)

section DegreeOne

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace A] [BorelSpace A]

/-- Pointwise, everywhere-defined crossed homomorphisms (PDF p. 11). -/
def IsCrossedHom (rho : ContinuousModule G A) (c : G → A) : Prop :=
  ∀ s t, c (s * t) = c s + rho.action s (c t)

/-- Borel measurability and continuity on an open identity neighborhood (PDF p. 8). -/
def IsLocallyContinuousMeasurable (c : G → A) : Prop :=
  Measurable c ∧ ∃ U : Set G, IsOpen U ∧ 1 ∈ U ∧ ContinuousOn c U

/-- The actual locally continuous measurable one-cocycles, not their quotient (PDF p. 11). -/
def locallyContinuousOneCocycles (rho : ContinuousModule G A) : Set (G → A) :=
  {c | IsLocallyContinuousMeasurable c ∧ IsCrossedHom rho c}

/-- The continuous one-cocycles, with the action retained (PDF p. 11). -/
def continuousOneCocycles (rho : ContinuousModule G A) : Set (G → A) :=
  {c | Continuous c ∧ IsCrossedHom rho c}

example (rho : ContinuousModule G A) : IsCrossedHom rho (fun _ => 0) := by
  intro s t
  simp

example (rho : ContinuousModule G A) :
    (fun _ => 0) ∈ continuousOneCocycles rho := by
  exact ⟨continuous_const, by intro s t; simp⟩

end DegreeOne

section Sections

variable {K E Q : Type*} [Group K] [Group E] [Group Q]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace Q]
  [IsTopologicalGroup K] [IsTopologicalGroup E] [IsTopologicalGroup Q]

/-- Closed kernel embedding, open quotient, algebraic exactness, and an actual
continuous local section (PDF pp. 9--10, Definition 2). -/
def IsLocallySplitSequence (i : K →* E) (p : E →* Q) : Prop :=
  Continuous i ∧ Continuous p ∧ Topology.IsClosedEmbedding i ∧ IsOpenMap p ∧
  Function.Surjective p ∧ Set.range i = {x | p x = 1} ∧
  ∃ U : Set Q, IsOpen U ∧ 1 ∈ U ∧
    ∃ sigma : U → E, Continuous sigma ∧ ∀ u, p (sigma u) = u.val

example (i : K →* E) (p : E →* Q) (h : IsLocallySplitSequence i p) :
    Function.Surjective p := h.2.2.2.2.1

end Sections

/-- Normalized coordinates for a locally continuous measurable two-cocycle.
All Section 4 standing hypotheses are explicit parameters (PDF pp. 12--14).
Normalization is only for this representative, not for the source cochain complex. -/
structure LocalCocycle (G A : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] where
  coefficients : ContinuousModule G A
  cocycle : G × G → A
  measurable_cocycle : Measurable cocycle
  cocycle_identity : ∀ g h k,
    coefficients.action g (cocycle (h, k)) + cocycle (g, h * k) =
      cocycle (g, h) + cocycle (g * h, k)
  normalized_left : ∀ g, cocycle (1, g) = 0
  normalized_right : ∀ g, cocycle (g, 1) = 0
  identityNeighborhood : Set G
  isOpen_identityNeighborhood : IsOpen identityNeighborhood
  one_mem_identityNeighborhood : 1 ∈ identityNeighborhood
  continuous_cocycle :
    ContinuousOn cocycle (identityNeighborhood ×ˢ identityNeighborhood)

section ConstructedExtension

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A]
  [MeasurableSpace A] [BorelSpace A]

/-- Sanity: the zero representative supplies a genuine instance for every
continuous coefficient action; the LocalCocycle hypotheses are nonvacuous. -/
example (rho : ContinuousModule G A) : Nonempty (LocalCocycle G A) := by
  refine ⟨{
    coefficients := rho
    cocycle := fun _ => 0
    measurable_cocycle := measurable_const
    cocycle_identity := ?_
    normalized_left := ?_
    normalized_right := ?_
    identityNeighborhood := Set.univ
    isOpen_identityNeighborhood := isOpen_univ
    one_mem_identityNeighborhood := Set.mem_univ 1
    continuous_cocycle := continuousOn_const }⟩
  · intro g h k
    simp
  · intro g
    rfl
  · intro g
    rfl

/-- Separate carrier for the twisted extension; it does not inherit the global
product topology or a topological-group instance (PDF pp. 12--14). -/
structure ExtensionPoint (D : LocalCocycle G A) where
  coefficient : A
  base : G

/-- The explicit twisted multiplication with the fixed coefficient action
(PDF p. 14). Renew46.P18.twistedMul has trivial action and cannot replace this
operation for a general continuous G-module. -/
def actionTwistedMul (D : LocalCocycle G A) (x y : ExtensionPoint D) : ExtensionPoint D :=
  ⟨x.coefficient + D.coefficients.action x.base y.coefficient +
    D.cocycle (x.base, y.base), x.base * y.base⟩

/-- The corrected inverse (PDF p. 14). Printed: second coordinate e_G and an
inconsistent variable s. Changed to g^-1 and -g^-1.(a+F(g,g^-1)), forced by
multiplication; even F=0,a=0 contradicts the printed second coordinate. -/
def twistedInv (D : LocalCocycle G A) (x : ExtensionPoint D) : ExtensionPoint D :=
  ⟨D.coefficients.action (x.base⁻¹)
    (-(x.coefficient + D.cocycle (x.base, x.base⁻¹))), x.base⁻¹⟩

/-- Identity in normalized twisted coordinates (PDF pp. 12--14). -/
def identityPoint (D : LocalCocycle G A) : ExtensionPoint D := ⟨0, 1⟩

/-- Kernel inclusion (PDF p. 13). -/
def kernelInclusion (D : LocalCocycle G A) (a : A) : ExtensionPoint D := ⟨a, 1⟩

/-- Quotient projection (PDF p. 13). -/
def quotientProjection (D : LocalCocycle G A) (x : ExtensionPoint D) : G := x.base

/-- Underlying coordinate bijection, used only for the product sigma algebra
in Proposition 4(v), not for a global product topology (PDF p. 14). -/
def extensionCoordinates (D : LocalCocycle G A) (x : ExtensionPoint D) : A × G :=
  (x.coefficient, x.base)

/-- All left translates of the local rectangular neighborhood base, exactly
as in Sections 4.1--4.2 (PDF pp. 12--13). -/
def translatedRectangles (D : LocalCocycle G A) : Set (Set (ExtensionPoint D)) :=
  {V | ∃ (x : ExtensionPoint D) (UA : Set A) (UG : Set G),
    IsOpen UA ∧ 0 ∈ UA ∧ IsOpen UG ∧ 1 ∈ UG ∧
    ContinuousOn D.cocycle (UG ×ˢ UG) ∧
    V = (actionTwistedMul D x) '' {y | y.coefficient ∈ UA ∧ y.base ∈ UG}}

/-- The source's topology generated by its translated local rectangles (PDF p. 13). -/
instance extensionTopology (D : LocalCocycle G A) : TopologicalSpace (ExtensionPoint D) :=
  TopologicalSpace.generateFrom (translatedRectangles D)

/-- Borel sigma algebra for the constructed topology (PDF p. 13). -/
instance extensionMeasurableSpace (D : LocalCocycle G A) :
    MeasurableSpace (ExtensionPoint D) := borel (ExtensionPoint D)

instance extensionBorelSpace (D : LocalCocycle G A) : BorelSpace (ExtensionPoint D) :=
  ⟨rfl⟩

/-- Inner conjugation in the explicit algebraic coordinates (PDF p. 13). -/
def innerConjugation (D : LocalCocycle G A) (x y : ExtensionPoint D) : ExtensionPoint D :=
  actionTwistedMul D (actionTwistedMul D x y) (twistedInv D x)

example (D : LocalCocycle G A) : D.cocycle (1, 1) = 0 := D.normalized_left 1

example (D : LocalCocycle G A) (x y : ExtensionPoint D) :
    (actionTwistedMul D x y).base = x.base * y.base := rfl

example (D : LocalCocycle G A) (x : ExtensionPoint D) :
    (twistedInv D x).base = x.base⁻¹ := rfl

example (D : LocalCocycle G A) (a : A) :
    quotientProjection D (kernelInclusion D a) = 1 := rfl

example (D : LocalCocycle G A) (x : ExtensionPoint D) :
    actionTwistedMul D (identityPoint D) x = x := by
  cases x
  simp [actionTwistedMul, identityPoint, D.normalized_left, D.coefficients.action_one]

/-- Real nonnegative continuous functions of compact support (PDF p. 14).
Compact support is the closure of the nonzero locus. -/
def IsNonnegativeTest (D : LocalCocycle G A) (f : ExtensionPoint D → ℝ) : Prop :=
  Continuous f ∧ HasCompactSupport f ∧ ∀ x, 0 ≤ f x

example (D : LocalCocycle G A) : IsNonnegativeTest D (fun _ => 0) := by
  refine ⟨continuous_const, ?_, fun _ => le_rfl⟩
  simp [HasCompactSupport]

/-- The source translation convention f_x(s)=f(xs) (PDF p. 14). -/
def leftTranslate (D : LocalCocycle G A) (f : ExtensionPoint D → ℝ)
    (x : ExtensionPoint D) : ExtensionPoint D → ℝ := fun s => f (actionTwistedMul D x s)

/-- Costs of all finite domination covers, allowing nonnegative coefficients
as in Definition 4 (PDF p. 14). The empty cover is allowed. -/
def coverCosts (D : LocalCocycle G A) (f g : ExtensionPoint D → ℝ) : Set ℝ :=
  {r | ∃ (n : ℕ) (c : Fin n → ℝ) (u : Fin n → ExtensionPoint D),
    (∀ j, 0 ≤ c j) ∧
    (∀ s, f s ≤ ∑ j, c j * g (actionTwistedMul D (u j) s)) ∧ r = ∑ j, c j}

/-- Approximate integral (f;g), on the nonnegative cone only (Definition 4,
PDF p. 14). Theorems require a nonzero denominator test. Outside that domain
sInf is Lean's total operation; its default value has no analytic meaning. -/
noncomputable def approximateIntegral (D : LocalCocycle G A)
    (f g : ExtensionPoint D → ℝ) : ℝ := sInf (coverCosts D f g)

/-- I_phi(f)=(f;phi)/(g;phi), with g fixed (Definition 5, PDF p. 14).
All uses below require both g and phi to be nonzero nonnegative test functions. -/
noncomputable def normalizedIntegral (D : LocalCocycle G A)
    (g phi f : ExtensionPoint D → ℝ) : ℝ :=
  approximateIntegral D f phi / approximateIntegral D g phi

example (D : LocalCocycle G A) (f : ExtensionPoint D → ℝ) (x s : ExtensionPoint D) :
    leftTranslate D f x s = f (actionTwistedMul D x s) := rfl

example (D : LocalCocycle G A) (g : ExtensionPoint D → ℝ) :
    0 ∈ coverCosts D (fun _ => 0) g := by
  refine ⟨0, (fun j => Fin.elim0 j), (fun j => Fin.elim0 j), ?_, ?_, ?_⟩
  · intro j
    exact Fin.elim0 j
  · intro s
    simp
  · simp

example (D : LocalCocycle G A) (g phi f : ExtensionPoint D → ℝ) :
    normalizedIntegral D g phi f =
      approximateIntegral D f phi / approximateIntegral D g phi := rfl

/-- A nonzero positive real linear integral on C_c(E), invariant under every
source left translation (PDF pp. 14, 17). The translated test is required to
exist, so the invariance condition cannot hold vacuously. -/
def IsPositiveInvariantIntegral (D : LocalCocycle G A)
    (I : C_c(ExtensionPoint D, ℝ) →ₗ[ℝ] ℝ) : Prop :=
  I ≠ 0 ∧
  (∀ f : C_c(ExtensionPoint D, ℝ), (∀ s, 0 ≤ f s) → 0 ≤ I f) ∧
  ∀ (f : C_c(ExtensionPoint D, ℝ)) (x : ExtensionPoint D),
    ∃ fx : C_c(ExtensionPoint D, ℝ),
      (∀ s, fx s = f (actionTwistedMul D x s)) ∧ I fx = I f

/-- The left-invariant locally finite Borel measure properties explicitly
used in Remark 4 (PDF p. 17). No product-Haar assertion is included. -/
def IsLeftInvariantMeasure (D : LocalCocycle G A)
    (mu : Measure (ExtensionPoint D)) : Prop :=
  mu ≠ 0 ∧
  (∀ (x : ExtensionPoint D) (W : Set (ExtensionPoint D)),
    MeasurableSet W → IsCompact (closure W) →
      mu ((actionTwistedMul D x) '' W) = mu W) ∧
  ∀ K : Set (ExtensionPoint D), IsCompact K → mu K < ⊤

example (D : LocalCocycle G A) :
    ¬ IsPositiveInvariantIntegral D (0 : C_c(ExtensionPoint D, ℝ) →ₗ[ℝ] ℝ) := by
  intro h
  exact h.1 rfl

example (D : LocalCocycle G A) :
    ¬ IsLeftInvariantMeasure D (0 : Measure (ExtensionPoint D)) := by
  intro h
  exact h.1 rfl

/-- Every hypothesis of Proposition 6 (PDF p. 18), including symmetry,
relative compactness, both closure factors, identity membership and finite
positive mass. Measures take values in ENNReal. -/
def IsLocalSteinhausSet (D : LocalCocycle G A) (mu : Measure (ExtensionPoint D))
    (U : Set G) (M : Set (ExtensionPoint D)) : Prop :=
  MeasurableSet M ∧
  (∀ x : ExtensionPoint D, x ∈ M ↔ twistedInv D x ∈ M) ∧
  M ⊆ (quotientProjection D) ⁻¹' U ∧
  IsOpen U ∧ 1 ∈ U ∧ (∀ g : G, g ∈ U ↔ g⁻¹ ∈ U) ∧
  IsCompact (closure U) ∧
  (∀ g ∈ closure U, ∀ h ∈ closure U, g * h ∈ D.identityNeighborhood) ∧
  identityPoint D ∈ M ∧ 0 < mu M ∧ mu M < ⊤

example (D : LocalCocycle G A) (mu : Measure (ExtensionPoint D)) (U : Set G) :
    ¬ IsLocalSteinhausSet D mu U ∅ := by
  intro h
  exact h.2.2.2.2.2.2.2.2.1

/-- The actual local convolution mass (PDF p. 19). On the Proposition 6
domain, every mass is finite before conversion to a real number. -/
noncomputable def localConvolution (D : LocalCocycle G A)
    (mu : Measure (ExtensionPoint D)) (M : Set (ExtensionPoint D))
    (x : ExtensionPoint D) : ℝ := (mu (M ∩ (actionTwistedMul D x) '' M)).toReal

example (D : LocalCocycle G A) (mu : Measure (ExtensionPoint D))
    (M : Set (ExtensionPoint D)) (x : ExtensionPoint D) :
    localConvolution D mu M x = (mu (M ∩ (actionTwistedMul D x) '' M)).toReal := rfl

end ConstructedExtension

end QAlgorithms.Papers.Independent.Intakethird100.P08


