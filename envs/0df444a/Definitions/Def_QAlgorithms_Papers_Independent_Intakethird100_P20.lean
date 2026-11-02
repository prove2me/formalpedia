-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P20
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T07:31:03.792088+00:00
-- url     : https://prove2.me/theorems/6088df6e-cd72-4791-b1f5-b1d22fb77812
-- title:
--   Definitions for Observables I: Stone Spectra
-- statement:
--   The objects the formalized statements of *Observables I: Stone Spectra* (arXiv:math-ph/0509020) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsFilterBase`: Proper nonempty directed bases, Definition 3.3, PDF p.38. No upward closure is built in.
--   - `IsQuasipoint`: Maximal proper filter bases, Definition 3.4, PDF p.39.
--   - `StoneSpectrum`: Underlying Stone spectrum, Definition 3.5, PDF p.40.
--   - `stoneBasic`: Membership basic sets Q_a, PDF pp.39–40.
--   - `IsDualIdeal`: Proper dual ideals, PDF pp.10–11.
--   - `IsLatticePoint`: Completely prime lattice points, Definition 3.2, PDF pp.36–37.
--   - `IsSigmaPoint`: Countable primeness, the notion of point in a sigma algebra.
--   - `IsDistributive`: Both finite distributive laws, Definition 2.1, PDF p.17.
--   - `IsOrthocomplement`: Designated orthocomplement, Definition 2.2, PDF p.20.
--   - `IsOrthomodular`: Orthomodularity in the form of Definition 2.4, PDF p.21.
--   - `LatticeCommutes`: Designated commutation relation, PDF p.21.
--   - `IsSubOrtholattice`: Proof-intended sub-ortholattices, including complements and bounds, PDF pp.24,69.
--   - `IsDistributiveOn`: Distributivity restricted to a sublattice.
--   - `IsBooleanSector`: Boolean sectors, with the proof-intended correction to Definition 2.6.
--   - `IsBooleanFilterBase`: Boolean filter bases, PDF p.69.
--   - `IsBooleanQuasipoint`: Maximal Boolean filter bases, Definition 3.13, PDF p.69.
--   - `ortholatticeGenerated`: Ortholattice generation: intersection of containing sub-ortholattices.
--   - `HasFrameLaw`: The frame law called complete distributivity in this paper, PDF pp.18,45.
--   - `IsFiniteType`: Definition 3.9, PDF p.45, for nonempty directed ranges of increasing nets.
--   - `HasDirectedMeetLaw`: Meet-continuity for nonempty increasing nets, PDF p.46.
--   - `IsSpectralFamily`: Right-continuous spectral families, Definition 2.8, PDF p.27.
--   - `IsBoundedSpectralFamily`: Bounded spectral families with both truncation endpoints.
--   - `IsMeasurableSpectralFamily`: Spectral families in a concrete sigma algebra, PDF p.12; actual set intersections.
--   - `measurableSublevels`: Measurable sublevel family, PDF p.12.
--   - `spectralCutInfimum`: Real cut infimum, PDF pp.12–13; theorems ensure finite cuts on the stated domains.
--   - `openSublevels`: Open sublevel family, PDF pp.13–14.
--   - `IsRegularSpectralFamily`: Regularity includes the closure bar in Definition 1.7, PDF p.13.
--   - `admissibleDomain`: Admissible domain, Definition 1.5, PDF p.13.
--   - `LiesOver`: Quasipoints over x use the intersection of closures, PDF pp.14,49.
--   - `openPseudoCompl`: Open pseudocomplement M minus closure U, PDF p.18.
--   - `RegularOpens`: Regular opens with inherited inclusion order.
--   - `regularizeOpen`: Regularization, PDF pp.18,56.
--   - `regularizedBase`: Image under regularization as a subset of regular opens.
--   - `BorelSets`: Concrete Boolean algebra of Borel sets.
--   - `borelSaturation`: The constructed C(B), saturation modulo meagre Borel sets, PDF p.57.
--   - `IsSigmaIdeal`: Sigma ideals with closure under countable existing joins, Definition 3.10.
--   - `LatticePresheaf`: Set-valued presheaves, Definition 3.1, PDF p.33.
--   - `IsCompletePresheaf`: Exact gluing, including empty covers and compatibility only at nonzero overlaps.
--   - `IsOrthogonalRepresentation`: Orthogonal representations in the concrete algebra, Definition 3.12, PDF pp.59–60.
--   - `spectralSumFunction`: Finite spectral-sum transform; zero coefficients are allowed, PDF p.60.
--   - `IsSigmaComplete`: Countable completeness without an arbitrary-join operation, PDF pp.50–52.
--   - `closedLine`: The closed line spanned by x, expressed intrinsically without choosing a basis.
--   - `principalQuasipoint`: Principal ideals of the lattice, PDF p.66.
--   - `DualIdeal`: Proper dual-ideal space D(L), PDF pp.10–11.
--   - `principalDualIdeal`: The principal dual ideal H_a for nonzero a.
--   - `HasIntersectionProperty`: Intersection identity on nonempty families, expressed without choosing an intersection object.
--   - `IsAbstractObservable`: Abstract observable, Definition 1.4, PDF pp.10–11. No representability is assumed.
--   - `dualSpectralValue`: The spectral cut on a proper dual ideal, PDF p.10.
--   - `IsCompletelyIncreasing`: Completely increasing functions on nonzero lattice elements, PDF pp.11–12.
--   - `extendIncreasing`: r ↦ f_r, the infimum over the elements of the ideal, PDF pp.11–12.
--   - `restrictObservable`: f ↦ r_f, evaluation at principal dual ideals, PDF pp.11–12.
--   - `CofiniteSubspaces`: Zero and the closed subspaces of finite codimension, Example 3.2, PDF p.43.
--   - `cofiniteBasic`: Basic membership interpreted in the ambient closed-subspace lattice.
--   - `compactificationBase`: Canonical extension to the one-point compactification, PDF p.49.
--   - `IsUnboundedQuasipoint`: Unbounded quasipoints contain the complements of all compact sets, PDF p.49.
--   - `latticeCommutant`: The lattice commutant from Definition 2.5, PDF p.22. The formula also defines the commutant of the empty set, which is all of L.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, https://arxiv.org/abs/math-ph/0509020v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P33

/-! Statements from de Groote, Observables I: Stone Spectra, math-ph/0509020v1.
All page numbers are PDF pages. New definitions are local to this paper;
operator projections reuse the pinned accepted Next46.P33 interface. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace
open QAlgorithms.Papers.Independent.Next46.P33 (Projection)
open scoped Topology

universe u v

/-- Proper nonempty directed bases, Definition 3.3, PDF p.38. No upward closure is built in. -/
def IsFilterBase {L : Type u} [LE L] [Bot L] (B : Set L) : Prop :=
  B.Nonempty ∧ (⊥ : L) ∉ B ∧ ∀ a ∈ B, ∀ b ∈ B, ∃ c ∈ B, c ≤ a ∧ c ≤ b

/-- Maximal proper filter bases, Definition 3.4, PDF p.39. -/
def IsQuasipoint {L : Type u} [LE L] [Bot L] (B : Set L) : Prop :=
  IsFilterBase B ∧ ∀ C : Set L, IsFilterBase C → B ⊆ C → C = B

/-- Underlying Stone spectrum, Definition 3.5, PDF p.40. -/
def StoneSpectrum (L : Type u) [LE L] [Bot L] := {B : Set L // IsQuasipoint B}

/-- Membership basic sets Q_a, PDF pp.39–40. -/
def stoneBasic {L : Type u} [LE L] [Bot L] (a : L) : Set (StoneSpectrum L) := {B | a ∈ B.val}

/-- Membership-generated topology, not the order topology. -/
instance stoneTopology {L : Type u} [LE L] [Bot L] : TopologicalSpace (StoneSpectrum L) :=
  TopologicalSpace.generateFrom (Set.range (stoneBasic : L → Set (StoneSpectrum L)))

/-- Proper dual ideals, PDF pp.10–11. -/
def IsDualIdeal {L : Type u} [Lattice L] [BoundedOrder L] (J : Set L) : Prop :=
  J.Nonempty ∧ (⊥ : L) ∉ J ∧ (∀ a ∈ J, ∀ b, a ≤ b → b ∈ J) ∧
  (∀ a ∈ J, ∀ b ∈ J, a ⊓ b ∈ J)

/-- Completely prime lattice points, Definition 3.2, PDF pp.36–37. -/
def IsLatticePoint {L : Type u} [CompleteLattice L] (p : Set L) : Prop :=
  IsDualIdeal p ∧ ∀ s : Set L, sSup s ∈ p → ∃ a ∈ s, a ∈ p

/-- Countable primeness, the notion of point in a sigma algebra. -/
def IsSigmaPoint {L : Type u} [Lattice L] [BoundedOrder L] (p : Set L) : Prop :=
  IsDualIdeal p ∧ ∀ a : ℕ → L, ∀ b : L,
    IsLUB (Set.range a) b → b ∈ p → ∃ n, a n ∈ p

/-- Both finite distributive laws, Definition 2.1, PDF p.17. -/
def IsDistributive {L : Type u} [Lattice L] : Prop :=
  (∀ a b c : L, a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)) ∧
  (∀ a b c : L, a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c))

/-- Designated orthocomplement, Definition 2.2, PDF p.20. -/
def IsOrthocomplement {L : Type u} [Lattice L] [BoundedOrder L] (perp : L → L) : Prop :=
  (∀ a, a ⊓ perp a = ⊥ ∧ a ⊔ perp a = ⊤) ∧
  (∀ a b, perp (a ⊓ b) = perp a ⊔ perp b ∧ perp (a ⊔ b) = perp a ⊓ perp b) ∧
  (∀ a, perp (perp a) = a)

/-- Orthomodularity in the form of Definition 2.4, PDF p.21. -/
def IsOrthomodular {L : Type u} [Lattice L] [BoundedOrder L] (perp : L → L) : Prop :=
  IsOrthocomplement perp ∧ ∀ a b c, b ≤ a → c ≤ perp a →
    a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)

/-- Designated commutation relation, PDF p.21. -/
def LatticeCommutes {L : Type u} [Lattice L] (perp : L → L) (a b : L) : Prop :=
  a = (a ⊓ b) ⊔ (a ⊓ perp b)

/-- Proof-intended sub-ortholattices, including complements and bounds, PDF pp.24,69. -/
def IsSubOrtholattice {L : Type u} [Lattice L] [BoundedOrder L] (perp : L → L) (S : Set L) : Prop :=
  (⊥ : L) ∈ S ∧ (⊤ : L) ∈ S ∧ (∀ a ∈ S, perp a ∈ S) ∧
  (∀ a ∈ S, ∀ b ∈ S, a ⊓ b ∈ S ∧ a ⊔ b ∈ S)

/-- Distributivity restricted to a sublattice. -/
def IsDistributiveOn {L : Type u} [Lattice L] (S : Set L) : Prop :=
  (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)) ∧
  (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c))

/-- Boolean sectors, with the proof-intended correction to Definition 2.6. -/
def IsBooleanSector {L : Type u} [Lattice L] [BoundedOrder L] (perp : L → L) (S : Set L) : Prop :=
  IsSubOrtholattice perp S ∧ IsDistributiveOn S ∧
  ∀ T : Set L, IsSubOrtholattice perp T → IsDistributiveOn T → S ⊆ T → T = S

/-- Boolean filter bases, PDF p.69. -/
def IsBooleanFilterBase {L : Type u} [Lattice L] [BoundedOrder L] (perp : L → L) (B : Set L) : Prop :=
  IsFilterBase B ∧ ∀ a ∈ B, ∀ b ∈ B, LatticeCommutes perp a b

/-- Maximal Boolean filter bases, Definition 3.13, PDF p.69. -/
def IsBooleanQuasipoint {L : Type u} [Lattice L] [BoundedOrder L] (perp : L → L) (B : Set L) : Prop :=
  IsBooleanFilterBase perp B ∧ ∀ C : Set L, IsBooleanFilterBase perp C → B ⊆ C → C = B

/-- Ortholattice generation: intersection of containing sub-ortholattices. -/
def ortholatticeGenerated {L : Type u} [Lattice L] [BoundedOrder L] (perp : L → L) (B : Set L) : Set L :=
  {a | ∀ S : Set L, IsSubOrtholattice perp S → B ⊆ S → a ∈ S}

/-- The frame law called complete distributivity in this paper, PDF pp.18,45. -/
def HasFrameLaw (L : Type u) [CompleteLattice L] : Prop :=
  ∀ a : L, ∀ s : Set L, a ⊓ sSup s = sSup ((fun b => a ⊓ b) '' s)

/-- Definition 3.9, PDF p.45, for nonempty directed ranges of increasing nets. -/
def IsFiniteType (L : Type u) [CompleteLattice L] : Prop :=
  ∀ s : Set L, s.Nonempty → DirectedOn (· ≤ ·) s →
    closure (⋃ a ∈ s, stoneBasic a) = stoneBasic (sSup s)

/-- Meet-continuity for nonempty increasing nets, PDF p.46. -/
def HasDirectedMeetLaw (L : Type u) [CompleteLattice L] : Prop :=
  ∀ a : L, ∀ s : Set L, s.Nonempty → DirectedOn (· ≤ ·) s →
    a ⊓ sSup s = sSup ((fun b => a ⊓ b) '' s)

/-- Right-continuous spectral families, Definition 2.8, PDF p.27. -/
def IsSpectralFamily {L : Type u} [CompleteLattice L] (E : ℝ → L) : Prop :=
  Monotone E ∧ (∀ t, E t = sInf (E '' Set.Ioi t)) ∧
    sInf (Set.range E) = ⊥ ∧ sSup (Set.range E) = ⊤

/-- Bounded spectral families with both truncation endpoints. -/
def IsBoundedSpectralFamily {L : Type u} [CompleteLattice L] (E : ℝ → L) : Prop :=
  IsSpectralFamily E ∧ ∃ a b : ℝ, (∀ t < a, E t = ⊥) ∧ (∀ t > b, E t = ⊤)

/-- Spectral families in a concrete sigma algebra, PDF p.12; actual set intersections. -/
def IsMeasurableSpectralFamily {M : Type u} [MeasurableSpace M] (E : ℝ → Set M) : Prop :=
  (∀ t, MeasurableSet (E t)) ∧ Monotone E ∧
  (∀ t, E t = ⋂ s : Set.Ioi t, E s.val) ∧
  (⋂ t, E t) = ∅ ∧ (⋃ t, E t) = Set.univ

/-- Measurable sublevel family, PDF p.12. -/
def measurableSublevels {M : Type u} (g : M → ℝ) (t : ℝ) : Set M := g ⁻¹' Set.Iic t

/-- Real cut infimum, PDF pp.12–13; theorems ensure finite cuts on the stated domains. -/
def spectralCutInfimum {M : Type u} (E : ℝ → Set M) (x : M) : ℝ := sInf {t | x ∈ E t}

/-- Open sublevel family, PDF pp.13–14. -/
def openSublevels {M : Type u} [TopologicalSpace M] (f : M → ℝ) (t : ℝ) : Opens M :=
  ⟨interior (f ⁻¹' Set.Iic t), isOpen_interior⟩

/-- Regularity includes the closure bar in Definition 1.7, PDF p.13. -/
def IsRegularSpectralFamily {M : Type u} [TopologicalSpace M] (E : ℝ → Opens M) : Prop :=
  IsSpectralFamily E ∧ ∀ t s : ℝ, t < s → closure (E t : Set M) ⊆ (E s : Set M)

/-- Admissible domain, Definition 1.5, PDF p.13. -/
def admissibleDomain {M : Type u} [TopologicalSpace M] (E : ℝ → Opens M) : Set M :=
  {x | ∃ t, x ∉ (E t : Set M)}

/-- Quasipoints over x use the intersection of closures, PDF pp.14,49. -/
def LiesOver {M : Type u} [TopologicalSpace M] (B : StoneSpectrum (Opens M)) (x : M) : Prop :=
  (⋂ U : {U : Opens M // U ∈ B.val}, closure (U.val : Set M)) = {x}

/-- Open pseudocomplement M minus closure U, PDF p.18. -/
def openPseudoCompl {M : Type u} [TopologicalSpace M] (U : Opens M) : Opens M :=
  ⟨(closure (U : Set M))ᶜ, isClosed_closure.isOpen_compl⟩

/-- Regular opens with inherited inclusion order. -/
def RegularOpens (M : Type u) [TopologicalSpace M] :=
  {U : Opens M // interior (closure (U : Set M)) = (U : Set M)}

instance regularOpensLE {M : Type u} [TopologicalSpace M] : LE (RegularOpens M) :=
  ⟨fun U V => U.val ≤ V.val⟩

instance regularOpensBot {M : Type u} [TopologicalSpace M] : Bot (RegularOpens M) :=
  ⟨⟨⊥, by simp⟩⟩

/-- Regularization, PDF pp.18,56. -/
def regularizeOpen {M : Type u} [TopologicalSpace M] (U : Opens M) : Opens M :=
  ⟨interior (closure (U : Set M)), isOpen_interior⟩

/-- Image under regularization as a subset of regular opens. -/
def regularizedBase {M : Type u} [TopologicalSpace M] (B : StoneSpectrum (Opens M)) : Set (RegularOpens M) :=
  {V | ∃ U ∈ B.val, regularizeOpen U = V.val}

/-- Concrete Boolean algebra of Borel sets. -/
abbrev BorelSets (M : Type u) [TopologicalSpace M] := {A : Set M // @MeasurableSet M (borel M) A}

/-- Borel-set lattice operations are actual union and intersection, PDF pp.49–50. -/
instance borelSetsLattice {M : Type u} [TopologicalSpace M] : Lattice (BorelSets M) where
  sup A B := ⟨A.val ∪ B.val, A.prop.union B.prop⟩
  le_sup_left := fun _ _ => Set.subset_union_left
  le_sup_right := fun _ _ => Set.subset_union_right
  sup_le := fun _ _ _ hA hB => Set.union_subset hA hB
  inf A B := ⟨A.val ∩ B.val, A.prop.inter B.prop⟩
  inf_le_left := fun _ _ => Set.inter_subset_left
  inf_le_right := fun _ _ => Set.inter_subset_right
  le_inf := fun _ _ _ hA hB => Set.subset_inter hA hB

/-- The Borel algebra has the actual empty and full sets as bounds, PDF p.50. -/
instance borelSetsBoundedOrder {M : Type u} [TopologicalSpace M] : BoundedOrder (BorelSets M) where
  bot := ⟨∅, @MeasurableSet.empty M (borel M)⟩
  bot_le := fun _ => Set.empty_subset _
  top := ⟨Set.univ, @MeasurableSet.univ M (borel M)⟩
  le_top := fun _ => Set.subset_univ _

/-- Sanity: meet in the Borel lattice is set intersection. -/
example {M : Type u} [TopologicalSpace M] (A B : BorelSets M) :
    (A ⊓ B).val = A.val ∩ B.val := rfl

/-- Sanity: the least Borel set is empty. -/
example {M : Type u} [TopologicalSpace M] : (⊥ : BorelSets M).val = ∅ := rfl

/-- The constructed C(B), saturation modulo meagre Borel sets, PDF p.57. -/
def borelSaturation {M : Type u} [TopologicalSpace M] (B : StoneSpectrum (Opens M)) : Set (BorelSets M) :=
  {A | ∃ U ∈ B.val, IsMeagre ((A.val \ (U : Set M)) ∪ ((U : Set M) \ A.val))}

/-- Sigma ideals with closure under countable existing joins, Definition 3.10. -/
def IsSigmaIdeal {L : Type u} [Lattice L] [BoundedOrder L] (I : Set L) : Prop :=
  I.Nonempty ∧ (∀ a ∈ I, ∀ b, b ≤ a → b ∈ I) ∧
  ∀ a : ℕ → L, (∀ n, a n ∈ I) → ∀ b, IsLUB (Set.range a) b → b ∈ I

/-- Set-valued presheaves, Definition 3.1, PDF p.33. -/
structure LatticePresheaf (L : Type u) [PartialOrder L] where
  Fiber : L → Type v
  restrict : {a b : L} → a ≤ b → Fiber b → Fiber a
  restrict_id : ∀ a (s : Fiber a), restrict (le_refl a) s = s
  restrict_comp : ∀ {a b c} (hab : a ≤ b) (hbc : b ≤ c) (s : Fiber c),
    restrict hab (restrict hbc s) = restrict (hab.trans hbc) s

/-- Exact gluing, including empty covers and compatibility only at nonzero overlaps. -/
def IsCompletePresheaf {L : Type u} [CompleteLattice L] (S : LatticePresheaf.{u,v} L) : Prop :=
  ∀ a : L, ∀ cover : Set L, ∀ hcover : sSup cover = a,
  ∀ sections : (b : cover) → S.Fiber b.val,
    (∀ b c : cover, b.val ⊓ c.val ≠ ⊥ →
      S.restrict inf_le_left (sections b) = S.restrict inf_le_right (sections c)) →
    ∃! s : S.Fiber a, ∀ b : cover,
      S.restrict (show b.val ≤ a from by rw [← hcover]; exact le_sSup b.prop) s = sections b

/-- The frozen concrete projection subtype has the zero operator as bottom, PDF p.25. -/
instance operatorProjectionBot {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (R : VonNeumannAlgebra H) : Bot (Projection R) :=
  ⟨⟨0, R.zero_mem, IsStarProjection.zero _⟩⟩

/-- Orthogonal representations in the concrete algebra, Definition 3.12, PDF pp.59–60. -/
def IsOrthogonalRepresentation {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {R : VonNeumannAlgebra H}
    {n : ℕ} (x : R.toStarSubalgebra) (c : Fin n → ℂ) (p : Fin n → Projection R) : Prop :=
  (∀ i, (p i).val ≠ 0) ∧ (∀ i j, i ≠ j → (p i).val * (p j).val = 0) ∧
    (x : H →L[ℂ] H) = ∑ i, c i • (p i).val

/-- Finite spectral-sum transform; zero coefficients are allowed, PDF p.60. -/
def spectralSumFunction {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {R : VonNeumannAlgebra H}
    {n : ℕ} (c : Fin n → ℂ) (p : Fin n → Projection R)
    (B : StoneSpectrum (Projection R)) : ℂ := by
  classical
  exact ∑ i, if p i ∈ B.val then c i else 0

/-- Sanity: a quasipoint excludes zero. -/
example {L : Type u} [LE L] [Bot L] (B : StoneSpectrum L) : (⊥ : L) ∉ B.val := B.prop.1.2.1

/-- Sanity: constant sublevels have the expected membership condition. -/
example {M : Type u} (c t : ℝ) : measurableSublevels (fun _ : M => c) t = {x | c ≤ t} := rfl

/-- Sanity: zero is an actual projection, including in the zero algebra. -/
example {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (R : VonNeumannAlgebra H) : (⊥ : Projection R).val = 0 := rfl

/-- Countable completeness without an arbitrary-join operation, PDF pp.50–52. -/
def IsSigmaComplete (L : Type u) [PartialOrder L] : Prop :=
  ∀ a : ℕ → L, ∃ b, IsLUB (Set.range a) b

/-- The closed line spanned by x, expressed intrinsically without choosing a basis. -/
def closedLine {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : H) : ClosedSubmodule ℂ H :=
  sInf {U : ClosedSubmodule ℂ H | x ∈ U}

/-- Principal ideals of the lattice, PDF p.66. -/
def principalQuasipoint {L : Type u} [LE L] (a : L) : Set L := {b | a ≤ b}

/-- Proper dual-ideal space D(L), PDF pp.10–11. -/
def DualIdeal (L : Type u) [Lattice L] [BoundedOrder L] := {J : Set L // IsDualIdeal J}

instance dualIdealTopology {L : Type u} [Lattice L] [BoundedOrder L] :
    TopologicalSpace (DualIdeal L) :=
  TopologicalSpace.generateFrom (Set.range (fun a : L => {J : DualIdeal L | a ∈ J.val}))

/-- The principal dual ideal H_a for nonzero a. -/
def principalDualIdeal {L : Type u} [Lattice L] [BoundedOrder L]
    (a : {a : L // a ≠ ⊥}) : DualIdeal L :=
  ⟨{b | a.val ≤ b}, ⟨⟨a.val, le_rfl⟩, (fun h => a.prop (le_bot_iff.mp h)),
    (fun _ hab _ hbc => hab.trans hbc), (fun _ hab _ hac => le_inf hab hac)⟩⟩

/-- Intersection identity on nonempty families, expressed without choosing an intersection object. -/
def HasIntersectionProperty {L : Type u} [Lattice L] [BoundedOrder L]
    (f : DualIdeal L → ℝ) : Prop :=
  ∀ family : Set (DualIdeal L), family.Nonempty → ∀ J : DualIdeal L,
    J.val = {a | ∀ K ∈ family, a ∈ K.val} → f J = sSup (f '' family)

/-- Abstract observable, Definition 1.4, PDF pp.10–11. No representability is assumed. -/
def IsAbstractObservable {L : Type u} [Lattice L] [BoundedOrder L]
    (f : DualIdeal L → ℝ) : Prop :=
  UpperSemicontinuous f ∧ HasIntersectionProperty f

/-- The spectral cut on a proper dual ideal, PDF p.10. -/
def dualSpectralValue {L : Type u} [Lattice L] [BoundedOrder L]
    (E : ℝ → L) (J : DualIdeal L) : ℝ := sInf {t | E t ∈ J.val}

/-- Completely increasing functions on nonzero lattice elements, PDF pp.11–12. -/
def IsCompletelyIncreasing {L : Type u} [CompleteLattice L]
    (r : {a : L // a ≠ ⊥} → ℝ) : Prop :=
  ∀ s : Set {a : L // a ≠ ⊥}, s.Nonempty → ∀ a : {a : L // a ≠ ⊥},
    IsLUB (Subtype.val '' s) a.val → r a = sSup (r '' s)

/-- r ↦ f_r, the infimum over the elements of the ideal, PDF pp.11–12. -/
def extendIncreasing {L : Type u} [Lattice L] [BoundedOrder L]
    (r : {a : L // a ≠ ⊥} → ℝ) (J : DualIdeal L) : ℝ :=
  sInf (r '' {a | a.val ∈ J.val})

/-- f ↦ r_f, evaluation at principal dual ideals, PDF pp.11–12. -/
def restrictObservable {L : Type u} [Lattice L] [BoundedOrder L]
    (f : DualIdeal L → ℝ) (a : {a : L // a ≠ ⊥}) : ℝ := f (principalDualIdeal a)

/-- Sanity: principal dual ideals retain their generator. -/
example {L : Type u} [Lattice L] [BoundedOrder L] (a : {a : L // a ≠ ⊥}) :
    a.val ∈ (principalDualIdeal a).val := le_rfl

/-- Zero and the closed subspaces of finite codimension, Example 3.2, PDF p.43. -/
def CofiniteSubspaces (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  {U : ClosedSubmodule ℂ H // U = ⊥ ∨ FiniteDimensional ℂ U.orthogonal.toSubmodule}

instance cofiniteSubspacesLE {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    LE (CofiniteSubspaces H) := ⟨fun U V => U.val ≤ V.val⟩

instance cofiniteSubspacesBot {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Bot (CofiniteSubspaces H) := ⟨⟨⊥, Or.inl rfl⟩⟩

/-- Basic membership interpreted in the ambient closed-subspace lattice. -/
def cofiniteBasic {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : ClosedSubmodule ℂ H) : Set (StoneSpectrum (CofiniteSubspaces H)) :=
  {B | ∃ V ∈ B.val, V.val = U}

/-- Canonical extension to the one-point compactification, PDF p.49. -/
def compactificationBase {M : Type u} [TopologicalSpace M]
    (B : StoneSpectrum (Opens M)) : Set (Opens (OnePoint M)) :=
  {V | ∃ U ∈ B.val, (U : Set M) = ((↑) : M → OnePoint M) ⁻¹' (V : Set (OnePoint M))}

/-- Unbounded quasipoints contain the complements of all compact sets, PDF p.49. -/
def IsUnboundedQuasipoint {M : Type u} [TopologicalSpace M]
    (B : StoneSpectrum (Opens M)) : Prop :=
  ∀ K : Set M, IsCompact K → ∃ U ∈ B.val, (U : Set M) = Kᶜ

/-- Sanity: the cofinite lattice explicitly contains its zero even in infinite dimension. -/
example {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    (⊥ : CofiniteSubspaces H).val = ⊥ := rfl

/-- The lattice commutant from Definition 2.5, PDF p.22.
The formula also defines the commutant of the empty set, which is all of L. -/
def latticeCommutant {L : Type u} [Lattice L] (perp : L → L) (S : Set L) : Set L :=
  {b | ∀ a ∈ S, LatticeCommutes perp a b}

/-- Sanity: the commutant of a singleton tests the designated commutation relation. -/
example {L : Type u} [Lattice L] (perp : L → L) (a b : L) :
    b ∈ latticeCommutant perp {a} ↔ LatticeCommutes perp a b := by
  simp [latticeCommutant]

-- BEGIN DRAFT THEOREMS
end QAlgorithms.Papers.Independent.Intakethird100.P20


