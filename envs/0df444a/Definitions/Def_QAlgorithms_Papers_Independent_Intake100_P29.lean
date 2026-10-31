-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P29
-- name    : QAlgorithms_Papers_Independent_Intake100_P29
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T17:28:36.509523+00:00
-- url     : https://prove2.me/theorems/f1b56c06-370e-475b-8473-27a68cf30150
-- title:
--   Definitions for Blocks of cyclotomic Hecke algebras
-- statement:
--   The objects the formalized statements of *Blocks of cyclotomic Hecke algebras* (arXiv:math/0607451) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `row`: Native YoungDiagram rows are zero outside the finite shape.
--   - `partSize`: Partition size reuses the native diagram cardinality.
--   - `Multipartition`: Ordered r-tuples of partitions (PDF p. 3).
--   - `size`: Total number of nodes.
--   - `Node`: All three coordinates are zero based.
--   - `nodeDiagram`: Nodes are counted individually, even when their residues coincide.
--   - `partDiagram`: Ordinary diagrams reuse Mathlib cells, for computing cores.
--   - `column`: Column lengths reuse the native Young-diagram accessor.
--   - `rimHook`: The southeast rim hook attached to x (PDF p. 6).
--   - `rimHookSize`: Source rim-hook length is its actual cardinality (PDF p. 6).
--   - `legLength`: Leg length uses the column, not the row, of the root node.
--   - `foot`: The foot of a hook at a diagram node (PDF p. 6).
--   - `handColumn`: Column of the wrapped hook's hand.
--   - `SameHookRemainder`: Equality of the two diagrams after removing the specified hooks.
--   - `dominates`: Dominance in the orientation of PDF p. 3.
--   - `strictlyDominates`: The strict dominance condition in Definition 2.5.
--   - `parameterT`: The generic deformation indeterminate.
--   - `deformedParameter`: The exact X_a of PDF p. 5, including the additional t-1 for zero Q_a.
--   - `deformedResidue`: O-residue; negative contents use integer powers (PDF p. 6).
--   - `tOneOrder`: Order at t=1 computed from reduced numerator and denominator. Zero has the root-multiplicity API default 0; this is never used as a valuation of zero. Every contributing compatible off-diagonal pair in Definition 2.5 has distinct deformed foot residues. See the domain audit in MODERATION_NOTES.md.
--   - `jantzenCoefficient`: The literal signed double sum of Definition 2.5 (PDF p. 6).
--   - `JantzenEquivalent`: Definition 2.8: linkage through same-size multipartitions, in either direction.
--   - `fieldResidue`: Field-valued residues, for q≠1 and nonzero Q, from PDF p. 7.
--   - `FieldResidueEquivalent`: Equality of residue multisets, retaining repeated residues.
--   - `quantumCharacteristic`: Least k≥2 for which the geometric sum vanishes, or 0 for infinity.
--   - `chargedResidue`: Charged residues of section 3; ZMod 0 is the integer-content case.
--   - `ChargedResidueEquivalent`: Charged residue equivalence, counting nodes rather than distinct values.
--   - `primePowerMultiplicity`: ν'_p(h)=p^{v_p(h)}, or 1 in characteristic zero (PDF p. 11). Only nonzero h is used in the statements.
--   - `IntercomponentPattern`: Intercomponent pattern of 3.6(a); common remainders and distinct components force both components to change, as required by the printed hypothesis.
--   - `SingleComponentPattern`: Pattern in 3.6(b) and 4.2: z=(i,m,a), m<j, e divides h_z, and the hook wrapped onto the common remainder has its hand in column m.
--   - `singleComponentFormula`: Both signed branches; the difference can vanish.
--   - `CoreRemoval`: One ordinary e-rim-hook removal. Infinity (e=0) permits no removals.
--   - `partitionCore`: Compute the e-core by minimizing size among successive e-hook removals. This is the terminal packed abacus of PDF p. 11; order independence is the ordinary partition-core property, not an extra theorem hypothesis.
--   - `multicore`: Componentwise e-core (Definition 3.8, PDF p. 14).
--   - `coreWeight`: Number of removed e-hooks; infinite quantum characteristic gives zero.
--   - `maximumCoreWeight`: The attained maximum over the nonempty same-size residue class. All possible weights are in [0,|λ|], so a finite filter suffices.
--   - `ReducedMulticore`: Definition 3.15 through condition 3.14(a), in the class of the same total size.
--   - `betaSet`: Charged beta numbers. Zero-based row i corresponds to source row i+1.
--   - `RunnerTransfer`: A legal transfer on packed abacuses: remove the lowest bead on runner i and place it at the first gap on runner j. For e=0 each runner has one integer position, so the same conditions are precisely the occupancy guards.
--   - `CoreSwap`: Definition 3.10(a) as a legal relation. Both opposite transfers must exist and produce packed abacuses; unchanged components are fixed. There is no assigned output for an illegal or inconsistent swap.
--   - `Vector`: Coordinate vector spaces are finite dimensional.
--   - `AffineModule`: Finite-dimensional right modules for the extended affine Hecke algebra in m+1 Laurent variables (PDF pp. 1,8--9). T_i has the literal quadratic (T_i+q)(T_i-1)=0 from p. 3. Changing standard Bernstein generators by G_i=-T_i leaves T_i X_i T_i=q X_(i+1) unchanged. No Murphy recursion, Specht family or Schur normalization enters this definition.
--   - `AffineMorphism`: A morphism commutes with all right actions v ↦ vT_i and v ↦ vX_i.
--   - `Simple`: Nonzero simple right modules, expressed through invariant linear subspaces. In finite dimensions invariance under invertible X_i also gives invariance under X_i inverse.
--   - `ModuleIso`: Isomorphism makes linkage independent of coordinate choices.
--   - `FactorsCyclotomic`: Factoring through the actual cyclotomic quotient is exactly annihilation by the cyclotomic polynomial (PDF p. 1). Parameter repetitions are retained.
--   - `NonsplitExtension`: Nonsplit 0→D→E→D'→0. P restricts E only when extensions are taken in a cyclotomic quotient category. A splitting must be a module morphism.
--   - `Linkage`: Block linkage on isomorphism classes of simple finite-dimensional modules. P restricts vertices, R restricts middle terms. Iso edges identify different coordinate representatives of the same simple module (PDF pp. 1,4).
--   - `LaurentPolynomial`: Laurent polynomials are finite coefficient families of integer exponents.
--   - `SymmetricLaurent`: Symmetric Laurent polynomials, with no orbit-sum multiplicity factors that would fail in positive characteristic.
--   - `evaluateLaurent`: Evaluation at commuting invertible X_i, using an ordered product because the surrounding matrix algebra itself is not commutative.
--   - `SameCentralCharacter`: Equal central characters via the actual symmetric Laurent centre identified on PDF pp. 2,8. Scalar action is part of this conclusion.
-- source:
--   Blocks of cyclotomic Hecke algebras, arXiv:math/0607451v4, https://arxiv.org/abs/math/0607451v4

import Mathlib

/-!
Lyle--Mathas, Blocks of cyclotomic Hecke algebras, arXiv:math/0607451v4.
YoungDiagram and Matrix are reused from Mathlib; the remaining definitions
are confined to this paper. Diagram coordinates and component
indices are zero based; add one to obtain source coordinates. The natural
number 0 represents infinite quantum characteristic, or characteristic zero.
-/

namespace QAlgorithms.Papers.Independent.Intake100.P29

noncomputable section

open scoped BigOperators Classical

/-- Native YoungDiagram rows are zero outside the finite shape. -/
def row (L : YoungDiagram) (i : ℕ) : ℕ := L.rowLen i

/-- Partition size reuses the native diagram cardinality. -/
def partSize (L : YoungDiagram) : ℕ := L.card

example : partSize (⊥ : YoungDiagram) = 0 := by
  simp [partSize, YoungDiagram.card]

/-- Ordered r-tuples of partitions (PDF p. 3). -/
abbrev Multipartition (r : ℕ) := Fin r → YoungDiagram

/-- Total number of nodes. -/
def size {r : ℕ} (L : Multipartition r) : ℕ := ∑ a, partSize (L a)

/-- All three coordinates are zero based. -/
structure Node (r : ℕ) where
  comp : Fin r
  row : ℕ
  col : ℕ
  deriving DecidableEq

/-- Nodes are counted individually, even when their residues coincide. -/
def nodeDiagram {r : ℕ} (L : Multipartition r) : Finset (Node r) :=
  Finset.univ.biUnion fun a => (L a).cells.image fun ij => ⟨a, ij.1, ij.2⟩

/-- Ordinary diagrams reuse Mathlib cells, for computing cores. -/
def partDiagram (L : YoungDiagram) : Finset (ℕ × ℕ) := L.cells

/-- Column lengths reuse the native Young-diagram accessor. -/
def column (L : YoungDiagram) (j : ℕ) : ℕ := L.colLen j

/-- The southeast rim hook attached to x (PDF p. 6). -/
def rimHook {r : ℕ} (L : Multipartition r) (x : Node r) : Finset (Node r) :=
  (nodeDiagram L).filter fun y => y.comp = x.comp ∧ x.row ≤ y.row ∧ x.col ≤ y.col ∧
    ¬(⟨y.comp, y.row + 1, y.col + 1⟩ : Node r) ∈ nodeDiagram L

/-- Source rim-hook length is its actual cardinality (PDF p. 6). -/
def rimHookSize {r : ℕ} (L : Multipartition r) (x : Node r) : ℕ :=
  (rimHook L x).card

/-- Leg length uses the column, not the row, of the root node. -/
def legLength {r : ℕ} (L : Multipartition r) (x : Node r) : ℕ :=
  column (L x.comp) x.col - (x.row + 1)

/-- The foot of a hook at a diagram node (PDF p. 6). -/
def foot {r : ℕ} (L : Multipartition r) (x : Node r) : Node r :=
  ⟨x.comp, column (L x.comp) x.col - 1, x.col⟩

/-- Column of the wrapped hook's hand. -/
def handColumn {r : ℕ} (L : Multipartition r) (x : Node r) : ℕ :=
  row (L x.comp) x.row - 1

/-- Equality of the two diagrams after removing the specified hooks. -/
def SameHookRemainder {r : ℕ} (L M : Multipartition r) (x y : Node r) : Prop :=
  nodeDiagram L \ rimHook L x = nodeDiagram M \ rimHook M y

/-- Dominance in the orientation of PDF p. 3. -/
def dominates {r : ℕ} (L M : Multipartition r) : Prop :=
  ∀ a : Fin r, ∀ k : ℕ,
    (∑ b ∈ Finset.univ.filter (fun b : Fin r => b < a), partSize (M b)) +
        ((M a).rowLens.take k).sum ≤
    (∑ b ∈ Finset.univ.filter (fun b : Fin r => b < a), partSize (L b)) +
        ((L a).rowLens.take k).sum

/-- The strict dominance condition in Definition 2.5. -/
def strictlyDominates {r : ℕ} (L M : Multipartition r) : Prop :=
  dominates L M ∧ L ≠ M

variable {F : Type} [Field F]

/-- The generic deformation indeterminate. -/
def parameterT (F : Type) [Field F] : RatFunc F :=
  algebraMap (Polynomial F) (RatFunc F) Polynomial.X

/-- The exact X_a of PDF p. 5, including the additional t-1 for zero Q_a. -/
def deformedParameter {r : ℕ} (n : ℕ) (Q : Fin r → F) (a : Fin r) : RatFunc F :=
  (if Q a = 0 then parameterT F - 1 else algebraMap F (RatFunc F) (Q a)) *
    parameterT F ^ (n * (a.val + 1))

/-- O-residue; negative contents use integer powers (PDF p. 6). -/
def deformedResidue {r : ℕ} (n : ℕ) (q : F) (Q : Fin r → F)
    (x : Node r) : RatFunc F :=
  (algebraMap F (RatFunc F) q * parameterT F) ^ ((x.col : ℤ) - x.row) *
    deformedParameter n Q x.comp

/-- Order at t=1 computed from reduced numerator and denominator. Zero has the
root-multiplicity API default 0; this is never used as a valuation of zero.
Every contributing compatible off-diagonal pair in Definition 2.5 has distinct
deformed foot residues. See the domain audit in MODERATION_NOTES.md. -/
def tOneOrder (f : RatFunc F) : ℤ :=
  (f.num.rootMultiplicity 1 : ℤ) - f.denom.rootMultiplicity 1

/-- The literal signed double sum of Definition 2.5 (PDF p. 6). -/
def jantzenCoefficient {r : ℕ} (q : F) (Q : Fin r → F)
    (L M : Multipartition r) : ℤ :=
  if strictlyDominates L M then
    ∑ x ∈ nodeDiagram L, ∑ y ∈ (nodeDiagram M).filter (fun y => SameHookRemainder L M x y),
      (-1 : ℤ) ^ (legLength L x + legLength M y) *
        tOneOrder (deformedResidue (size L) q Q (foot L x) -
          deformedResidue (size L) q Q (foot M y))
  else 0

/-- Definition 2.8: linkage through same-size multipartitions, in either direction. -/
def JantzenEquivalent {r : ℕ} (q : F) (Q : Fin r → F)
    (L M : Multipartition r) : Prop :=
  ∃ h : size M = size L,
    Relation.ReflTransGen
      (fun A B : {N : Multipartition r // size N = size L} =>
        jantzenCoefficient q Q A.val B.val ≠ 0 ∨
          jantzenCoefficient q Q B.val A.val ≠ 0)
      ⟨L, rfl⟩ ⟨M, h⟩

/-- Field-valued residues, for q≠1 and nonzero Q, from PDF p. 7. -/
def fieldResidue {r : ℕ} (q : F) (Q : Fin r → F) (x : Node r) : F :=
  q ^ ((x.col : ℤ) - x.row) * Q x.comp

/-- Equality of residue multisets, retaining repeated residues. -/
def FieldResidueEquivalent {r : ℕ} (q : F) (Q : Fin r → F)
    (L M : Multipartition r) : Prop :=
  ∀ f : F, ((nodeDiagram L).filter fun x => fieldResidue q Q x = f).card =
    ((nodeDiagram M).filter fun x => fieldResidue q Q x = f).card

/-- Least k≥2 for which the geometric sum vanishes, or 0 for infinity. -/
def quantumCharacteristic (q : F) : ℕ :=
  if h : ∃ k : ℕ, 2 ≤ k ∧ (∑ i ∈ Finset.range k, q ^ i) = 0 then Nat.find h else 0

/-- Charged residues of section 3; ZMod 0 is the integer-content case. -/
def chargedResidue {r : ℕ} (e : ℕ) (c : Fin r → ℤ) (x : Node r) : ZMod e :=
  ((x.col : ℤ) - x.row + c x.comp : ℤ)

/-- Charged residue equivalence, counting nodes rather than distinct values. -/
def ChargedResidueEquivalent {r : ℕ} (e : ℕ) (c : Fin r → ℤ)
    (L M : Multipartition r) : Prop :=
  ∀ f : ZMod e, ((nodeDiagram L).filter fun x => chargedResidue e c x = f).card =
    ((nodeDiagram M).filter fun x => chargedResidue e c x = f).card

/-- ν'_p(h)=p^{v_p(h)}, or 1 in characteristic zero (PDF p. 11).
Only nonzero h is used in the statements. -/
def primePowerMultiplicity (p : ℕ) (h : ℤ) : ℕ :=
  if p = 0 then 1 else p ^ padicValNat p h.natAbs

example (h : ℤ) : primePowerMultiplicity 0 h = 1 := rfl

example {r : ℕ} (q : F) (Q : Fin r → F) (L : Multipartition r) :
    jantzenCoefficient q Q L L = 0 := by
  simp [jantzenCoefficient, strictlyDominates]

/-- Intercomponent pattern of 3.6(a); common remainders and distinct components
force both components to change, as required by the printed hypothesis. -/
def IntercomponentPattern {r : ℕ} (q : F) (Q : Fin r → F)
    (L M : Multipartition r) (x y : Node r) : Prop :=
  x ∈ nodeDiagram L ∧ y ∈ nodeDiagram M ∧ x.comp < y.comp ∧
  SameHookRemainder L M x y ∧ fieldResidue q Q (foot L x) = fieldResidue q Q (foot M y)

/-- Pattern in 3.6(b) and 4.2: z=(i,m,a), m<j, e divides h_z, and the
hook wrapped onto the common remainder has its hand in column m. -/
def SingleComponentPattern {r : ℕ} (e : ℕ) (L M : Multipartition r)
    (x z y : Node r) : Prop :=
  0 < e ∧ x ∈ nodeDiagram L ∧ z ∈ nodeDiagram L ∧ y ∈ nodeDiagram M ∧
  z.comp = x.comp ∧ y.comp = x.comp ∧ z.row = x.row ∧ z.col < x.col ∧
  (∀ a, a ≠ x.comp → L a = M a) ∧ e ∣ rimHookSize L z ∧
  SameHookRemainder L M x y ∧ rimHookSize L x = rimHookSize M y ∧ handColumn M y = z.col

/-- Both signed branches; the difference can vanish. -/
def singleComponentFormula {r : ℕ} (p e : ℕ) (L M : Multipartition r)
    (x z y : Node r) : ℤ :=
  (-1 : ℤ) ^ (legLength L x + legLength M y) *
    ((primePowerMultiplicity p (rimHookSize L z) : ℤ) -
      if e ∣ rimHookSize L x then (primePowerMultiplicity p (rimHookSize L x) : ℤ) else 0)

/-- One ordinary e-rim-hook removal. Infinity (e=0) permits no removals. -/
def CoreRemoval (e : ℕ) (L M : YoungDiagram) : Prop :=
  0 < e ∧ ∃ i j : ℕ, (i, j) ∈ partDiagram L ∧
    let H := (partDiagram L).filter fun z => i ≤ z.1 ∧ j ≤ z.2 ∧
      (z.1 + 1, z.2 + 1) ∉ partDiagram L
    H.card = e ∧ partDiagram M = partDiagram L \ H

/-- Compute the e-core by minimizing size among successive e-hook removals.
This is the terminal packed abacus of PDF p. 11; order independence is the
ordinary partition-core property, not an extra theorem hypothesis. -/
def partitionCore (e : ℕ) (L : YoungDiagram) : YoungDiagram :=
  if e = 0 then L else
    Function.argminOn partSize {M | Relation.ReflTransGen (CoreRemoval e) L M}
      ⟨L, Relation.ReflTransGen.refl⟩

/-- Componentwise e-core (Definition 3.8, PDF p. 14). -/
def multicore {r : ℕ} (e : ℕ) (L : Multipartition r) : Multipartition r :=
  fun a => partitionCore e (L a)

/-- Number of removed e-hooks; infinite quantum characteristic gives zero. -/
def coreWeight {r : ℕ} (e : ℕ) (L : Multipartition r) : ℕ :=
  if e = 0 then 0 else (size L - size (multicore e L)) / e

/-- The attained maximum over the nonempty same-size residue class.
All possible weights are in [0,|λ|], so a finite filter suffices. -/
def maximumCoreWeight {r : ℕ} (e : ℕ) (c : Fin r → ℤ)
    (L : Multipartition r) : ℕ :=
  ((Finset.range (size L + 1)).filter fun w => ∃ M : Multipartition r,
    size M = size L ∧ ChargedResidueEquivalent e c M L ∧ coreWeight e M = w).sup id

/-- Definition 3.15 through condition 3.14(a), in the class of the same total size. -/
def ReducedMulticore {r : ℕ} (e : ℕ) (c : Fin r → ℤ)
    (L : Multipartition r) : Prop :=
  ∀ M : Multipartition r, size M = size L → ChargedResidueEquivalent e c M L →
    multicore e M = M

/-- Charged beta numbers. Zero-based row i corresponds to source row i+1. -/
def betaSet (c : ℤ) (L : YoungDiagram) : Set ℤ :=
  {z | ∃ i : ℕ, z = (row L i : ℤ) - (i + 1 : ℕ) + c}

/-- A legal transfer on packed abacuses: remove the lowest bead on runner i
and place it at the first gap on runner j. For e=0 each runner has one
integer position, so the same conditions are precisely the occupancy guards. -/
def RunnerTransfer (e : ℕ) (c : ℤ) (i j : ZMod e) (L M : YoungDiagram) : Prop :=
  ∃ u v : ℤ, (u : ZMod e) = i ∧ (v : ZMod e) = j ∧ u ∈ betaSet c L ∧
    v ∉ betaSet c L ∧
    (∀ z ∈ betaSet c L, (z : ZMod e) = i → z ≤ u) ∧
    (∀ z : ℤ, z ∉ betaSet c L → (z : ZMod e) = j → v ≤ z) ∧
    betaSet c M = insert v (betaSet c L \ {u})

/-- Definition 3.10(a) as a legal relation. Both opposite transfers must
exist and produce packed abacuses; unchanged components are fixed. There is
no assigned output for an illegal or inconsistent swap. -/
def CoreSwap {r : ℕ} (e : ℕ) (c : Fin r → ℤ)
    (L M : Multipartition r) (a b : Fin r) (i j : ZMod e) : Prop :=
  multicore e L = L ∧ multicore e M = M ∧
  (∀ d, d ≠ a → d ≠ b → L d = M d) ∧
  RunnerTransfer e (c a) i j (L a) (M a) ∧
  RunnerTransfer e (c b) j i (L b) (M b)

example (L : YoungDiagram) : partitionCore 0 L = L := by simp [partitionCore]

example {r : ℕ} (L : Multipartition r) : coreWeight 0 L = 0 := rfl

/-- Coordinate vector spaces are finite dimensional. -/
abbrev Vector (F : Type) (d : ℕ) := Fin d → F

/-- Finite-dimensional right modules for the extended affine Hecke algebra in
m+1 Laurent variables (PDF pp. 1,8--9). T_i has the literal quadratic
(T_i+q)(T_i-1)=0 from p. 3. Changing standard Bernstein generators by
G_i=-T_i leaves T_i X_i T_i=q X_(i+1) unchanged. No Murphy recursion,
Specht family or Schur normalization enters this definition. -/
structure AffineModule (F : Type) [Field F] (m : ℕ) (q : F) where
  dim : ℕ
  T : Fin m → Matrix (Fin dim) (Fin dim) F
  X : Fin (m + 1) → (Matrix (Fin dim) (Fin dim) F)ˣ
  quadratic : ∀ i, (T i + q • 1) * (T i - 1) = 0
  braid : ∀ i j, j.val = i.val + 1 → T i * T j * T i = T j * T i * T j
  distant : ∀ i j, i.val + 1 < j.val → T i * T j = T j * T i
  laurent : ∀ i j, (X i : Matrix (Fin dim) (Fin dim) F) * (X j : Matrix (Fin dim) (Fin dim) F) =
    (X j : Matrix (Fin dim) (Fin dim) F) * (X i : Matrix (Fin dim) (Fin dim) F)
  mixed : ∀ i, T i * (X i.castSucc : Matrix (Fin dim) (Fin dim) F) * T i = q • (X i.succ : Matrix (Fin dim) (Fin dim) F)
  other : ∀ i j, j ≠ i.castSucc → j ≠ i.succ →
    T i * (X j : Matrix (Fin dim) (Fin dim) F) = (X j : Matrix (Fin dim) (Fin dim) F) * T i

/-- A morphism commutes with all right actions v ↦ vT_i and v ↦ vX_i. -/
def AffineMorphism {m : ℕ} {q : F} (D E : AffineModule F m q)
    (f : Vector F D.dim →ₗ[F] Vector F E.dim) : Prop :=
  (∀ i v, f (Matrix.vecMul v (D.T i)) = Matrix.vecMul (f v) (E.T i)) ∧
  (∀ i v, f (Matrix.vecMul v (D.X i : Matrix (Fin D.dim) (Fin D.dim) F)) =
    Matrix.vecMul (f v) (E.X i : Matrix (Fin E.dim) (Fin E.dim) F))

/-- Nonzero simple right modules, expressed through invariant linear subspaces.
In finite dimensions invariance under invertible X_i also gives invariance
under X_i inverse. -/
def Simple {m : ℕ} {q : F} (D : AffineModule F m q) : Prop :=
  0 < D.dim ∧ ∀ S : Submodule F (Vector F D.dim),
    (∀ i v, v ∈ S → Matrix.vecMul v (D.T i) ∈ S) →
    (∀ i v, v ∈ S → Matrix.vecMul v (D.X i : Matrix (Fin D.dim) (Fin D.dim) F) ∈ S) →
    S = ⊥ ∨ S = ⊤

/-- Isomorphism makes linkage independent of coordinate choices. -/
def ModuleIso {m : ℕ} {q : F} (D E : AffineModule F m q) : Prop :=
  ∃ f : Vector F D.dim ≃ₗ[F] Vector F E.dim, AffineMorphism D E f.toLinearMap

/-- Factoring through the actual cyclotomic quotient is exactly annihilation
by the cyclotomic polynomial (PDF p. 1). Parameter repetitions are retained. -/
def FactorsCyclotomic {m r : ℕ} {q : F} (Q : Fin r → F) (D : AffineModule F m q) : Prop :=
  (List.ofFn fun a => (D.X 0 : Matrix (Fin D.dim) (Fin D.dim) F) - Q a • 1).prod = 0

/-- Nonsplit 0→D→E→D'→0. P restricts E only when extensions are taken in a
cyclotomic quotient category. A splitting must be a module morphism. -/
def NonsplitExtension {m : ℕ} {q : F} (P : AffineModule F m q → Prop)
    (D Dprime : AffineModule F m q) : Prop :=
  ∃ E : AffineModule F m q, P E ∧
    ∃ f : Vector F D.dim →ₗ[F] Vector F E.dim,
    ∃ g : Vector F E.dim →ₗ[F] Vector F Dprime.dim,
      AffineMorphism D E f ∧ AffineMorphism E Dprime g ∧ Function.Injective f ∧
      Function.Surjective g ∧ LinearMap.range f = LinearMap.ker g ∧
      ¬∃ s : Vector F Dprime.dim →ₗ[F] Vector F E.dim,
        AffineMorphism Dprime E s ∧ g.comp s = LinearMap.id

/-- Block linkage on isomorphism classes of simple finite-dimensional modules.
P restricts vertices, R restricts middle terms. Iso edges identify different
coordinate representatives of the same simple module (PDF pp. 1,4). -/
def Linkage {m : ℕ} {q : F} (P R : AffineModule F m q → Prop)
    (D Dprime : AffineModule F m q) : Prop :=
  Simple D ∧ P D ∧ Simple Dprime ∧ P Dprime ∧
  Relation.ReflTransGen
    (fun A B => Simple A ∧ P A ∧ Simple B ∧ P B ∧
      (ModuleIso A B ∨ NonsplitExtension R A B ∨ NonsplitExtension R B A)) D Dprime

/-- Laurent polynomials are finite coefficient families of integer exponents. -/
abbrev LaurentPolynomial (F : Type) [Zero F] (m : ℕ) := (Fin (m + 1) → ℤ) →₀ F

/-- Symmetric Laurent polynomials, with no orbit-sum multiplicity factors that
would fail in positive characteristic. -/
def SymmetricLaurent {m : ℕ} (f : LaurentPolynomial F m) : Prop :=
  ∀ s : Equiv.Perm (Fin (m + 1)), ∀ z : Fin (m + 1) → ℤ, f (fun i => z (s i)) = f z

/-- Evaluation at commuting invertible X_i, using an ordered product because
the surrounding matrix algebra itself is not commutative. -/
def evaluateLaurent {m : ℕ} {q : F} (D : AffineModule F m q)
    (f : LaurentPolynomial F m) : Matrix (Fin D.dim) (Fin D.dim) F :=
  f.sum fun z a => a •
    (((List.ofFn fun i => (D.X i) ^ z i).prod : (Matrix (Fin D.dim) (Fin D.dim) F)ˣ) : Matrix (Fin D.dim) (Fin D.dim) F)

/-- Equal central characters via the actual symmetric Laurent centre
identified on PDF pp. 2,8. Scalar action is part of this conclusion. -/
def SameCentralCharacter {m : ℕ} {q : F} (D E : AffineModule F m q) : Prop :=
  ∀ f : LaurentPolynomial F m, SymmetricLaurent f → ∃ a : F,
    evaluateLaurent D f = a • 1 ∧ evaluateLaurent E f = a • 1

example {m : ℕ} {q : F} (D : AffineModule F m q) :
    evaluateLaurent D 0 = 0 := by simp [evaluateLaurent]

example {m : ℕ} {q : F} (D : AffineModule F m q) : ModuleIso D D := by
  refine ⟨LinearEquiv.refl F _, ?_⟩
  constructor <;> intro i v <;> rfl

example {m : ℕ} {q : F} (D : AffineModule F m q) (h : D.dim = 0) : ¬Simple D := by
  intro hs
  have hp := hs.1
  omega

end

end QAlgorithms.Papers.Independent.Intake100.P29


