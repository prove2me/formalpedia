-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62
-- name    : QAlgorithms_Papers_Independent_Information100_P62
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T21:29:30.545146+00:00
-- url     : https://prove2.me/theorems/5e296929-0605-429f-83b2-a28770ed91cb
-- title:
--   Definitions for Transmitting algebras through quantum channels
-- statement:
--   The objects the formalized statements of *Transmitting algebras through quantum channels* (arXiv:2609.40054) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Shape`
--   - `Valid`: PDF p.11, (2.3): nonzero finite-dimensional algebra types.
--   - `Block`
--   - `blockSize`
--   - `Algebra`
--   - `Logical`
--   - `Faithful`: PDF p.11: no preservation-of-one requirement.
--   - `Embeds`: PDF p.11, Definition 2.1: actual faithful complex-linear star-homomorphism.
--   - `Packs`: PDF p.12, (2.8).
--   - `MultiplicityPacking`: PDF pp.11–12, (2.7), including positive occurrence of every source block.
--   - `lengthDim`: PDF p.36, (4.22): faithful dimension, not the vector-space dimension of A.
--   - `equalBlocks`
--   - `quantum`
--   - `classical`
--   - `graph`: PDF p.13, Definition 2.3: span over all normalized Kraus presentations. On channels all such presentations have exactly the same span.
--   - `IsSystem`
--   - `GraphHom`: PDF p.15, Definition 2.9: arbitrary finite ancilla and contravariant compression.
--   - `GraphIso`
--   - `IsProjection`
--   - `projection`: Orthogonal projection computed from the subspace.
--   - `imageSpace`
--   - `kernelSpace`
--   - `support`
--   - `Code`: PDF pp.14,23: scalar compression is equality with CP because I belongs to S.
--   - `Correctable`: PDF p.19, Theorem 2.16: exact correctability of a corner algebra with unit P.
--   - `Transmits`: PDF p.21, Definition 3.1: arbitrary faithful encoding representations; no restriction to multiplicity one or to a fixed support.
--   - `transmission`
--   - `Maximal`: PDF p.29, (4.1).
--   - `Dominating`: PDF p.29, (4.2), including transmittability of the dominating type.
--   - `HasDominating`
--   - `maximals`
--   - `pinching`: PDF p.21, (3.2): defined on every operator, not only block-diagonal inputs.
--   - `pinchingSystem`: PDF p.25: span of the scalar block identities.
--   - `alpha`: PDF p.14, (2.12). On finite-dimensional operator systems the feasible set is bounded.
--   - `alphaQ`
--   - `alphaEA`: PDF p.14, (2.13): arbitrary finite shared ancillas, normalized positive density, isometric encodings, and Hilbert–Schmidt orthogonality.
--   - `logTwo`
--   - `classicalCapacity`: PDF p.14, (2.17)–(2.19): capacities in their equivalent graph formulations.
--   - `quantumCapacity`
--   - `assistedCapacity`
--   - `dmax`: PDF p.32, (4.6); the input-dimension cutoff loses no faithful representation.
--   - `hybrid`: PDF p.32, (4.7), with value zero for unattainable positive dimensions.
--   - `packingNumber`: PDF p.33, (4.10): zero is included even when no d-block embeds.
--   - `reconstruction`: PDF p.34, (4.13): t steps visit D,D-1,...,D-t+1. Subtraction is in integers.
--   - `multiplicity`
--   - `capacityAlgebra`: PDF p.34, (4.14): none precisely when a reconstructed multiplicity is negative.
--   - `forbidden`: PDF p.36, Definition 4.9: minimal nonembedding types among nonzero algebras.
--   - `IsAlgebra`: PDF p.39: ambient-unital star-subalgebra; commutativity alone does not suffice.
--   - `commutant`
--   - `HasType`: Exact type of a concrete algebra; range equality includes surjectivity onto S.
--   - `IsCornerAlgebra`: PDF p.19: possibly nonunital star-subalgebra with its own nonzero unit P.
--   - `RepresentationOn`: A representation extended linearly off A; no conditions are imposed off A.
--   - `tensorShape`: PDF p.44: tensor product types, with multiplicities.
--   - `powerShape`
--   - `tensorChannel`: Full matrix-unit tensor expansion, permitting unrestricted entangled inputs.
--   - `starLower`: PDF p.44, (5.2): includes the downward closure of product types.
--   - `tensorPower`
--   - `width`: PDF p.45, (5.6); finiteness follows from the faithful dimension bound.
--   - `generatedProduct`
--   - `Indecomposable`
--   - `partitionCount`
--   - `classicalChannel`: PDF p.13, (2.11).
--   - `Stochastic`
--   - `independence`
--   - `unit`: Matrix units use the source's zero-based basis labels.
--   - `example42Kraus`: PDF p.29, Example 4.2.
--   - `example42`
--   - `example43Kraus`: PDF p.30, Example 4.3, and p.47, (5.11).
--   - `example43`
--   - `negativeExample`: PDF p.34, footnote 4.
--   - `capacityExample`: PDF p.35, Remark 4.8.
--   - `appendixExample`: PDF p.60, (6.13).
--   - `compositionExample`: PDF p.62, (6.29).
--   - `cycleMatrix`: PDF p.43, (4.38).
--   - `cycleChannel`
--   - `dephasing`
--   - `selectorChannel`
--   - `charge`: PDF p.48, (5.14): the first q sorted Hamming weights, with multiplicities.
--   - `widthType`
--   - `selectorType`
--   - `faceVertices`: PDF p.49: 0 and 2 denote singleton coordinates; 1 denotes a free coordinate. This represents exactly the distinct nonempty faces, without repetitions.
--   - `cubeKraus`: PDF p.49, (5.22).
--   - `cubeEffect`
--   - `cubePi`: PDF p.50, (5.27).
--   - `cubeOutput`: PDF p.50, (5.29): zero compression coefficients are excluded before inversion.
--   - `partialCross`: PDF p.61, (6.23): partial trace of a cross operator over the first factor.
--   - `selectedSpan`: PDF p.25: span of complete output ranges for the selected block labels. An empty family has span bottom.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, https://arxiv.org/abs/2609.40054v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel

/-! Salzmann–Singh, arXiv:2609.40054v1. Local definitions for this paper only.
Algebra types are multisets: equality means abstract star-isomorphism. Correctability
uses the equivalent Knill–Laflamme criterion of Theorem 2.16, p.19.
Compilation is pending the batch mechanical check. -/

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder
open Finset

attribute [local instance] Classical.propDecidable

abbrev Shape := Multiset ℕ

/-- PDF p.11, (2.3): nonzero finite-dimensional algebra types. -/
def Valid (A : Shape) : Prop := A ≠ 0 ∧ ∀ d ∈ A, 0 < d

abbrev Block (A : Shape) := Fin A.toList.length

def blockSize (A : Shape) (k : Block A) : ℕ := A.toList.get k

abbrev Algebra (A : Shape) := (k : Block A) → Matrix (Fin (blockSize A k)) (Fin (blockSize A k)) ℂ

abbrev Logical (A : Shape) := Σ k : Block A, Fin (blockSize A k)

/-- PDF p.11: no preservation-of-one requirement. -/
def Faithful {A B : Type} [AddCommMonoid A] [AddCommMonoid B]
    [Module ℂ A] [Module ℂ B] [Mul A] [Mul B] [Star A] [Star B]
    (f : A →ₗ[ℂ] B) : Prop :=
  Function.Injective f ∧ (∀ x y, f (x * y) = f x * f y) ∧ ∀ x, f (star x) = star (f x)

/-- PDF p.11, Definition 2.1: actual faithful complex-linear star-homomorphism. -/
def Embeds (A B : Shape) : Prop := ∃ f : Algebra A →ₗ[ℂ] Algebra B, Faithful f

/-- PDF p.12, (2.8). -/
def Packs (A B : Shape) : Prop :=
  ∃ f : Block A → Block B, ∀ j, ∑ k ∈ univ.filter (fun k => f k = j), blockSize A k ≤ blockSize B j

/-- PDF pp.11–12, (2.7), including positive occurrence of every source block. -/
def MultiplicityPacking (A B : Shape) : Prop :=
  ∃ L : Block A → Block B → ℕ,
    (∀ j, ∑ k, L k j * blockSize A k ≤ blockSize B j) ∧ ∀ k, 1 ≤ ∑ j, L k j

/-- PDF p.36, (4.22): faithful dimension, not the vector-space dimension of A. -/
def lengthDim (A : Shape) : ℕ := A.sum

def equalBlocks (d c : ℕ) : Shape := Multiset.replicate c d

def quantum (d : ℕ) : Shape := {d}

def classical (c : ℕ) : Shape := equalBlocks 1 c

example : equalBlocks 2 0 = 0 := rfl

example : lengthDim (quantum 2) = 2 := rfl

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]
variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- PDF p.13, Definition 2.3: span over all normalized Kraus presentations.
On channels all such presentations have exactly the same span. -/
def graph (F : Superop I O) : Submodule ℂ (Matrix I I ℂ) :=
  Submodule.span ℂ {X | ∃ (r : ℕ) (E : Fin r → Matrix O I ℂ),
    IsKrausFamily E ∧ (∀ R, F R = krausApply E R) ∧ ∃ i j, X = (E i)ᴴ * E j}

def IsSystem (S : Submodule ℂ (Matrix I I ℂ)) : Prop :=
  (1 : Matrix I I ℂ) ∈ S ∧ ∀ X ∈ S, Xᴴ ∈ S

/-- PDF p.15, Definition 2.9: arbitrary finite ancilla and contravariant compression. -/
def GraphHom (S : Submodule ℂ (Matrix I I ℂ)) (T : Submodule ℂ (Matrix J J ℂ)) : Prop :=
  ∃ e : ℕ, 0 < e ∧ ∃ V : Matrix (J × Fin e) I ℂ,
    Vᴴ * V = 1 ∧ ∀ X ∈ T, ∀ Y : Matrix (Fin e) (Fin e) ℂ,
      Vᴴ * Matrix.kronecker X Y * V ∈ S

def GraphIso (S : Submodule ℂ (Matrix I I ℂ)) (T : Submodule ℂ (Matrix J J ℂ)) : Prop :=
  GraphHom S T ∧ GraphHom T S

def IsProjection (P : Matrix I I ℂ) : Prop := Pᴴ = P ∧ P * P = P

/-- Orthogonal projection computed from the subspace. -/
def projection (C : Submodule ℂ (EuclideanSpace ℂ I)) : Matrix I I ℂ :=
  fun i j => (C.starProjection (ket j)) i

def imageSpace (E : Matrix O I ℂ) : Submodule ℂ (EuclideanSpace ℂ O) :=
  LinearMap.range (Matrix.toEuclideanLin E)

def kernelSpace (E : Matrix O I ℂ) : Submodule ℂ (EuclideanSpace ℂ I) :=
  LinearMap.ker (Matrix.toEuclideanLin E)

def support (X : Matrix I I ℂ) : Matrix I I ℂ := projection (imageSpace X)

/-- PDF pp.14,23: scalar compression is equality with CP because I belongs to S. -/
def Code (S : Submodule ℂ (Matrix I I ℂ)) (P : Matrix I I ℂ) : Prop :=
  IsProjection P ∧ ∀ X ∈ S, ∃ z : ℂ, P * X * P = z • P

/-- PDF p.19, Theorem 2.16: exact correctability of a corner algebra with unit P. -/
def Correctable (F : Superop I O) (A : Submodule ℂ (Matrix I I ℂ)) (P : Matrix I I ℂ) : Prop :=
  ∀ X ∈ A, ∀ s ∈ graph F, X * (P * s * P) = (P * s * P) * X

/-- PDF p.21, Definition 3.1: arbitrary faithful encoding representations;
no restriction to multiplicity one or to a fixed support. -/
def Transmits (F : Superop I O) (A : Shape) : Prop :=
  Valid A ∧ ∃ f : Algebra A →ₗ[ℂ] Matrix I I ℂ, Faithful f ∧
    ∀ X, ∀ s ∈ graph F, f X * (f 1 * s * f 1) = (f 1 * s * f 1) * f X

def transmission (F : Superop I O) : Set Shape := {A | Transmits F A}

/-- PDF p.29, (4.1). -/
def Maximal (F : Superop I O) (A : Shape) : Prop :=
  Transmits F A ∧ ∀ B, Transmits F B → Embeds A B → A = B

/-- PDF p.29, (4.2), including transmittability of the dominating type. -/
def Dominating (F : Superop I O) (A : Shape) : Prop :=
  Transmits F A ∧ ∀ B, Transmits F B → Embeds B A

def HasDominating (F : Superop I O) : Prop := ∃ A, Dominating F A

def maximals (F : Superop I O) : Set Shape := {A | Maximal F A}

/-- PDF p.21, (3.2): defined on every operator, not only block-diagonal inputs. -/
def pinching (A : Shape) : Superop (Logical A) (Logical A) :=
  fun X i j => if i.1 = j.1 then X i j else 0

/-- PDF p.25: span of the scalar block identities. -/
def pinchingSystem (A : Shape) : Submodule ℂ (Matrix (Logical A) (Logical A) ℂ) :=
  Submodule.span ℂ {X | ∃ z : Block A → ℂ, X = fun i j => if i = j then z i.1 else 0}

example (A : Shape) (X : Matrix (Logical A) (Logical A) ℂ) (i : Logical A) :
    pinching A X i i = X i i := by simp [pinching]

/-- PDF p.14, (2.12). On finite-dimensional operator systems the feasible set is bounded. -/
def alpha (S : Submodule ℂ (Matrix I I ℂ)) : ℕ :=
  sSup {m | ∃ v : Fin m → EuclideanSpace ℂ I,
    (∀ i, IsState (v i)) ∧ ∀ i j, i ≠ j → ∀ X ∈ S, inner ℂ (v i) (act X (v j)) = 0}

def alphaQ (S : Submodule ℂ (Matrix I I ℂ)) : ℕ :=
  sSup {d | ∃ P : Matrix I I ℂ, Code S P ∧ P.rank = d}

/-- PDF p.14, (2.13): arbitrary finite shared ancillas, normalized positive density,
isometric encodings, and Hilbert–Schmidt orthogonality. -/
def alphaEA (S : Submodule ℂ (Matrix I I ℂ)) : ℕ :=
  sSup {m | ∃ a r : ℕ, 0 < a ∧ 0 < r ∧
    ∃ rho : Matrix (Fin a) (Fin a) ℂ, rho.PosSemidef ∧ Matrix.trace rho = 1 ∧
    ∃ V : Fin m → Matrix (I × Fin r) (Fin a) ℂ,
      (∀ j, (V j)ᴴ * V j = 1) ∧ ∀ j k, j ≠ k → ∀ X ∈ S,
        ∀ Y : Matrix (Fin r) (Fin r) ℂ,
          Matrix.trace ((V j * rho * (V k)ᴴ)ᴴ * Matrix.kronecker X Y) = 0}

def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- PDF p.14, (2.17)–(2.19): capacities in their equivalent graph formulations. -/
def classicalCapacity (F : Superop I O) : ℝ := logTwo (alpha (graph F))

def quantumCapacity (F : Superop I O) : ℝ := logTwo (alphaQ (graph F))

def assistedCapacity (F : Superop I O) : ℝ := logTwo (alphaEA (graph F))

/-- PDF p.32, (4.6); the input-dimension cutoff loses no faithful representation. -/
def dmax (F : Superop I O) : ℕ :=
  (univ.filter (fun d : Fin (Fintype.card I + 1) => Transmits F (quantum d.val))).sup Fin.val

/-- PDF p.32, (4.7), with value zero for unattainable positive dimensions. -/
def hybrid (F : Superop I O) (d : ℕ) : ℕ :=
  if d = 0 then 0 else
    (univ.filter (fun c : Fin (Fintype.card I + 1) => Transmits F (equalBlocks d c.val))).sup Fin.val

/-- PDF p.33, (4.10): zero is included even when no d-block embeds. -/
def packingNumber (d : ℕ) (A : Shape) : ℕ :=
  if d = 0 then 0 else
    (univ.filter (fun c : Fin (lengthDim A + 1) => Embeds (equalBlocks d c.val) A)).sup Fin.val

/-- PDF p.34, (4.13): t steps visit D,D-1,...,D-t+1. Subtraction is in integers. -/
def reconstruction (c : ℕ → ℕ) (D : ℕ) : ℕ → (ℕ → ℤ)
  | 0 => fun _ => 0
  | t + 1 =>
    let prev := reconstruction c D t
    let d := D - t
    fun k => if k = d then (c d : ℤ) - ∑ m ∈ Icc (d + 1) D, prev m * (m / d : ℕ)
      else prev k

def multiplicity (F : Superop I O) (d : ℕ) : ℤ := reconstruction (hybrid F) (dmax F) (dmax F) d

/-- PDF p.34, (4.14): none precisely when a reconstructed multiplicity is negative. -/
def capacityAlgebra (F : Superop I O) : Option Shape :=
  if ∀ d ∈ Icc 1 (dmax F), 0 ≤ multiplicity F d then
    some (↑((List.range (dmax F)).flatMap (fun t => List.replicate (multiplicity F (t + 1)).toNat (t + 1))) : Shape)
  else none

example (c : ℕ → ℕ) (D d : ℕ) : reconstruction c D 0 d = 0 := rfl

/-- PDF p.36, Definition 4.9: minimal nonembedding types among nonzero algebras. -/
def forbidden (A : Shape) : Set Shape :=
  {B | Valid B ∧ ¬ Embeds B A ∧ ∀ C, Valid C → Embeds C B → C ≠ B → Embeds C A}

/-- PDF p.39: ambient-unital star-subalgebra; commutativity alone does not suffice. -/
def IsAlgebra (S : Submodule ℂ (Matrix I I ℂ)) : Prop :=
  IsSystem S ∧ ∀ X ∈ S, ∀ Y ∈ S, X * Y ∈ S

def commutant (S : Submodule ℂ (Matrix I I ℂ)) : Submodule ℂ (Matrix I I ℂ) :=
  Submodule.span ℂ {X | ∀ Y ∈ S, X * Y = Y * X}

/-- Exact type of a concrete algebra; range equality includes surjectivity onto S. -/
def HasType (S : Submodule ℂ (Matrix I I ℂ)) (A : Shape) : Prop :=
  Valid A ∧ ∃ f : Algebra A →ₗ[ℂ] Matrix I I ℂ, Faithful f ∧ ∀ Y, Y ∈ S ↔ ∃ X, f X = Y

/-- PDF p.19: possibly nonunital star-subalgebra with its own nonzero unit P. -/
def IsCornerAlgebra (A : Submodule ℂ (Matrix I I ℂ)) (P : Matrix I I ℂ) : Prop :=
  P ∈ A ∧ P ≠ 0 ∧ IsProjection P ∧ (∀ X ∈ A, Xᴴ ∈ A) ∧
    (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ ∀ X ∈ A, P * X = X ∧ X * P = X

/-- A representation extended linearly off A; no conditions are imposed off A. -/
def RepresentationOn (A : Submodule ℂ (Matrix I I ℂ)) (f : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Prop :=
  Set.InjOn f A ∧ (∀ X ∈ A, ∀ Y ∈ A, f (X * Y) = f X * f Y) ∧ ∀ X ∈ A, f Xᴴ = (f X)ᴴ

/-- PDF p.44: tensor product types, with multiplicities. -/
def tensorShape (A B : Shape) : Shape := (A.toList.flatMap (fun a => B.toList.map (fun b => a * b)) : List ℕ)

def powerShape (A : Shape) : ℕ → Shape
  | 0 => quantum 1
  | n + 1 => tensorShape (powerShape A n) A

/-- Full matrix-unit tensor expansion, permitting unrestricted entangled inputs. -/
def tensorChannel (F : Superop I O) (G : Superop J K) : Superop (I × J) (O × K) :=
  fun X a b => ∑ i, ∑ j, ∑ k, ∑ l,
    X (i, k) (j, l) * F (Matrix.single i j 1) a.1 b.1 * G (Matrix.single k l 1) a.2 b.2

/-- PDF p.44, (5.2): includes the downward closure of product types. -/
def starLower (U V : Set Shape) : Set Shape :=
  {C | Valid C ∧ ∃ A ∈ U, ∃ B ∈ V, Embeds C (tensorShape A B)}

def tensorPower (F : Superop I O) (n : ℕ) := piSuperop (fun _ : Fin n => F)

/-- PDF p.45, (5.6); finiteness follows from the faithful dimension bound. -/
def width (F : Superop I O) (n : ℕ) : ℕ := (maximals (tensorPower F n)).ncard

def generatedProduct {R : ℕ} (G : Fin R → Shape) (a : Fin R → ℕ) : Shape :=
  (List.ofFn (fun j => powerShape (G j) (a j))).foldl tensorShape (quantum 1)

def Indecomposable (F : Superop I O) (n : ℕ) (A : Shape) : Prop :=
  2 ≤ n ∧ Maximal (tensorPower F n) A ∧
    ∀ m, 1 ≤ m → m < n → A ∉ starLower (transmission (tensorPower F m)) (transmission (tensorPower F (n - m)))

def partitionCount (r : ℕ) : ℕ := Nat.card (Nat.Partition r)

/-- PDF p.13, (2.11). -/
def classicalChannel (N : Matrix O I ℝ) : Superop I O :=
  fun X a b => if a = b then ∑ i, (N a i : ℂ) * X i i else 0

def Stochastic (N : Matrix O I ℝ) : Prop := (∀ a i, 0 ≤ N a i) ∧ ∀ i, ∑ a, N a i = 1

def independence (N : Matrix O I ℝ) : ℕ :=
  (univ.powerset.filter (fun s : Finset I => ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a, N a i * N a j = 0)).sup Finset.card

/-- Matrix units use the source's zero-based basis labels. -/
def unit {a b : ℕ} (i : Fin a) (j : Fin b) : Matrix (Fin a) (Fin b) ℂ := Matrix.single i j 1

/-- PDF p.29, Example 4.2. -/
def example42Kraus : Fin 3 → Matrix (Fin 3) (Fin 4) ℂ :=
  ![unit 0 0 + unit 1 1, (Real.sqrt 2 : ℂ)⁻¹ • (unit 1 2 + unit 2 2),
    (Real.sqrt 2 : ℂ)⁻¹ • (unit 1 3 - unit 2 3)]

def example42 := krausApply example42Kraus

/-- PDF p.30, Example 4.3, and p.47, (5.11). -/
def example43Kraus : Fin 2 → Matrix (Fin 4) (Fin 3) ℂ :=
  ![unit 0 0 + (Real.sqrt 2 : ℂ)⁻¹ • unit 1 1, (Real.sqrt 2 : ℂ)⁻¹ • unit 2 1 + unit 3 2]

def example43 := krausApply example43Kraus

/-- PDF p.34, footnote 4. -/
def negativeExample := krausApply (![unit 0 0 + unit 1 1 + unit 2 2,
  unit 0 3 + unit 1 4, unit 2 5 + unit 6 6] : Fin 3 → Matrix (Fin 7) (Fin 7) ℂ)

/-- PDF p.35, Remark 4.8. -/
def capacityExample := krausApply (![unit 0 0 + unit 1 1 + unit 2 2 + unit 3 3,
  unit 3 4 + unit 4 5] : Fin 2 → Matrix (Fin 6) (Fin 6) ℂ)

/-- PDF p.60, (6.13). -/
def appendixExample := krausApply (![unit 0 0 + unit 1 1,
  unit 1 2 + unit 3 3] : Fin 2 → Matrix (Fin 4) (Fin 4) ℂ)

/-- PDF p.62, (6.29). -/
def compositionExample := krausApply
  (![(Real.sqrt 2 : ℂ)⁻¹ • (unit 0 0 + unit 0 2 + unit 3 0 - unit 3 2) + unit 1 1,
    (Real.sqrt 2 : ℂ)⁻¹ • (unit 0 3 - unit 2 3)] : Fin 2 → Matrix (Fin 4) (Fin 4) ℂ)

/-- PDF p.43, (4.38). -/
def cycleMatrix : Matrix (Fin 5) (Fin 5) ℝ :=
  fun j i => if j = i ∨ j.val = (i.val + 1) % 5 then 1 / 2 else 0

def cycleChannel := classicalChannel cycleMatrix

def dephasing := krausApply (![unit 0 0, unit 1 1] : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)

def selectorChannel := tensorChannel dephasing example43

/-- PDF p.48, (5.14): the first q sorted Hamming weights, with multiplicities. -/
def charge (n q : ℕ) : ℕ :=
  ((((List.ofFn (fun x : Fin (2 ^ n) => hammingWeight (natToBits n x.val))).mergeSort (· ≤ ·)).take q).map (fun w => 2 ^ w)).sum

def widthType (n q : ℕ) : Shape := quantum q + classical (3 ^ n - charge n q)

def selectorType (n : ℕ) (N : Fin (2 ^ n) → ℕ) : Shape :=
  (List.ofFn (fun q => (List.replicate (N q) (widthType n (q.val + 1))).foldl (· + ·) 0)).foldl (· + ·) 0

/-- PDF p.49: 0 and 2 denote singleton coordinates; 1 denotes a free coordinate.
This represents exactly the distinct nonempty faces, without repetitions. -/
def faceVertices {n : ℕ} (F : Fin n → Fin 3) : Finset (Qubits n) :=
  univ.filter (fun y => ∀ i, (F i).val = 1 ∨ ((F i).val = 0 ∧ y i = false) ∨ ((F i).val = 2 ∧ y i = true))

/-- PDF p.49, (5.22). -/
def cubeKraus {n : ℕ} (y : Qubits n) : Matrix (Fin n → Fin 4) (Fin n → Fin 3) ℂ :=
  fun a b => ∏ i, example43Kraus (if y i then 1 else 0) (a i) (b i)

def cubeEffect {n : ℕ} (y : Qubits n) := (cubeKraus y)ᴴ * cubeKraus y

/-- PDF p.50, (5.27). -/
def cubePi (n : ℕ) : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℂ :=
  (∑ y : Qubits n, cubeKraus y) * (∑ y : Qubits n, cubeKraus y)ᴴ

/-- PDF p.50, (5.29): zero compression coefficients are excluded before inversion. -/
def cubeOutput {n : ℕ} (P : Matrix (Fin n → Fin 3) (Fin n → Fin 3) ℂ) (lam : Qubits n → ℝ) :=
  ∑ y ∈ univ.filter (fun y => 0 < lam y), ((lam y : ℂ)⁻¹) • (cubeKraus y * P * (cubeKraus y)ᴴ)

/-- PDF p.61, (6.23): partial trace of a cross operator over the first factor. -/
def partialCross {g : ℕ} (u v : EuclideanSpace ℂ (Fin 2 × Fin g)) : Matrix (Fin g) (Fin g) ℂ :=
  fun a b => ∑ i : Fin 2, u (i, a) * conj (v (i, b))

example : charge 0 1 = 1 := by
  simp [charge, List.ofFn_succ, hammingWeight]

example : partialCross (g := 1) 0 0 = 0 := by ext; simp [partialCross]

/-- PDF p.25: span of complete output ranges for the selected block labels.
An empty family has span bottom. -/
def selectedSpan {r : ℕ} (E : Fin r → Matrix O I ℂ) {A : Shape}
    (f : Block A → Fin r) (U : Finset (Block A)) : Submodule ℂ (EuclideanSpace ℂ O) :=
  ⨆ k : {k : Block A // k ∈ U}, imageSpace (E (f k.val))

end

end QAlgorithms.Papers.Independent.Information100.P62


