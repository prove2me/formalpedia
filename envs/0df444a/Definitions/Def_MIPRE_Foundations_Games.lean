-- Prove2me | Definitions.Def_MIPRE_Foundations_Games
-- name    : MIPRE_Foundations_Games
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:06:04.474093+00:00
-- url     : https://prove2.me/theorems/2894f932-d6e1-464e-8158-fbe5710be380
-- title:
--   Nonlocal games, strategies and values: tensor-product, synchronous and commuting strategies
-- statement:
--   **Games** (blueprint §2.1). `MIPRE.Game X Y A B` ($X, Y, A, B$ finite): a distribution `μ : X → Y → ℝ` (`μ_nonneg`, `μ_sum_one`) and a predicate `D : X → Y → A → B → Bool`. `MIPRE.SynchronousGame X A`: the same with $Y = X$, $B = A$ and `synchronous`, $D(x,x,a,b) = \mathrm{false}$ for $a \ne b$; `SynchronousGame.toGame` forgets it.
--
--   **Skeleton.** `MIPRE.ProjectiveMeasurement X A 𝒜` (star ring $\mathcal A$): `M : X → A → 𝒜` with `selfAdjoint`, `projective` and `normalized` ($\sum_a M^a_x = 1$); `ProjectiveMeasurement.map φ P` transports along a star-algebra equivalence. `MIPRE.TracialState 𝒜`: a linear functional $\tau$ (coercion `instFunLikeComplex`) with $0 \le \tau(m^{*}m)$, $\tau(1) = 1$, $\tau(mn) = \tau(nm)$; `TracialState.comp τ φ` pulls back along one; `MIPRE.normalizedTrace n` is $\mathrm{Tr}(\cdot)/|n|$. `MIPRE.tracialValue G τ P`:
--   $$\sum_{x,y}\sum_{a,b} \mu(x,y)\,[D(x,y,a,b)]\ \mathrm{Re}\,\tau\bigl(M^a_x M^b_y\bigr).$$
--   `MIPRE.POVM X d`: self-adjoint `mats`, `nonneg` (Loewner order), `normalized`.
--
--   **Strategies and values.** `MIPRE.TensorProductStrategy G`: `dA`, `dB`, a unit state `ψ` on `Fin dA × Fin dB` (`ψ_unit`), projective measurements `PA`, `PB`; its `value` is $\sum \mu[D]\,\mathrm{Re}\langle\psi,(A^a_x \otimes B^b_y)\psi\rangle$, `MIPRE.quantumValue G` its supremum. `MIPRE.SyncStrategy G`: `d` with `d_pos`, `P` on $d \times d$ matrices; its `value` is `tracialValue` against the normalized trace, `MIPRE.syncValue G` the supremum; `SyncStrategy.IsPCC`: $M^a_xM^b_y = M^b_yM^a_x$ whenever $\mu(x,y) > 0$; `SyncStrategy.povm` gives `P` as POVMs. `MIPRE.CommutingStrategy G`: a `CStarAlgebra` `alg : Type`, a tracial state `τ`, a projective measurement `P` in `alg`; `value` $=$ `tracialValue G τ P`. `SyncStrategy.toCommutingStrategy` uses `alg = CStarMatrix (Fin d) (Fin d) ℂ`; `SyncStrategy.toTensorProductStrategy` plays $A^a_x = M^a_x$, $B^b_y = (M^b_y)^{\mathsf T}$ on `MIPRE.maxEntangled d` $= d^{-1/2}\sum_i |i\rangle|i\rangle$.
--
--   The embedded lemmas are coercion and `simp` rules, $0 \le \mathrm{value} \le 1$ for tensor-product strategies, the explicit form `SyncStrategy.value_eq`, and the value preservation of both conversions.
--
--   **Formalization Note**. Distributions are real functions with nonnegativity and normalization fields, not `PMF`; values take `.re` (no proof obligations); strategies are projective, following JNVWY; the algebra of a `CommutingStrategy` lives in universe `0`. `commValue` and `entRequirement` are not in this bundle.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Games.lean; blueprint def:game, def:sync-game, def:tensor-strategy, def:q-value, def:sync-strategy, def:pcc, def:sync-value, def:commuting-strategy, def:commuting-value; [JNVWY] Z. Ji, A. Natarajan, T. Vidick, J. Wright, H. Yuen, MIP* = RE, arXiv:2001.04383 (Section 5.2 for PCC strategies)

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Games.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Games, strategies, and values

This file contains the definitions of blueprint Section 2.1 ("Games, strategies, and
values") of the MIP* = RE formalization project: two-player one-round nonlocal games, the
three classes of strategies (tensor-product, synchronous, and commuting), the associated
values, and the entanglement requirement.

The three strategy classes are built on a common skeleton, which this file factors out:
a question-indexed family of projective measurements in a complex star algebra
(`MIPRE.ProjectiveMeasurement`). Tensor-product strategies instantiate it on two matrix
algebras joined by a state vector and the Born rule; synchronous strategies instantiate
it on one matrix algebra `ℂ^{d×d}`, evaluated against the dimension-normalized trace;
commuting strategies are the general case of an abstract unital C*-algebra with a
tracial state (`MIPRE.TracialState`), evaluated by the generic value
`MIPRE.tracialValue`. The inclusion of synchronous into commuting strategies is
`MIPRE.SyncStrategy.toCommutingStrategy`, which preserves the value definitionally; the
comparison of values (blueprint `lem:sync-le-valco`) follows.

The matrix-based definitions (`POVM`, `SynchronousGame`, and the synchronous value)
agree with those of `MIPRE.HaltingGameValue`, which is kept self-contained. The
synchronous strategy is packaged differently there (with `POVM`s in place of a
`ProjectiveMeasurement`); `MIPRE.SyncStrategy.ofPOVM` and `MIPRE.SyncStrategy.value_eq`
provide the correspondence.

## Main definitions

- `MIPRE.Game`: two-player one-round games (blueprint `def:game`).
- `MIPRE.SynchronousGame`: synchronous games, with the interpretation
  `MIPRE.SynchronousGame.toGame` (blueprint `def:sync-game`).
- `MIPRE.ProjectiveMeasurement`: question-indexed projective measurement families in a
  star ring, the common skeleton of the three strategy classes.
- `MIPRE.TracialState`: tracial states on a complex star algebra;
  `MIPRE.normalizedTrace` is the normalized matrix trace `Tr(·)/d`.
- `MIPRE.tracialValue`: the generic value of a projective measurement family against a
  tracial state.
- `MIPRE.POVM`: positive operator-valued measures, following the QuantumLib
  (Lean-QuantumInfo) definition; the vocabulary of the distance measures
  (`MIPRE.Foundations.Distances`) and of the correspondence with
  `MIPRE.HaltingGameValue`.
- `MIPRE.TensorProductStrategy`: finite-dimensional tensor-product strategies, with
  projective measurements on both factors (blueprint `def:tensor-strategy`).
- `MIPRE.quantumValue`: the quantum value `val*` of a game (blueprint `def:q-value`).
- `MIPRE.SyncStrategy`: synchronous strategies (blueprint `def:sync-strategy`), the
  instantiation of the skeleton at `ℂ^{d×d}` with the normalized trace.
- `MIPRE.SyncStrategy.IsPCC`: PCC (projective, consistent, and commuting) strategies
  (blueprint `def:pcc`).
- `MIPRE.syncValue`: the synchronous value of a synchronous game (blueprint
  `def:sync-value`).
- `MIPRE.CommutingStrategy`: commuting strategies, given by a unital C*-algebra with a
  tracial state (blueprint `def:commuting-strategy`).
- `MIPRE.commValue`: the commuting value of a synchronous game (blueprint
  `def:commuting-value`).
- `MIPRE.SyncStrategy.toCommutingStrategy`: a synchronous strategy is a commuting
  strategy, with the same value (`MIPRE.SyncStrategy.value_toCommutingStrategy`).
- `MIPRE.entRequirement`: the entanglement requirement `Ent(G, ν)` (blueprint `def:ent`).

## Main statements

- `MIPRE.tracialValue_nonneg` and `MIPRE.tracialValue_le_one`: the generic value lies in
  `[0, 1]`; the synchronous and commuting values inherit both bounds.
- `MIPRE.ProjectiveMeasurement.consistency`: against a tracial state, a projective
  family answers equal questions with equal answers (probability zero for `a ≠ b`).
- `MIPRE.syncValue_le_quantumValue`: the synchronous value lower-bounds the quantum value
  (blueprint `lem:sync-le-valstar`).
- `MIPRE.syncValue_le_commValue`: the synchronous value lower-bounds the commuting value
  (blueprint `lem:sync-le-valco`).

## Implementation notes

- Question distributions are bare real-valued functions with nonnegativity and
  normalization fields, rather than `PMF` (which is `ℝ≥0∞`-valued and would force
  coercions in the value definitions).
- Outcome probabilities are nonnegative reals, but proving so requires positivity
  arguments; as in `MIPRE.HaltingGameValue`, each value takes the real part `.re` of the
  relevant complex quantity so that the definitions carry no proof obligations.
- The shared layer (`ProjectiveMeasurement`, `TracialState`, `tracialValue`) requires no
  norm: the definitions and the basic lemmas hold over any complex star algebra. The
  C*-structure enters only in `CommutingStrategy`, following the blueprint. In
  particular the matrix-based strategies never need mathlib's (scoped) matrix
  operator-norm instances.
- Tensor-product strategies are defined with projective measurements, as in JNVWY
  (where strategies are assumed projective; by Naimark dilation this loses no
  generality, and allowing general POVMs would define the same quantum value — a fact
  we do not need and do not formalize). General POVMs remain as `POVM`, the vocabulary
  of the distance measures and rounding arguments.
- The algebra of a `CommutingStrategy` lives in universe `0`. This loses no generality:
  for a finite game, the GNS representation of the (separable) C*-subalgebra generated by
  the finitely many measurement operators realizes the same correlation, and it lives in
  universe `0`.
- `SyncStrategy.toCommutingStrategy` realizes the matrix algebra as
  `CStarMatrix (Fin d) (Fin d) ℂ`, mathlib's type synonym of `Matrix` carrying the
  (unscoped) operator-norm `CStarAlgebra` instance. All algebraic instances of
  `CStarMatrix` are definitionally those of `Matrix`, so the strategy transported along
  `CStarMatrix.ofMatrixStarAlgEquiv` has the same value by `rfl`.
- A commuting strategy whose algebra is finite-dimensional is *not* literally a
  synchronous strategy: a finite-dimensional C*-algebra is a direct sum of matrix
  blocks, and its tracial states are the convex combinations of the normalized traces
  of the blocks. The two notions give the same supremum of values (decompose the trace
  and pick the best block), but we do not need this fact; the inclusion
  `SyncStrategy.toCommutingStrategy` is the direction the project uses.
- `POVM` matches the QuantumLib (Lean-QuantumInfo) definition
  (`QuantumInfo.Finite.POVM`), with `selfAdjoint (Matrix d d ℂ)` spelled out for its
  definitionally equal `HermitianMat d ℂ`, so that the strategy layer can be upstreamed.
  `SyncStrategy.povm` and `SyncStrategy.ofPOVM` convert between the
  `ProjectiveMeasurement` packaging and the POVM packaging.

## References

- Ji, Natarajan, Vidick, Wright, Yuen, *MIP\* = RE*, arXiv:2001.04383.
-/

namespace MIPRE

/- The partial order on `ℂ` (for positivity of tracial states) and the Loewner order on
matrices (`0 ≤ A ↔ A.PosSemidef`, for POVM elements) are scoped. -/
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder

/-! ## Games -/

/-- A two-player one-round game (blueprint `def:game`): finite question alphabets `X`,
`Y`, finite answer alphabets `A`, `B`, a probability distribution `μ` on `X × Y`, and a
decision predicate `D` (`true` = accept). -/
structure Game (X Y A B : Type*) [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  /-- The probability that the players are asked the question pair `(x, y)`. -/
  μ : X → Y → ℝ
  /-- Question probabilities are nonnegative. -/
  μ_nonneg : ∀ x y, 0 ≤ μ x y
  /-- Question probabilities sum to one. -/
  μ_sum_one : ∑ x, ∑ y, μ x y = 1
  /-- The decision predicate: `D x y a b = true` means the answers `(a, b)` to the
  questions `(x, y)` are accepted. -/
  D : X → Y → A → B → Bool

/-- A synchronous game (blueprint `def:sync-game`): both players receive questions from
the same alphabet and answer from the same alphabet; on equal questions, unequal answers
always lose. -/
structure SynchronousGame (X A : Type*) [Fintype X] [Fintype A] [DecidableEq A] where
  /-- The probability that the players are asked the question pair `(x, y)`. -/
  μ : X → X → ℝ
  /-- Question probabilities are nonnegative. -/
  μ_nonneg : ∀ x y, 0 ≤ μ x y
  /-- Question probabilities sum to one. -/
  μ_sum_one : ∑ x, ∑ y, μ x y = 1
  /-- The decision predicate: `D x y a b = true` means the answers `(a, b)` to the
  questions `(x, y)` are accepted. -/
  D : X → X → A → A → Bool
  /-- Unequal answers to equal questions are rejected. -/
  synchronous : ∀ x a b, a ≠ b → D x x a b = false

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- A synchronous game is in particular a game, with `Y = X` and `B = A`. -/
def SynchronousGame.toGame [DecidableEq A] (G : SynchronousGame X A) : Game X X A A where
  μ := G.μ
  μ_nonneg := G.μ_nonneg
  μ_sum_one := G.μ_sum_one
  D := G.D

/-! ## Projective measurement families and tracial states

All strategy classes below are built on a common skeleton: a question-indexed family of
projective measurements in a complex star algebra. Tensor-product and synchronous
strategies instantiate it on matrix algebras; commuting strategies on an abstract unital
C*-algebra, evaluated against a tracial state. The skeleton is defined once, so that
the definitions and basic lemmas are shared. No norm is needed at this level of
generality. -/

/-- A question-indexed family of projective measurements with outcomes in a star ring
`𝒜`: for each question `x`, the operators `M x a` are self-adjoint idempotents (i.e.
orthogonal projections) that sum to one. This is the common skeleton of the strategy
classes: tensor-product strategies (`TensorProductStrategy`) and synchronous strategies
(`SyncStrategy`) instantiate it at matrix algebras, commuting strategies
(`CommutingStrategy`) at an abstract unital C*-algebra. -/
structure ProjectiveMeasurement (X A 𝒜 : Type*) [Fintype A] [Ring 𝒜] [StarRing 𝒜] where
  /-- The measurement operators, indexed by questions and answers. -/
  M : X → A → 𝒜
  /-- Each measurement operator is self-adjoint. -/
  selfAdjoint : ∀ x a, star (M x a) = M x a
  /-- Each measurement operator is idempotent, hence a projection. -/
  projective : ∀ x a, M x a * M x a = M x a
  /-- For each question, the measurement operators sum to one. -/
  normalized : ∀ x, ∑ a, M x a = 1

/-- A tracial state on a complex star algebra `𝒜`: a linear functional that is positive
(`0 ≤ τ (star m * m)`, in the order of `ℂ`), unital (`τ 1 = 1`), and tracial
(`τ (m * n) = τ (n * m)`). On a unital C*-algebra this is the standard notion of tracial
state (blueprint `def:commuting-strategy`). -/
structure TracialState (𝒜 : Type*) [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜] extends
    𝒜 →ₗ[ℂ] ℂ where
  /-- The functional is positive. -/
  nonneg' : ∀ m, 0 ≤ toLinearMap (star m * m)
  /-- The functional is unital. -/
  map_one' : toLinearMap 1 = 1
  /-- The functional is tracial. -/
  map_mul_comm' : ∀ m n, toLinearMap (m * n) = toLinearMap (n * m)

variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]

namespace TracialState

instance : FunLike (TracialState 𝒜) 𝒜 ℂ where
  coe τ := ⇑τ.toLinearMap
  coe_injective τ σ h := by
    cases τ; cases σ; congr; exact DFunLike.coe_injective h

instance : LinearMapClass (TracialState 𝒜) ℂ 𝒜 ℂ where
  map_add τ := map_add τ.toLinearMap
  map_smulₛₗ τ := map_smulₛₗ τ.toLinearMap

@[simp] theorem coe_toLinearMap (τ : TracialState 𝒜) : ⇑τ.toLinearMap = ⇑τ := rfl

@[simp] theorem coe_mk (f : 𝒜 →ₗ[ℂ] ℂ) (h₁ h₂ h₃) :
    ⇑(⟨f, h₁, h₂, h₃⟩ : TracialState 𝒜) = ⇑f := rfl

/-- A tracial state is positive. -/
theorem star_mul_self_nonneg (τ : TracialState 𝒜) (m : 𝒜) : 0 ≤ τ (star m * m) :=
  τ.nonneg' m

/-- A tracial state is unital. -/
@[simp] theorem map_one (τ : TracialState 𝒜) : τ 1 = 1 := τ.map_one'

/-- A tracial state is tracial. -/
theorem map_mul_comm (τ : TracialState 𝒜) (m n : 𝒜) : τ (m * n) = τ (n * m) :=
  τ.map_mul_comm' m n

/-- Pull back a tracial state along a star-algebra equivalence. -/
def comp (τ : TracialState ℬ) (φ : 𝒜 ≃⋆ₐ[ℂ] ℬ) : TracialState 𝒜 where
  toLinearMap :=
    { toFun := fun m => τ (φ m)
      map_add' := fun m n => by simp [map_add]
      map_smul' := fun c m => by simp [map_smul] }
  nonneg' m := by
    show 0 ≤ τ (φ (star m * m))
    rw [map_mul φ, map_star φ]
    exact τ.star_mul_self_nonneg _
  map_one' := by
    show τ (φ 1) = 1
    rw [_root_.map_one φ, τ.map_one]
  map_mul_comm' m n := by
    show τ (φ (m * n)) = τ (φ (n * m))
    rw [map_mul φ, map_mul φ, τ.map_mul_comm]

@[simp] theorem comp_apply (τ : TracialState ℬ) (φ : 𝒜 ≃⋆ₐ[ℂ] ℬ) (m : 𝒜) :
    τ.comp φ m = τ (φ m) := rfl

end TracialState

namespace ProjectiveMeasurement

/-- Transport a projective measurement family along a star-algebra equivalence. -/
def map (φ : 𝒜 ≃⋆ₐ[ℂ] ℬ) (P : ProjectiveMeasurement X A 𝒜) :
    ProjectiveMeasurement X A ℬ where
  M x a := φ (P.M x a)
  selfAdjoint x a := by rw [← map_star, P.selfAdjoint]
  projective x a := by rw [← map_mul, P.projective]
  normalized x := by rw [← map_sum, P.normalized, map_one]

omit [Fintype X] in
@[simp] theorem map_M (φ : 𝒜 ≃⋆ₐ[ℂ] ℬ) (P : ProjectiveMeasurement X A 𝒜) (x : X)
    (a : A) : (P.map φ).M x a = φ (P.M x a) := rfl

variable [DecidableEq A]

end ProjectiveMeasurement

/-! ## POVMs -/

/-- A POVM is a (finite) collection of PSD matrices on the same Hilbert space that sum
to the identity. Here `X` indexes the matrices, and `d` is the space dimension.

This is the QuantumLib (Lean-QuantumInfo) definition of `POVM`, with
`selfAdjoint (Matrix d d ℂ)` spelled out for its definitionally equal
`HermitianMat d ℂ`; `0 ≤ mats x` is the Loewner order, i.e. positive semidefiniteness.

General POVMs are not part of the strategy definitions (strategies are projective, via
`ProjectiveMeasurement`); they are the vocabulary of the distance measures
(`MIPRE.Foundations.Distances`) and of the correspondence with
`MIPRE.HaltingGameValue` (`SyncStrategy.povm`, `SyncStrategy.ofPOVM`). -/
structure POVM (X : Type*) (d : Type*) [Fintype X] [Fintype d] [DecidableEq d] where
  /-- The measurement operators, one for each outcome. -/
  mats : X → selfAdjoint (Matrix d d ℂ)
  /-- Each measurement operator is positive semidefinite. -/
  nonneg : ∀ x, 0 ≤ mats x
  /-- The measurement operators sum to the identity. -/
  normalized : ∑ x, mats x = 1

/-! ## Tensor-product strategies and the quantum value -/

/-- A tensor-product strategy for a game `G` (blueprint `def:tensor-strategy`):
finite-dimensional Hilbert spaces `ℂ^dA` and `ℂ^dB`, a unit vector `ψ` in their tensor
product — realized as `Fin dA × Fin dB → ℂ` — and projective measurements `{A^x_a}` on
`ℂ^dA` and `{B^y_b}` on `ℂ^dB`, packaged as `ProjectiveMeasurement` families on the two
matrix algebras. Restricting to projective measurements follows JNVWY; by Naimark
dilation this loses no generality. Outcome probabilities are computed using the Born
rule (see `TensorProductStrategy.value`). -/
structure TensorProductStrategy (G : Game X Y A B) where
  /-- The dimension of the first player's Hilbert space. -/
  dA : ℕ
  /-- The dimension of the second player's Hilbert space. -/
  dB : ℕ
  /-- The shared state, a vector in the tensor product `ℂ^dA ⊗ ℂ^dB = ℂ^(dA × dB)`. -/
  ψ : Fin dA × Fin dB → ℂ
  /-- The shared state is a unit vector. (In particular `dA` and `dB` are positive,
  since a zero-dimensional space contains no unit vector.) -/
  ψ_unit : star ψ ⬝ᵥ ψ = 1
  /-- The first player's measurements: for each question `x`, a projective measurement
  on `ℂ^dA`. -/
  PA : ProjectiveMeasurement X A (Matrix (Fin dA) (Fin dA) ℂ)
  /-- The second player's measurements: for each question `y`, a projective measurement
  on `ℂ^dB`. -/
  PB : ProjectiveMeasurement Y B (Matrix (Fin dB) (Fin dB) ℂ)

/-- The value of a tensor-product strategy in `G` (blueprint `def:q-value`): the players
answer questions `(x, y)` with `(a, b)` with the Born-rule probability
`⟨ψ| A^x_a ⊗ B^y_b |ψ⟩`, the tensor product being realized by the Kronecker product.
The probability is a nonnegative real; we take the real part so that the definition
typechecks with no proof obligations. -/
noncomputable def TensorProductStrategy.value {G : Game X Y A B}
    (S : TensorProductStrategy G) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b,
    G.μ x y * (if G.D x y a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re

/-- The quantum value `val*(G)` of a game (blueprint `def:q-value`): the supremum of
strategy values over all tensor-product strategies. -/
noncomputable def quantumValue (G : Game X Y A B) : ℝ :=
  ⨆ S : TensorProductStrategy G, S.value

/-! ### Born-rule bounds

The quantum value is a supremum over a type that may be empty, so the comparison lemmas
below need the range of `TensorProductStrategy.value` to be bounded and `quantumValue` to
be nonnegative. Both come from the Born rule: for fixed questions the outcome
probabilities are nonnegative and sum to `⟨ψ|ψ⟩ = 1`.

(`MIPRE.Repetition` proves the same two bounds by transporting through the vendored
parallel-repetition development; those proofs are not available here, since
`MIPRE/Foundations/` cannot import `MIPRE/Background/`.) -/

/-- A Kronecker product of two projections is positive semidefinite: it is its own
`Pᴴ * P`. A candidate for `MIPRE/Mathlib/` if a second consumer appears. -/
theorem posSemidef_kronecker {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {P : Matrix m m ℂ} {Q : Matrix n n ℂ} (hPs : star P = P)
    (hPp : P * P = P) (hQs : star Q = Q) (hQp : Q * Q = Q) : (P ⊗ₖ Q).PosSemidef := by
  have hPH : Pᴴ = P := by rw [← Matrix.star_eq_conjTranspose]; exact hPs
  have hQH : Qᴴ = Q := by rw [← Matrix.star_eq_conjTranspose]; exact hQs
  have h : (P ⊗ₖ Q)ᴴ * (P ⊗ₖ Q) = P ⊗ₖ Q := by
    rw [Matrix.conjTranspose_kronecker, hPH, hQH, ← Matrix.mul_kronecker_mul, hPp, hQp]
  have := Matrix.posSemidef_conjTranspose_mul_self (P ⊗ₖ Q)
  rwa [h] at this

namespace TensorProductStrategy

variable {G : Game X Y A B}

/-- A Born-rule probability of a tensor-product strategy is nonnegative: `A^x_a ⊗ B^y_b`
is a projection, hence positive semidefinite. -/
theorem re_dotProduct_nonneg (S : TensorProductStrategy G) (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re := by
  have hps := posSemidef_kronecker (S.PA.selfAdjoint x a) (S.PA.projective x a)
    (S.PB.selfAdjoint y b) (S.PB.projective y b)
  simpa using (Complex.le_def.mp (hps.dotProduct_mulVec_nonneg S.ψ)).1

/-- The value of a tensor-product strategy is nonnegative. -/
theorem value_nonneg (S : TensorProductStrategy G) : 0 ≤ S.value := by
  refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  have hind : (0 : ℝ) ≤ if G.D x y a b then 1 else 0 := by split_ifs <;> norm_num
  exact mul_nonneg (mul_nonneg (G.μ_nonneg x y) hind) (S.re_dotProduct_nonneg x y a b)

/-- For each question pair the Born-rule probabilities sum to `⟨ψ|ψ⟩ = 1`: the measurement
operators sum to one on each side, and the Kronecker product is bilinear. -/
theorem sum_dotProduct_kronecker (S : TensorProductStrategy G) (x : X) (y : Y) :
    ∑ a, ∑ b, (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)) = 1 := by
  have hmat : ∑ a, ∑ b, (S.PA.M x a ⊗ₖ S.PB.M y b) = 1 := by
    have hsplit : ∑ a, ∑ b, (S.PA.M x a ⊗ₖ S.PB.M y b)
        = (∑ a, S.PA.M x a) ⊗ₖ (∑ b, S.PB.M y b) := by
      ext p q
      simp only [Matrix.sum_apply, kroneckerMap_apply, Finset.sum_mul_sum]
    rw [hsplit, S.PA.normalized, S.PB.normalized, Matrix.one_kronecker_one]
  calc ∑ a, ∑ b, (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ))
      = star S.ψ ⬝ᵥ ((∑ a, ∑ b, (S.PA.M x a ⊗ₖ S.PB.M y b)) *ᵥ S.ψ) := by
        simp_rw [Matrix.sum_mulVec, dotProduct_sum]
    _ = star S.ψ ⬝ᵥ S.ψ := by rw [hmat, Matrix.one_mulVec]
    _ = 1 := S.ψ_unit

/-- The value of a tensor-product strategy is at most one. -/
theorem value_le_one (S : TensorProductStrategy G) : S.value ≤ 1 := by
  have key : ∀ x y, ∑ a, ∑ b,
      (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re = 1 := fun x y => by
    simpa [Complex.re_sum] using congrArg Complex.re (S.sum_dotProduct_kronecker x y)
  calc S.value
      ≤ ∑ x, ∑ y, G.μ x y * ∑ a, ∑ b,
          (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun b _ => ?_
        cases hD : G.D x y a b with
        | false =>
          simpa [hD] using mul_nonneg (G.μ_nonneg x y) (S.re_dotProduct_nonneg x y a b)
        | true => simp
    _ = ∑ x, ∑ y, G.μ x y := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [key, mul_one]
    _ = 1 := G.μ_sum_one

/-- The values of tensor-product strategies are bounded above (by one). -/
theorem bddAbove_range_value (G : Game X Y A B) :
    BddAbove (Set.range fun S : TensorProductStrategy G => S.value) := by
  refine ⟨1, ?_⟩
  rintro r ⟨S, rfl⟩
  exact S.value_le_one

end TensorProductStrategy

/-- The quantum value is nonnegative. -/
theorem quantumValue_nonneg (G : Game X Y A B) : 0 ≤ quantumValue G :=
  Real.iSup_nonneg fun S => S.value_nonneg

/-! ## The generic tracial value -/

variable [DecidableEq A]

/-- The value of a projective measurement family `P` against a tracial state `τ` in a
synchronous game `G`: the players answer questions `(x, y)` with `(a, b)` with
probability `τ (M^x_a M^y_b)`, a nonnegative real by `TracialState.nonneg_mul`; we take
the real part so that the definition carries no proof obligations. The synchronous value
(blueprint `def:sync-value`) and the commuting value (blueprint `def:commuting-value`)
are instantiations. -/
noncomputable def tracialValue (G : SynchronousGame X A) (τ : TracialState 𝒜)
    (P : ProjectiveMeasurement X A 𝒜) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b,
    G.μ x y * (if G.D x y a b then 1 else 0) * (τ (P.M x a * P.M y b)).re

/-- The dimension-normalized trace `τ(m) = Tr(m)/n` is a tracial state on the matrix
algebra `ℂ^{n×n}` (in fact its unique tracial state, though we do not prove this). -/
noncomputable def normalizedTrace (n : Type*) [Fintype n] [DecidableEq n]
    [hn : Nonempty n] : TracialState (Matrix n n ℂ) where
  toLinearMap := (Fintype.card n : ℂ)⁻¹ • Matrix.traceLinearMap n ℂ ℂ
  nonneg' m := by
    show (0 : ℂ) ≤ (Fintype.card n : ℂ)⁻¹ * (star m * m).trace
    refine mul_nonneg ?_ ?_
    · rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
      exact Complex.zero_le_real.mpr (by positivity)
    · have h := Matrix.posSemidef_conjTranspose_mul_self m
      rw [← Matrix.star_eq_conjTranspose] at h
      exact h.trace_nonneg
  map_one' := by
    show (Fintype.card n : ℂ)⁻¹ * (1 : Matrix n n ℂ).trace = 1
    rw [Matrix.trace_one, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  map_mul_comm' m₁ m₂ := by
    show (Fintype.card n : ℂ)⁻¹ * (m₁ * m₂).trace =
      (Fintype.card n : ℂ)⁻¹ * (m₂ * m₁).trace
    rw [Matrix.trace_mul_comm]

@[simp] theorem normalizedTrace_apply (n : Type*) [Fintype n] [DecidableEq n]
    [Nonempty n] (m : Matrix n n ℂ) :
    normalizedTrace n m = (Fintype.card n : ℂ)⁻¹ * m.trace := rfl

/-! ## Synchronous strategies and the synchronous value -/

/-- A synchronous strategy for a synchronous game (blueprint `def:sync-strategy`): a
question-indexed projective measurement family on `ℂ^d` (`d > 0`). Measurements for
different questions need not commute. There is no state vector: outcome probabilities
are computed with the dimension-normalized trace `τ(M) = Tr(M)/d` (see
`SyncStrategy.value`). This is the instantiation of the commuting framework at the full
matrix algebra with its canonical tracial state, see
`SyncStrategy.toCommutingStrategy`. -/
structure SyncStrategy (G : SynchronousGame X A) where
  /-- The dimension of the Hilbert space. -/
  d : ℕ
  /-- The dimension is positive. -/
  d_pos : 0 < d
  /-- The measurements: for each question, a projective measurement on `ℂ^d`. -/
  P : ProjectiveMeasurement X A (Matrix (Fin d) (Fin d) ℂ)

namespace SyncStrategy

variable {G : SynchronousGame X A}

/-- The value of a synchronous strategy in `G` (blueprint `def:sync-value`): the generic
tracial value against the normalized trace `τ(M) = Tr(M)/d`. See `SyncStrategy.value_eq`
for the explicit form. -/
noncomputable def value (S : SyncStrategy G) : ℝ :=
  tracialValue G (normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)) S.P

/-- The value of a synchronous strategy, written out (the spelling of blueprint
`def:sync-value` and of `MIPRE.HaltingGameValue.strategyValue`): the players answer
questions `(x, y)` with `(a, b)` with probability `Tr(M^x_a M^y_b)/d`. -/
theorem value_eq (S : SyncStrategy G) :
    S.value = ∑ x, ∑ y, ∑ a, ∑ b,
      G.μ x y * (if G.D x y a b then 1 else 0) *
        ((S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ)) := by
  unfold value tracialValue
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  show ((Fintype.card (Fin S.d) : ℂ)⁻¹ * (S.P.M x a * S.P.M y b).trace).re = _
  rw [Fintype.card_fin, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    Complex.re_ofReal_mul, inv_mul_eq_div]

/-- The measurements of a synchronous strategy, packaged as POVMs (positivity follows
from projectivity). This is the interface to the QuantumLib-compatible `POVM` layer. -/
def povm (S : SyncStrategy G) (x : X) : POVM A (Fin S.d) where
  mats a := ⟨S.P.M x a, selfAdjoint.mem_iff.mpr (S.P.selfAdjoint x a)⟩
  nonneg a := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (S.P.M x a)
    rw [← Matrix.star_eq_conjTranspose, S.P.selfAdjoint x a, S.P.projective x a] at h
    exact Subtype.coe_le_coe.mp h.nonneg
  normalized := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact S.P.normalized x

/-- A synchronous strategy is *PCC* (*projective, consistent, and commuting*, following
JNVWY Section 5.2; blueprint `def:pcc`) if the measurement operators associated with any
pair of questions asked with positive probability commute. Projectivity is part of
`SyncStrategy`, and consistency is automatic for synchronous strategies
(`ProjectiveMeasurement.consistency`), so only the commutation condition remains. -/
def IsPCC (S : SyncStrategy G) : Prop :=
  ∀ x y, 0 < G.μ x y → ∀ a b,
    S.P.M x a * S.P.M y b = S.P.M y b * S.P.M x a

end SyncStrategy

/-- The synchronous value of a synchronous game (blueprint `def:sync-value`): the
supremum of strategy values over all synchronous strategies. -/
noncomputable def syncValue (G : SynchronousGame X A) : ℝ :=
  ⨆ S : SyncStrategy G, S.value

/-! ## Commuting strategies and the commuting value -/

/-- A commuting strategy for a synchronous game (blueprint `def:commuting-strategy`): a
unital C*-algebra `alg` with a tracial state `τ`, together with a question-indexed
projective measurement family in `alg`. Outcome probabilities are computed with `τ` (see
`CommutingStrategy.value`).

The algebra lives in universe `0`; by the GNS representation this loses no generality
(see the module docstring). -/
structure CommutingStrategy (G : SynchronousGame X A) where
  /-- The underlying unital C*-algebra. -/
  alg : Type
  /-- The C*-algebra structure. -/
  [cstarAlgebra : CStarAlgebra alg]
  /-- The tracial state. -/
  τ : TracialState alg
  /-- The measurements: for each question, a projective measurement in `alg`. -/
  P : ProjectiveMeasurement X A alg

attribute [instance] MIPRE.CommutingStrategy.cstarAlgebra

namespace CommutingStrategy

variable {G : SynchronousGame X A}

/-- The value of a commuting strategy in `G` (blueprint `def:commuting-value`): the
generic tracial value; the players answer questions `(x, y)` with `(a, b)` with
probability `τ(M^x_a M^y_b)`. -/
noncomputable def value (S : CommutingStrategy G) : ℝ :=
  tracialValue G S.τ S.P

end CommutingStrategy

/-! ## A synchronous strategy is a commuting strategy -/

/-- A synchronous strategy is a commuting strategy (the content of blueprint
`lem:sync-le-valco`): take the algebra of `d × d` complex matrices with the normalized
trace. The algebra is realized as `CStarMatrix (Fin d) (Fin d) ℂ` — mathlib's type
synonym of `Matrix` carrying the operator-norm `CStarAlgebra` instance — and the
measurements and the state are transported along the definitionally trivial
star-algebra equivalence `CStarMatrix.ofMatrixStarAlgEquiv`. The value is preserved:
`SyncStrategy.value_toCommutingStrategy`. -/
noncomputable def SyncStrategy.toCommutingStrategy {G : SynchronousGame X A}
    (S : SyncStrategy G) : CommutingStrategy G where
  alg := CStarMatrix (Fin S.d) (Fin S.d) ℂ
  τ := (normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)).comp
    CStarMatrix.ofMatrixStarAlgEquiv.symm
  P := S.P.map CStarMatrix.ofMatrixStarAlgEquiv

/-- `SyncStrategy.toCommutingStrategy` preserves the value — definitionally. -/
@[simp] theorem SyncStrategy.value_toCommutingStrategy {G : SynchronousGame X A}
    (S : SyncStrategy G) : S.toCommutingStrategy.value = S.value :=
  rfl

/-! ## Entanglement requirement -/

/-! ## Relationship lemmas -/

/-! ### The maximally entangled state

The transpose trick: on `ψ = d^{-1/2} ∑ᵢ |i⟩|i⟩` one has `⟨ψ| M ⊗ N |ψ⟩ = Tr(M Nᵀ)/d`, so
`N = (M')ᵀ` turns the Born rule into the normalized trace that defines the synchronous
value. Like `posSemidef_kronecker`, these three are candidates for `MIPRE/Mathlib/` once a
second consumer appears. -/

/-- The maximally entangled state `d^{-1/2} ∑ᵢ |i⟩|i⟩` on `ℂ^d ⊗ ℂ^d`, realized as a
vector on `Fin d × Fin d`. -/
noncomputable def maxEntangled (d : ℕ) : Fin d × Fin d → ℂ :=
  fun p => if p.1 = p.2 then ((Real.sqrt d)⁻¹ : ℝ) else 0

/-- `d^{-1/2} · d^{-1/2} = d⁻¹`, in `ℂ`. -/
theorem ofReal_invSqrt_mul_self (d : ℕ) :
    ((((Real.sqrt d)⁻¹ : ℝ)) : ℂ) * ((((Real.sqrt d)⁻¹ : ℝ)) : ℂ) = (d : ℂ)⁻¹ := by
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg d),
    Complex.ofReal_inv, Complex.ofReal_natCast]

/-- The maximally entangled state is a unit vector. -/
theorem dotProduct_maxEntangled_self {d : ℕ} (hd : 0 < d) :
    star (maxEntangled d) ⬝ᵥ maxEntangled d = 1 := by
  classical
  simp only [dotProduct, maxEntangled, Pi.star_apply, Fintype.sum_prod_type,
    apply_ite (starRingEnd ℂ), map_zero, Complex.star_def, Complex.conj_ofReal,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    ofReal_invSqrt_mul_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hd.ne')

/-- One entry of `(M ⊗ₖ N) *ᵥ ψ` against the maximally entangled state. -/
theorem kronecker_mulVec_maxEntangled {d : ℕ} (M N : Matrix (Fin d) (Fin d) ℂ)
    (p : Fin d × Fin d) :
    ((M ⊗ₖ N) *ᵥ maxEntangled d) p
      = (((Real.sqrt d)⁻¹ : ℝ) : ℂ) * ∑ k, M p.1 k * N p.2 k := by
  classical
  simp [mulVec, dotProduct, maxEntangled, Fintype.sum_prod_type, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mul_sum, mul_comm, mul_assoc]

/-- The transpose trick: `⟨ψ| M ⊗ N |ψ⟩ = Tr(M Nᵀ)/d` on the maximally entangled state. -/
theorem dotProduct_kronecker_maxEntangled {d : ℕ} (M N : Matrix (Fin d) (Fin d) ℂ) :
    star (maxEntangled d) ⬝ᵥ ((M ⊗ₖ N) *ᵥ maxEntangled d) = (d : ℂ)⁻¹ * (M * Nᵀ).trace := by
  classical
  simp only [dotProduct, kronecker_mulVec_maxEntangled, maxEntangled, Pi.star_apply,
    Fintype.sum_prod_type, apply_ite (starRingEnd ℂ), map_zero, Complex.star_def,
    Complex.conj_ofReal, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [← mul_assoc, ofReal_invSqrt_mul_self, ← Finset.mul_sum, trace, diag_apply,
    mul_apply, transpose_apply]

/-! ### A synchronous strategy is a tensor-product strategy -/

/-- A synchronous strategy `{M^x_a}` on `ℂ^d` as a tensor-product strategy for the same
game (the content of blueprint `lem:sync-le-valstar`): `A^x_a = M^x_a`, `B^y_b = (M^y_b)ᵀ`,
and the maximally entangled state. Transposing preserves self-adjointness and
projectivity, and reverses products, so the transposed family is again a projective
measurement. -/
noncomputable def SyncStrategy.toTensorProductStrategy {G : SynchronousGame X A}
    (S : SyncStrategy G) : TensorProductStrategy G.toGame where
  dA := S.d
  dB := S.d
  ψ := maxEntangled S.d
  ψ_unit := dotProduct_maxEntangled_self S.d_pos
  PA := S.P
  PB :=
    { M := fun y b => (S.P.M y b)ᵀ
      selfAdjoint := fun y b => by
        rw [show star ((S.P.M y b)ᵀ) = (star (S.P.M y b))ᵀ from rfl, S.P.selfAdjoint y b]
      projective := fun y b => by
        rw [← Matrix.transpose_mul, S.P.projective y b]
      normalized := fun y => by
        rw [← Matrix.transpose_sum, S.P.normalized y, Matrix.transpose_one] }

/-- `SyncStrategy.toTensorProductStrategy` preserves the value: the Born-rule probability
`⟨ψ| M^x_a ⊗ (M^y_b)ᵀ |ψ⟩` is `Tr(M^x_a M^y_b)/d`, which is the probability computed by
`SyncStrategy.value` (see `SyncStrategy.value_eq`). -/
@[simp] theorem SyncStrategy.value_toTensorProductStrategy {G : SynchronousGame X A}
    (S : SyncStrategy G) : S.toTensorProductStrategy.value = S.value := by
  rw [S.value_eq]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  show (star (maxEntangled S.d) ⬝ᵥ ((S.P.M x a ⊗ₖ (S.P.M y b)ᵀ) *ᵥ maxEntangled S.d)).re = _
  rw [dotProduct_kronecker_maxEntangled, Matrix.transpose_transpose,
    show ((S.d : ℂ))⁻¹ = (((S.d : ℝ)⁻¹ : ℝ) : ℂ) by
      rw [Complex.ofReal_inv, Complex.ofReal_natCast],
    Complex.re_ofReal_mul, inv_mul_eq_div]

end MIPRE


