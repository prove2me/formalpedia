-- Prove2me | Definitions.Def_Formalism_HermitianLattices_StatementMaj
-- name    : Formalism_HermitianLattices_StatementMaj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:42.461575+00:00
-- url     : https://prove2.me/theorems/e49dfb6b-5599-4365-9038-f8d9a87404b4
-- title:
--   Statement Maj
-- statement:
--   Definitions and structural lemmas for Statement Maj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/StatementMaj.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace Formalism.HermitianLatticesTheory
section Maj
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
def vecAt (b : Module.Basis ι K V) (v : InfinitePlace K) (x : V) : ι → ℂ :=
  fun i => v.embedding (b.repr x i)
def gramAt (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V) (v : InfinitePlace K) :
    Matrix ι ι ℂ :=
  Matrix.of fun i j => v.embedding (h (b i) (b j))
def IsFrame (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V) (v : InfinitePlace K)
    (X : Matrix ι ι ℂ) : Prop :=
  IsUnit X.det ∧ ∃ ε : ι → ℂ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
    X.conjTranspose * gramAt h b v * X = Matrix.diagonal ε
def fcoord (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : ι → ℂ :=
  Matrix.mulVec (X v)⁻¹ (vecAt b v x)
def cnorm (u : ι → ℂ) : ℝ := Real.sqrt (∑ i, ‖u i‖ ^ 2)
def normAt (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : ℝ :=
  cnorm (fcoord b X v x)
def majAt (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x y : V) : ℂ :=
  ∑ i, star (fcoord b X v x i) * fcoord b X v y i
def jAt (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) : Matrix ι ι ℂ :=
  X v * ((X v).conjTranspose * gramAt h b v * X v) * (X v)⁻¹
def sgnAt (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (i : ι) : ℝ :=
  (((X v).conjTranspose * gramAt h b v * X v) i i).re
theorem fcoord_add (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x y : V) : fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
  unfold fcoord
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp [vecAt, map_add]
theorem fcoord_zero (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) : fcoord b X v 0 = 0 := by
  have h0 : vecAt b v 0 = 0 := by
    funext i
    simp [vecAt]
  simp only [fcoord, h0, Matrix.mulVec_zero]
def realizeRaw (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) :
    V →+ (InfinitePlace K × ι × Fin 2 → ℝ) where
  toFun x p := if p.2.2 = 0 then (fcoord b X p.1 x p.2.1).re else (fcoord b X p.1 x p.2.1).im
  map_zero' := by
    funext p
    simp [fcoord_zero]
  map_add' := by
    intro x y
    funext p
    simp only [fcoord_add, Pi.add_apply]
    split_ifs <;> simp
def realize (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) :
    V →+ EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
  (WithLp.linearEquiv 2 ℝ (InfinitePlace K × ι × Fin 2 → ℝ)).symm.toLinearMap.toAddMonoidHom.comp
    (realizeRaw b X)
def jW (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :
    EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
  (WithLp.equiv 2 _).symm fun p => sgnAt h b X p.1 p.2.1 * w p
def tdual {R : Type*} [CommRing R] [Module R V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) :
    Set V :=
  {y | ∀ x ∈ L, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = z}
def invDiff (K : Type*) [Field K] [NumberField K] : Set K :=
  {a | ∀ r : RingOfIntegers K, ∃ z : ℤ, Algebra.trace ℚ K (a * r) = z}
def dualI {R : Type*} [CommRing R] [Module R V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V)
    (I : Set K) : Set V :=
  {x | ∀ y ∈ L, h y x ∈ I}
variable [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
def idealSmul (I : Submodule (RingOfIntegers K) K) (L : Submodule (RingOfIntegers K) V) :
    Submodule (RingOfIntegers K) V :=
  Submodule.span (RingOfIntegers K) {z | ∃ a ∈ I, ∃ x ∈ L, z = a • x}
def content (L : Submodule (RingOfIntegers K) V) (y : V) : Submodule (RingOfIntegers K) K :=
  sInf {I | y ∈ idealSmul I L}
def contentIdeal (L : Submodule (RingOfIntegers K) V) (y : V) : Ideal (RingOfIntegers K) :=
  (content L y).comap (Algebra.linearMap (RingOfIntegers K) K)
def heightMaj (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (RingOfIntegers K) V) (y : V) : ℝ :=
  ((∏ v, normAt b X v y ^ 2) / (Ideal.absNorm (contentIdeal L y) : ℝ)) ^
    ((1 : ℝ) / (2 * Fintype.card (InfinitePlace K)))
def matAt (b : Module.Basis ι K V) (v : InfinitePlace K) (g : V →ₗ[K] V) : Matrix ι ι ℂ :=
  (LinearMap.toMatrix b b g).map v.embedding
def OpBoundAt (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (g : V →ₗ[K] V) (δ : ℝ) : Prop :=
  ∀ u : ι → ℂ, cnorm (Matrix.mulVec (X v)⁻¹ (Matrix.mulVec (matAt b v g - 1) u)) ≤
    δ * cnorm (Matrix.mulVec (X v)⁻¹ u)
end Maj
def invDiffSub (K : Type*) [Field K] [NumberField K] : Submodule (RingOfIntegers K) K :=
  Submodule.span (RingOfIntegers K) (invDiff K)
def MajBasic : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ), h.IsSymm →
    (∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) →
    (∀ v, IsFrame h b v (X v)) →
    (∀ v : InfinitePlace K,
      jAt h b X v * jAt h b X v = 1 ∧
      (jAt h b X v).conjTranspose * gramAt h b v * jAt h b X v = gramAt h b v ∧
      (jAt h b X v).conjTranspose * gramAt h b v = gramAt h b v * jAt h b X v ∧
      (∀ x y : V, majAt b X v x y = dotProduct (star (vecAt b v x))
        (Matrix.mulVec ((jAt h b X v).conjTranspose * gramAt h b v) (vecAt b v y))) ∧
      (∀ x : V, majAt b X v x x = ((normAt b X v x ^ 2 : ℝ) : ℂ)) ∧
      (∀ x : V, normAt b X v x = 0 → x = 0) ∧
      (∀ x : V, ‖v.embedding (h x x)‖ ≤ normAt b X v x ^ 2)) ∧
    ∀ x : V, ‖realize b X x‖ ^ 2 = ∑ v, normAt b X v x ^ 2
def MajDual : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K] [AddCommGroup V]
    [Module K V] [Fintype ι] [DecidableEq ι] [Module (RingOfIntegers K) V]
    [IsScalarTower (RingOfIntegers K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ), h.IsSymm →
    (∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) →
    (∀ v, IsFrame h b v (X v)) →
    (∀ x y : V, inner ℝ (realize b X x) (jW h b X (realize b X y)) =
      ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ) / 2) ∧
    ∀ L : Submodule (RingOfIntegers K) V, Submodule.IsLattice K L →
      (∃ _ : DiscreteTopology (zmap (realize b X) L), IsZLattice ℝ (zmap (realize b X) L)) ∧
      (∀ w, w ∈ Formalism.HadamardInequality.zdual (zmap (realize b X) L) ↔
        ∃ y : V, (∀ x ∈ L, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = 2 * z) ∧
          w = jW h b X (realize b X y)) ∧
      (∀ y : V, y ∈ tdual h L ↔ y ∈ dualI h L (invDiff K)) ∧
      (IsUnimodular h L → ∀ y : V, y ∈ dualI h L (invDiff K) ↔ y ∈ idealSmul (invDiffSub K) L)
def HeightBasic : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K] [AddCommGroup V]
    [Module K V] [Fintype ι] [DecidableEq ι] [Module (RingOfIntegers K) V]
    [IsScalarTower (RingOfIntegers K) K V] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (RingOfIntegers K) V),
    Submodule.IsLattice K L → ∀ y ∈ L, y ≠ 0 →
      y ∈ idealSmul (content L y) L ∧ content L y ≤ 1 ∧
      1 ≤ Ideal.absNorm (contentIdeal L y) ∧
      heightMaj b X L y ≤ (∏ v, normAt b X v y ^ 2) ^ ((1 : ℝ) / (2 * Fintype.card (InfinitePlace K))) ∧
      ∀ a : RingOfIntegers K, a ≠ 0 → heightMaj b X L ((a : K) • y) = heightMaj b X L y
def OpBound : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (g : V →ₗ[K] V) (δ : ℝ), 0 ≤ δ → (∀ v, OpBoundAt b X v g δ) →
    ∀ y : V, ‖realize b X (g y - y)‖ ≤ δ * ‖realize b X y‖
def FrameBasic : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V), h.IsSymm →
    (∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) →
    ∀ v : InfinitePlace K,
      (h.Nondegenerate → ∃ X : Matrix ι ι ℂ, IsFrame h b v X) ∧
      ∀ X g : Matrix ι ι ℂ, IsFrame h b v X →
        g.conjTranspose * gramAt h b v * g = gramAt h b v → IsFrame h b v (g * X)
def RealizeBasic : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ),
    (∀ (v : InfinitePlace K) (a : K) (x : V), fcoord b X v (a • x) = v.embedding a • fcoord b X v x) ∧
    ∀ (q : ℚ) (x : V), realize b X (algebraMap ℚ K q • x) = (q : ℝ) • realize b X x
def MajLattice : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K] [AddCommGroup V]
    [Module K V] [Fintype ι] [DecidableEq ι] [Module (RingOfIntegers K) V]
    [IsScalarTower (RingOfIntegers K) K V] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ L : Submodule (RingOfIntegers K) V, Submodule.IsLattice K L →
      DiscreteTopology (zmap (realize b X) L) ∧
      Submodule.span ℝ ((zmap (realize b X) L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))) = ⊤
end Formalism.HermitianLatticesTheory


