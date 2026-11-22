-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
-- name    : Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:52:22.469285+00:00
-- url     : https://prove2.me/theorems/7d29179e-6993-4384-a41d-f6abc8630a86
-- title:
--   Pairing Orthogonal Complement
-- statement:
--   Definitions and structural lemmas for Pairing Orthogonal Complement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/PairingOrthogonalComplement.lean

import Mathlib
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementEI
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementCS
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementNC
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementMV
import Definitions.Def_Formalism_YangianSpanCharacter_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLatticeCounting.S4
open Finset
open Formalism.SL.IwahoriBlocks (IsHerm eich)
section defs
variable {E : Type*} [CommRing E] [StarRing E] {V : Type*} [AddCommGroup V] [Module E V]
def IsLat (O : Subring E) (abelian₂ : AddSubgroup V) : Prop := ∀ a ∈ O, ∀ v ∈ abelian₂, a • v ∈ abelian₂
def Integ (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) : Prop :=
  ∀ v ∈ abelian₂, ∀ w ∈ abelian₂, h v w ∈ O
def InTh (th : E) (abelian₂ : AddSubgroup V) (v : V) : Prop := ∃ w ∈ abelian₂, v = th • w
def InThO (O : Subring E) (th : E) (c : E) : Prop := ∃ d ∈ O, c = th * d
def eichLin (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s : E) : V →ₗ[E] V where
  toFun := eich h x u s
  map_add' v w := by
    simp only [eich, map_add, LinearMap.add_apply, add_smul]; abel
  map_smul' c v := by
    simp only [eich, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add,
      smul_sub, mul_smul]
def moved (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s : E) (abelian₂ : AddSubgroup V) : AddSubgroup V :=
  abelian₂.comap (eichLin h x u s).toAddMonoidHom
def MoveTuple (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (th : E) (abelian₂ : AddSubgroup V)
    (x x' u : V) (s : E) : Prop :=
  InTh th abelian₂ (x + x') ∧ u ∈ abelian₂ ∧ s • x ∈ abelian₂ ∧ star s • x ∈ abelian₂ ∧ InThO O th (h x' x)
def IsLift (th : E) (abelian₂ : AddSubgroup V) (w la la' : V) : Prop :=
  w + la ∈ abelian₂ ∧ w + la' ∈ abelian₂ ∧ InTh th abelian₂ (la' - la)
end defs
def SpanCharRing : Prop :=
  ∀ (E V : Type) [CommRing E] [AddCommGroup V] [Module E V] (O : Subring E) (θ : Eˣ),
    (θ : E) ∈ O → ∀ (n : ℕ) (f f' : Fin n → V), LinearIndependent E (Sum.elim f f') →
    ∀ α α' : Fin n → E,
      (((θ⁻¹ : Eˣ) : E) • (∑ i, α i • f i + ∑ i, α' i • f' i) ∈
          Submodule.span O (Set.range f ∪ Set.range (fun i => ((θ⁻¹ : Eˣ) : E) • (f' i - f i))) ↔
        ∀ i, α' i ∈ O ∧ ∃ x ∈ O, α i + α' i = θ * x)
def DetKills : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (m : ℕ) (f : Fin m → V) (c : Fin m → E),
    (∀ i j, h (f i) (f j) ∈ O) → (∀ j, h (∑ i, c i • f i) (f j) ∈ O) →
    ∀ i, (Matrix.of fun a b => h (f a) (f b)).det * c i ∈ O
def UnimodSplit : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (m : ℕ) (f : Fin m → V),
    (∀ i j, h (f i) (f j) ∈ O) →
    (∃ d ∈ O, d * (Matrix.of fun a b => h (f a) (f b)).det = 1) →
    ∀ v, (∀ j, h v (f j) ∈ O) →
      ∃ c : Fin m → E, (∀ i, c i ∈ O) ∧ ∀ j, h (v - ∑ i, c i • f i) (f j) = 0
def ValuationProductBound : Prop :=
  ∀ (B : Type) [Fintype B] (s : B → ℕ) (vh ve vt : B → ℝ) (q A : ℝ) (r : ℕ),
    1 ≤ q → (∀ b, 1 ≤ s b ∧ s b ≤ r + 1) → (∀ b, 0 ≤ vh b) → (∀ b, 0 ≤ ve b) →
    (∀ b, (s b : ℝ) * vt b = ve b - vh b) → ∑ b, vh b ≤ A → ∑ b, ve b ≤ A →
    ∏ b, q ^ (2 * (s b : ℝ) * vh b) ≤ (q ^ A) ^ (2 * ((r : ℝ) + 1)) ∧
    ∏ b, q ^ (vt b * ((s b : ℝ) * ((s b : ℝ) - 1) / 2)) ≤ (q ^ A) ^ (((r : ℝ) + 1) / 2)
def TauWell : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (th : E) (r : ℕ)
    (f f' g : Fin r → V) (c c' : Fin r → E),
    IsLat O abelian₂ → Integ h O abelian₂ → (∀ j, g j ∈ abelian₂) →
    (∀ i j, h (f i) (g j) = if i = j then 1 else 0) →
    (∀ i, InTh th abelian₂ (f' i - f i)) → (∀ i, c' i ∈ O) →
    InTh th abelian₂ (∑ i, c' i • f' i - ∑ i, c i • f i) →
    ∀ i, InThO O th (c' i - c i)
def PairingOrthogonalComplement : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (th : E) (w₁ la₁ la₂ la₂' : V),
    star th = th → Integ h O abelian₂ →
    h w₁ la₂ = 0 → h w₁ la₂' = 0 → h la₁ la₂ = 0 →
    h la₁ la₂' = h (w₁ + la₁) (la₂' - la₂) ∧
    (w₁ + la₁ ∈ abelian₂ → InTh th abelian₂ (la₂' - la₂) → InThO O th (h la₁ la₂'))
def TypeBeClass : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (th : E) (x x' : V),
    star th = th → Integ h O abelian₂ → InTh th abelian₂ (x + x') →
    (∀ xi ∈ abelian₂, h xi x = 0 → h xi x' = h xi (x + x') ∧ InThO O th (h xi x')) ∧
    (∀ xi' ∈ abelian₂, h x' xi' = 0 → h x xi' = h (x + x') xi' ∧ InThO O th (h x xi'))
def ThMParts : Prop :=
  ∀ (E : Type) [CommRing E] (V : Type) [AddCommGroup V] [Module E V] (O : Subring E)
    (abelian₂ : AddSubgroup V) (θ : Eˣ), (θ : E) ∈ O → IsLat O abelian₂ →
    ∀ (n : ℕ) (f f' : Fin n → V), LinearIndependent E (Sum.elim f f') →
    (∀ i, f i ∈ abelian₂) → (∀ i, f' i ∈ abelian₂) →
    ∀ α α' : Fin n → E,
      ((θ⁻¹ : Eˣ) : E) • ((∑ i, α i • f i) + (∑ i, α' i • f' i)) ∈
          Submodule.span O (Set.range f ∪ Set.range (fun i => ((θ⁻¹ : Eˣ) : E) • (f' i - f i))) →
      (∀ i, α i ∈ O ∧ α' i ∈ O) ∧ (∑ i, α i • f i) ∈ abelian₂ ∧ (∑ i, α' i • f' i) ∈ abelian₂
def TauLin : Prop :=
  ∀ (E : Type) [CommRing E] (V : Type) [AddCommGroup V] [Module E V] (O : Subring E)
    (abelian₂ : AddSubgroup V) (th c : E) (w₁ w₂ la₁ la₁' la₂ la₂' : V),
    IsLat O abelian₂ → c ∈ O → IsLift th abelian₂ w₁ la₁ la₁' → IsLift th abelian₂ w₂ la₂ la₂' →
    IsLift th abelian₂ (c • w₁ + w₂) (c • la₁ + la₂) (c • la₁' + la₂')
def TauHom : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (θ : Eˣ) (r : ℕ)
    (f f' g g' : Fin r → V) (a₁ a₁' a₂ a₂' a₃ a₃' : Fin r → E) (w₁ w₂ : V) (c : E),
    IsLat O abelian₂ → Integ h O abelian₂ → (∀ j, g j ∈ abelian₂) → (∀ j, g' j ∈ abelian₂) →
    (∀ i j, h (f i) (g j) = if i = j then 1 else 0) →
    (∀ i j, h (f' i) (g' j) = if i = j then 1 else 0) →
    (∀ i, InTh (θ : E) abelian₂ (f' i - f i)) → c ∈ O →
    IsLift (θ : E) abelian₂ w₁ (∑ i, a₁ i • f i) (∑ i, a₁' i • f' i) →
    IsLift (θ : E) abelian₂ w₂ (∑ i, a₂ i • f i) (∑ i, a₂' i • f' i) →
    IsLift (θ : E) abelian₂ (c • w₁ + w₂) (∑ i, a₃ i • f i) (∑ i, a₃' i • f' i) →
    ((θ⁻¹ : Eˣ) : E) • (((∑ i, a₃' i • f' i) - (∑ i, a₃ i • f i))
        - c • ((∑ i, a₁' i • f' i) - (∑ i, a₁ i • f i)) - ((∑ i, a₂' i • f' i) - (∑ i, a₂ i • f i))) ∈
      Submodule.span O (Set.range f ∪ Set.range (fun i => ((θ⁻¹ : Eˣ) : E) • (f' i - f i)))
def TauKer : Prop :=
  ∀ (E : Type) [CommRing E] (V : Type) [AddCommGroup V] [Module E V] (O : Subring E)
    (abelian₂ : AddSubgroup V) (θ : Eˣ), (θ : E) ∈ O → IsLat O abelian₂ →
    ∀ (n : ℕ) (f f' : Fin n → V), LinearIndependent E (Sum.elim f f') → (∀ i, f' i ∈ abelian₂) →
    ∀ (a a' : Fin n → E) (w : V),
      (w + (∑ i, a' i • f' i) ∈ abelian₂ →
        ((θ⁻¹ : Eˣ) : E) • ((∑ i, a' i • f' i) - (∑ i, a i • f i)) ∈
          Submodule.span O (Set.range f ∪ Set.range (fun i => ((θ⁻¹ : Eˣ) : E) • (f' i - f i))) →
        w ∈ abelian₂) ∧
      (w ∈ abelian₂ → IsLift (θ : E) abelian₂ w 0 0)
def TupleJac : Prop :=
  ∀ (E : Type) [CommRing E] (n m : ℕ) (A : Matrix (Fin m) (Fin m) E),
    LinearMap.det ({ toFun := fun X : Matrix (Fin n) (Fin m) E => X * A
                     map_add' := fun X Y => Matrix.add_mul X Y A
                     map_smul' := fun c X => Matrix.smul_mul c X A } :
        Matrix (Fin n) (Fin m) E →ₗ[E] Matrix (Fin n) (Fin m) E) = A.det ^ n
section herm
variable (F E : Type*) [Field F] [CommRing E] [Algebra F E] [StarRing E]
def hermSub (hs : ∀ c : F, star (algebraMap F E c) = algebraMap F E c) (m : ℕ) :
    Submodule F (Matrix (Fin m) (Fin m) E) where
  carrier := {X | X.conjTranspose = X}
  add_mem' := by
    intro a b ha hb
    change (a + b).conjTranspose = a + b
    have ha' : a.conjTranspose = a := ha
    have hb' : b.conjTranspose = b := hb
    rw [Matrix.conjTranspose_add, ha', hb']
  zero_mem' := Matrix.conjTranspose_zero
  smul_mem' := by
    intro c X hX
    change (c • X).conjTranspose = c • X
    have hX' : X.conjTranspose = X := hX
    ext i j
    have h1 : star (X j i) = X i j := by
      have := congrFun (congrFun hX' i) j
      simpa [Matrix.conjTranspose_apply] using this
    rw [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, Algebra.smul_def,
      Algebra.smul_def, star_mul', hs, h1]
def congrAll (m : ℕ) (A : Matrix (Fin m) (Fin m) E) :
    Matrix (Fin m) (Fin m) E →ₗ[F] Matrix (Fin m) (Fin m) E where
  toFun X := A.conjTranspose * X * A
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
def congrHerm (hs : ∀ c : F, star (algebraMap F E c) = algebraMap F E c) (m : ℕ)
    (A : Matrix (Fin m) (Fin m) E) : hermSub F E hs m →ₗ[F] hermSub F E hs m :=
  (congrAll F E m A).restrict (by
    intro X hX
    change (A.conjTranspose * X * A).conjTranspose = A.conjTranspose * X * A
    have hX' : X.conjTranspose = X := hX
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hX',
      Matrix.mul_assoc])
end herm
def HermJac : Prop :=
  ∀ (F E : Type) [Field F] [CommRing E] [Algebra F E] [StarRing E]
    (hs : ∀ c : F, star (algebraMap F E c) = algebraMap F E c),
    Module.finrank F E = 2 → (∀ y : E, star y = y → ∃ c : F, algebraMap F E c = y) →
    ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) E),
      LinearMap.det (congrHerm F E hs m A) = Algebra.norm F A.det ^ m
def PrimDensityInert : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (n m : ℕ) (Gm : Matrix (Fin m) (Fin m) L), 2 * m + 3 ≤ n →
      (∀ i j, Gm j i = Gm i j ^ Fintype.card K) →
      (Fintype.card K : ℝ) ^ (2 * n * m) / (Fintype.card K : ℝ) ^ (m ^ 2) / 2
        ≤ ({X : Fin m → Fin n → L | LinearIndependent L X ∧
              ∀ i j, ∑ k, X i k * X j k ^ Fintype.card K = Gm i j}.ncard : ℝ) ∧
      ({X : Fin m → Fin n → L | LinearIndependent L X ∧
              ∀ i j, ∑ k, X i k * X j k ^ Fintype.card K = Gm i j}.ncard : ℝ)
        ≤ 2 * ((Fintype.card K : ℝ) ^ (2 * n * m) / (Fintype.card K : ℝ) ^ (m ^ 2))
def PrimDensitySplit : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (n m : ℕ) (Gm : Matrix (Fin m) (Fin m) K), 2 * m + 3 ≤ n →
      (Fintype.card K : ℝ) ^ (2 * n * m) / (Fintype.card K : ℝ) ^ (m ^ 2) / 2
        ≤ ({XY : (Fin m → Fin n → K) × (Fin m → Fin n → K) | LinearIndependent K XY.1 ∧
              LinearIndependent K XY.2 ∧ ∀ i j, ∑ k, XY.1 i k * XY.2 j k = Gm i j}.ncard : ℝ) ∧
      ({XY : (Fin m → Fin n → K) × (Fin m → Fin n → K) | LinearIndependent K XY.1 ∧
              LinearIndependent K XY.2 ∧ ∀ i j, ∑ k, XY.1 i k * XY.2 j k = Gm i j}.ncard : ℝ)
        ≤ 2 * ((Fintype.card K : ℝ) ^ (2 * n * m) / (Fintype.card K : ℝ) ^ (m ^ 2))
def HermStdForm : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (n : ℕ) (Ph : Matrix (Fin n) (Fin n) L), IsUnit Ph.det →
      (∀ k l, Ph l k = Ph k l ^ Fintype.card K) →
      ∃ A : Matrix (Fin n) (Fin n) L, IsUnit A.det ∧
        A * Ph * (A.map fun y => y ^ Fintype.card K).transpose = 1
def PrimDensityInertForm : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (n m : ℕ) (Ph : Matrix (Fin n) (Fin n) L) (Gm : Matrix (Fin m) (Fin m) L), 2 * m + 3 ≤ n →
      IsUnit Ph.det → (∀ k l, Ph l k = Ph k l ^ Fintype.card K) →
      (∀ i j, Gm j i = Gm i j ^ Fintype.card K) →
      (Fintype.card K : ℝ) ^ (2 * n * m) / (Fintype.card K : ℝ) ^ (m ^ 2) / 2
        ≤ ({X : Fin m → Fin n → L | LinearIndependent L X ∧
              ∀ i j, ∑ k, ∑ l, X i k * Ph k l * X j l ^ Fintype.card K = Gm i j}.ncard : ℝ) ∧
      ({X : Fin m → Fin n → L | LinearIndependent L X ∧
              ∀ i j, ∑ k, ∑ l, X i k * Ph k l * X j l ^ Fintype.card K = Gm i j}.ncard : ℝ)
        ≤ 2 * ((Fintype.card K : ℝ) ^ (2 * n * m) / (Fintype.card K : ℝ) ^ (m ^ 2))
def PrimDensitySplitForm : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (n m : ℕ) (Ph : Matrix (Fin n) (Fin n) K)
    (Gm : Matrix (Fin m) (Fin m) K), 2 * m + 3 ≤ n → IsUnit Ph.det →
      (Fintype.card K : ℝ) ^ (2 * n * m) / (Fintype.card K : ℝ) ^ (m ^ 2) / 2
        ≤ ({XY : (Fin m → Fin n → K) × (Fin m → Fin n → K) | LinearIndependent K XY.1 ∧
              LinearIndependent K XY.2 ∧
              ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph k l * XY.2 j l = Gm i j}.ncard : ℝ) ∧
      ({XY : (Fin m → Fin n → K) × (Fin m → Fin n → K) | LinearIndependent K XY.1 ∧
              LinearIndependent K XY.2 ∧
              ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph k l * XY.2 j l = Gm i j}.ncard : ℝ)
        ≤ 2 * ((Fintype.card K : ℝ) ^ (2 * n * m) / (Fintype.card K : ℝ) ^ (m ^ 2))
def OverlatticeCount : Prop :=
  ∀ (O A : Type) [CommRing O] [AddCommGroup A] [Module O A] [Finite A] (m : ℕ),
    (∀ N : Submodule O A, ∃ s : Fin m → A, Submodule.span O (Set.range s) = N) →
    Nat.card (Submodule O A) ≤ Nat.card A ^ m
def LocalDensityShareBound : Prop :=
  ∀ (Ov : Type) [Fintype Ov] (dens dl : Ov → ℝ) (κ be disc tot : ℝ) (k r : ℕ),
    1 ≤ k → 0 ≤ κ → 1 ≤ be → (Fintype.card Ov : ℝ) ≤ disc ^ (2 * r + 2) →
    (∀ M, dens M = κ * ((be ^ (k + 2 * r + 1))⁻¹ / (be ^ (2 * r + 2))⁻¹) * dl M) →
    (∀ M, dl M ≤ 2) → κ / 2 ≤ tot →
    ∑ M, dens M ≤ 4 * disc ^ (2 * r + 2) * (be ^ (k - 1))⁻¹ * tot
def HomCount : Prop :=
  ∀ (O I : Type) [CommRing O] [AddCommGroup I] [Module O I] [Finite I] (n : ℕ),
    Nat.card ((Fin n → O) →ₗ[O] I) = Nat.card I ^ n
def ProperIndex : Prop :=
  ∀ (O B : Type) [CommRing O] [AddCommGroup B] [Module O B] [Finite B] (q : ℕ),
    (∀ P : Ideal O, P.IsMaximal → q ≤ Nat.card (O ⧸ P)) →
    ∀ I : Submodule O B, I ≠ ⊤ → q * Nat.card I ≤ Nat.card B
structure Unram (o O : Type*) [CommRing o] [CommRing O] [StarRing O] [Algebra o O] : Prop where
  star_o : ∀ c : o, star (algebraMap o O c) = algebraMap o O c
  free : Module.Free o O
  rank2 : Module.finrank o O = 2
  tr_onto : ∀ c : o, ∃ s : O, s + star s = algebraMap o O c
  tr_perfect : ∀ φ : O →ₗ[o] o, ∃ b : O, ∀ a : O,
    algebraMap o O (φ a) = a * star b + star (a * star b)
def SelfDual {O abelian₂ : Type*} [CommRing O] [StarRing O] [AddCommGroup abelian₂] [Module O abelian₂]
    (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O) : Prop :=
  IsHerm h ∧ ∀ φ : abelian₂ →ₗ[O] O, ∃ w, ∀ v, φ v = h v w
def Satur (o : Type*) {O abelian₂ : Type*} [CommRing o] [CommRing O] [Algebra o O] [AddCommGroup abelian₂]
    [Module O abelian₂] (S : Submodule O abelian₂) : Prop :=
  ∀ (c : o) (v : abelian₂), c ≠ 0 → algebraMap o O c • v ∈ S → v ∈ S
def DualCap : Prop :=
  ∀ (o O abelian₂ : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
    [Algebra o O] [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂] [Module.Finite O abelian₂]
    (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O), Unram o O → SelfDual h →
    ∀ S : Submodule O abelian₂, Satur o S → ∀ φ : S →ₗ[O] O, ∃ w : abelian₂, ∀ v : S, φ v = h v w
def UnimodHull : Prop :=
  ∀ (o O abelian₂ : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
    [Algebra o O] [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂] [Module.Finite O abelian₂]
    (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O), Unram o O → SelfDual h →
    ∀ (S : Submodule O abelian₂) (m₀ : ℕ), Satur o S → Module.Free O S → Module.finrank O S = m₀ →
    ∃ T : Submodule O abelian₂, S ≤ T ∧ Module.Free O T ∧ Module.finrank O T ≤ 2 * m₀ ∧
      (∀ v, ∃ t ∈ T, ∀ t' ∈ T, h (v - t) t' = 0) ∧ (∀ t ∈ T, (∀ t' ∈ T, h t t' = 0) → t = 0) ∧
      ∃ U₀ : Submodule O abelian₂, Module.Free O U₀ ∧
        Module.finrank O T + Module.finrank O U₀ = Module.finrank O abelian₂ ∧
        (∀ t ∈ T, ∀ u ∈ U₀, h t u = 0) ∧ (∀ v, ∃ t ∈ T, ∃ u ∈ U₀, v = t + u) ∧
        (∀ φ : U₀ →ₗ[O] O, ∃ w ∈ U₀, ∀ v : U₀, φ v = h v w)
def UnimodRank : Prop :=
  ∀ (o O abelian₂ : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
    [Algebra o O] [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂] [Module.Finite O abelian₂]
    (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O), Unram o O → SelfDual h →
    ∀ ρ : ℕ, ρ ≤ Module.finrank O abelian₂ →
    ∃ U₀ : Submodule O abelian₂, Module.Free O U₀ ∧ Module.finrank O U₀ = ρ ∧
      (∀ v, ∃ u ∈ U₀, ∀ u' ∈ U₀, h (v - u) u' = 0) ∧
      (∀ φ : U₀ →ₗ[O] O, ∃ w ∈ U₀, ∀ v : U₀, φ v = h v w)
structure LatModel {E V : Type*} [CommRing E] [StarRing E] [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V)
    {O' Lam' : Type*} [CommRing O'] [StarRing O'] [AddCommGroup Lam'] [Module O' Lam']
    (h' : Lam' →ₗ[O'] Lam' →ₗ⋆[O'] O') (io : O' →+* E) (j : Lam' →+ V) : Prop where
  io_inj : Function.Injective io
  io_range : ∀ c, c ∈ O ↔ ∃ a, io a = c
  io_star : ∀ a, io (star a) = star (io a)
  j_inj : Function.Injective j
  j_range : ∀ v, v ∈ abelian₂ ↔ ∃ w, j w = v
  j_smul : ∀ a w, j (a • w) = io a • j w
  form : ∀ v w, h (j v) (j w) = io (h' v w)
def BridgeExists : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V),
    (∀ c ∈ O, star c ∈ O) → IsLat O abelian₂ → Integ h O abelian₂ →
    ∃ (O' : Type) (_ : CommRing O') (_ : StarRing O') (Lam' : Type) (_ : AddCommGroup Lam')
      (_ : Module O' Lam') (h' : Lam' →ₗ[O'] Lam' →ₗ⋆[O'] O') (io : O' →+* E) (j : Lam' →+ V),
      LatModel h O abelian₂ h' io j
def BridgeSelfDual : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] [Nontrivial E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V)
    (O' Lam' : Type) [CommRing O'] [StarRing O'] [AddCommGroup Lam'] [Module O' Lam']
    (h' : Lam' →ₗ[O'] Lam' →ₗ⋆[O'] O') (io : O' →+* E) (j : Lam' →+ V),
    LatModel h O abelian₂ h' io j → IsHerm h →
    ∀ (n : ℕ) (b : Module.Basis (Fin n) E V), (∀ v, v ∈ abelian₂ ↔ ∀ i, b.repr v i ∈ O) →
    (∀ Φ : V →ₗ[E] E, ∃ v, ∀ x, Φ x = h x v) →
    (∀ v, (∀ w ∈ abelian₂, h w v ∈ O) → v ∈ abelian₂) →
    SelfDual h' ∧ Module.Free O' Lam' ∧ Module.Finite O' Lam' ∧ Module.finrank O' Lam' = n
def DualCapV : Prop :=
  ∀ (o O' Lam' : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O'] [StarRing O']
    [Algebra o O'] [AddCommGroup Lam'] [Module O' Lam'] [Module.Free O' Lam'] [Module.Finite O' Lam']
    (h' : Lam' →ₗ[O'] Lam' →ₗ⋆[O'] O')
    (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (io : O' →+* E) (j : Lam' →+ V),
    Unram o O' → SelfDual h' → LatModel h O abelian₂ h' io j →
    (∀ c : o, c ≠ 0 → IsUnit (io (algebraMap o O' c))) →
    (∀ v : V, ∃ c : o, c ≠ 0 ∧ io (algebraMap o O' c) • v ∈ abelian₂) →
    ∀ (Z : Submodule E V) (y : V), (∀ w ∈ abelian₂, w ∈ Z → h w y ∈ O) →
      ∃ l ∈ abelian₂, ∀ w ∈ Z, h w (y - l) = 0
def MoveCong : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (th : E) (x x' u : V) (s : E),
    IsHerm h → star th = th → IsLat O abelian₂ → Integ h O abelian₂ →
    u ∈ abelian₂ → s • x ∈ abelian₂ → InTh th abelian₂ (x + x') → InThO O th (h x' x) →
    h u x = 0 → h u x' = 0 →
    ∀ v ∈ abelian₂, h v x' = 0 →
      h v x = h v (x + x') ∧ InThO O th (h v x) ∧ InThO O th (h v x + h v u * h x' x) ∧
      InTh th abelian₂ (eich h x u s (eich h x' u s v) - v)
def MoveInvol : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (th : E) (x x' u : V) (s : E),
    IsHerm h → IsLat O abelian₂ → Integ h O abelian₂ →
    h x x = 0 → h u x = 0 → h u x' = 0 → s + star s = h u u →
    MoveTuple h O th abelian₂ x x' u s →
      MoveTuple h O th (moved h x u s abelian₂) x x' (-u) (star s) ∧
      IsLat O (moved h x u s abelian₂) ∧ Integ h O (moved h x u s abelian₂) ∧
      moved h x (-u) (star s) (moved h x u s abelian₂) = abelian₂ ∧ -(-u) = u ∧ star (star s) = s
def MovePerp : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (th : E) (x x' u : V) (s : E),
    IsHerm h → th ∈ O → IsLat O abelian₂ → Integ h O abelian₂ →
    h x x = 0 → h x' x' = 0 → h u x = 0 → h u x' = 0 → s + star s = h u u →
    MoveTuple h O th abelian₂ x x' u s →
      eich h x' u s '' {v | v ∈ abelian₂ ∧ h v x' = 0} = {v | v ∈ moved h x u s abelian₂ ∧ h v x' = 0}
def MovePerpX : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (th : E) (x x' u : V) (s : E)
    (r : ℕ) (e : Fin r → V) (c : Fin r → E),
    IsHerm h → th ∈ O → IsLat O abelian₂ → Integ h O abelian₂ →
    (∀ i k, h (e i) (e k) = 0) → x' = ∑ i, c i • e i →
    h x x = 0 → h u x = 0 → h u x' = 0 → s + star s = h u u →
    MoveTuple h O th abelian₂ x x' u s →
      eich h x' u s '' {v | v ∈ abelian₂ ∧ ∀ i, h v (e i) = 0}
        = {v | v ∈ moved h x u s abelian₂ ∧ ∀ i, h v (e i) = 0}
def MoveAdm : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (th : E) (x x' u f f' : V) (s : E),
    IsHerm h → star th = th → IsLat O abelian₂ → Integ h O abelian₂ →
    u ∈ abelian₂ → s • x ∈ abelian₂ → InTh th abelian₂ (x + x') → InThO O th (h x' x) →
    h x x = 0 → h u x = 0 → h u x' = 0 → s + star s = h u u →
    f' ∈ abelian₂ → h f' x' = 0 → InTh th abelian₂ (f' - f) →
      eich h x u s (eich h x' u s f' - eich h x (-u) (star s) f)
        = eich h x u s (eich h x' u s f') - f ∧
      InTh th abelian₂ (eich h x u s (eich h x' u s f') - f) ∧
      InTh th (moved h x u s abelian₂) (eich h x' u s f' - eich h x (-u) (star s) f)
def IsoComplement : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (r : ℕ) (e y : Fin r → V),
    IsHerm h → (∀ c ∈ O, star c = c → ∃ s ∈ O, s + star s = c) → Integ h O abelian₂ →
    (∀ i j, h (e i) (e j) = 0) → (∀ j, y j ∈ abelian₂) →
    (∀ i j, h (y j) (e i) = if i = j then 1 else 0) →
    ∃ c : Fin r → Fin r → E, (∀ j l, c j l ∈ O) ∧
      ∀ j k, h (y j - ∑ l, c j l • e l) (y k - ∑ l, c k l • e l) = 0
def SameTrace : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (La Lb : AddSubgroup V) (r : ℕ) (e y yb : Fin r → V),
    IsHerm h → (∀ c ∈ O, star c = c → ∃ s ∈ O, s + star s = c) →
    IsLat O La → IsLat O Lb → Integ h O La → Integ h O Lb →
    (∀ i j, h (e i) (e j) = 0) → (∀ i, e i ∈ La) →
    (∀ v, (∀ i, h v (e i) = 0) → (v ∈ La ↔ v ∈ Lb)) →
    (∀ j, y j ∈ La) → (∀ j, yb j ∈ Lb) →
    (∀ i j, h (y j) (e i) = if i = j then 1 else 0) →
    (∀ i j, h (yb j) (e i) = if i = j then 1 else 0) →
    (∀ d, (∀ i, h d (e i) = 0) → (∀ v ∈ La, (∀ i, h v (e i) = 0) → h v d ∈ O) →
      ∃ l ∈ La, (∀ i, h l (e i) = 0) ∧ ∃ c : Fin r → E, d = l + ∑ i, c i • e i) →
    ∃ n : V ≃ₗ[E] V, (∀ v w, h (n v) (n w) = h v w) ∧ (∀ v, (∀ i, h v (e i) = 0) → n v = v) ∧
      ∀ v, v ∈ La ↔ n v ∈ Lb
def SameTraceHyp : Prop :=
  ∀ (o O' Lam' : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O'] [StarRing O']
    [Algebra o O'] [AddCommGroup Lam'] [Module O' Lam'] [Module.Free O' Lam'] [Module.Finite O' Lam']
    (h' : Lam' →ₗ[O'] Lam' →ₗ⋆[O'] O')
    (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (io : O' →+* E) (j : Lam' →+ V),
    Unram o O' → SelfDual h' → LatModel h O abelian₂ h' io j → IsHerm h →
    (∀ c : o, c ≠ 0 → IsUnit (io (algebraMap o O' c))) →
    (∀ v : V, ∃ c : o, c ≠ 0 ∧ io (algebraMap o O' c) • v ∈ abelian₂) →
    ∀ (r : ℕ) (e : Fin r → V), (∀ i k, h (e i) (e k) = 0) → (∀ i, e i ∈ abelian₂) →
    LinearIndependent E e → (∀ c : Fin r → E, (∑ i, c i • e i) ∈ abelian₂ → ∀ i, c i ∈ O) →
    (∃ y : Fin r → V, (∀ k, y k ∈ abelian₂) ∧ ∀ i k, h (y k) (e i) = if i = k then 1 else 0) ∧
    (∀ d, (∀ i, h d (e i) = 0) → (∀ v ∈ abelian₂, (∀ i, h v (e i) = 0) → h v d ∈ O) →
      ∃ l ∈ abelian₂, (∀ i, h l (e i) = 0) ∧ ∃ c : Fin r → E, d = l + ∑ i, c i • e i)
def SuperDiagAdd : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R),
    (∀ i j, j < i → A i j = 0) → (∀ i, A i i = 1) → (∀ i j, j < i → B i j = 0) → (∀ i, B i i = 1) →
    ∀ j : Fin n, (A * B) j.castSucc j.succ = A j.castSucc j.succ + B j.castSucc j.succ
def MoveWeight : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (r : ℕ) (f : Fin (r + 1) → V) (co : Fin (r + 1) → V →ₗ[E] E)
    (al : Fin (r + 1) → E) (u : V) (s : E) (J : Fin r),
    (∀ i k, co k (f i) = if i = k then 1 else 0) →
    (∀ k : Fin (r + 1), J.val < k.val → al k = 0) →
    (∀ i k : Fin (r + 1), k.val ≤ J.val → h (f i) (f k) = 0) →
    (∀ k : Fin (r + 1), k.val ≤ J.val → h (f k) u = 0) →
    ∑ j : Fin r, co j.castSucc (eich h (∑ i, al i • f i) u s (f j.succ))
      = al J.castSucc * h (f J.succ) u
def MoveY : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (th : E) (x u y y' : V) (s : E),
    IsLat O abelian₂ → u ∈ abelian₂ → s • x ∈ abelian₂ →
    h y u = 0 → h y x = 0 → h y' u = 0 →
    eich h x u s (y + y') = y + y' - h y' x • (u + s • x) ∧
    (InTh th abelian₂ (y + y') → InThO O th (h y' x) → InTh th abelian₂ (eich h x u s (y + y'))) ∧
    (IsUnit th → InThO O th (h y' x) → ∀ w ∈ abelian₂, th • w = y + y' → w ∈ moved h x u s abelian₂)
def LeakAlg : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (th : E) (x x' u y v : V) (s : E),
    IsHerm h → IsLat O abelian₂ → u ∈ abelian₂ → s • x ∈ abelian₂ → h u x = 0 → h u x' = 0 → h v x' = 0 →
    y + eich h x u s (eich h x' u s v)
      = (y + h v u • x) + (v + h v u • x') - (h v x + h v u * h x' x) • (u + s • x) ∧
    (InTh th abelian₂ (y + eich h x u s (eich h x' u s v)) → InThO O th (h v x + h v u * h x' x) →
      InTh th abelian₂ ((y + h v u • x) + (v + h v u • x'))) ∧
    (h v x + h v u * h x' x) • u
      = (y + v + h v u • (x + x') - ((h v x + h v u * h x' x) * s) • x)
        - (y + eich h x u s (eich h x' u s v))
def LeakBack : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (x x' u y v y' m' : V) (s c : E),
    Integ h O abelian₂ → u ∈ abelian₂ → m' ∈ abelian₂ → h x' u = 0 → h y' u = 0 →
    (v + c • x' = y' + m' → h v u = h m' u ∧ h v u ∈ O) ∧
    (y + c • x) + eich h x u s (eich h x' u s (v + c • x')) - c • (x + eich h x u s (eich h x' u s x'))
      = y + eich h x u s (eich h x' u s v)
def PrimCancel : Prop :=
  ∀ (E : Type) [CommRing E] (O : Subring E) (th ka : E) (n : ℕ) (c d : Fin n → E),
    (∀ i, d i ∈ O) → ∑ i, d i * c i = 1 → (∀ i, ∃ t ∈ O, ka * c i = th * t) → ∃ t ∈ O, ka = th * t
def HermGaussRing : Prop :=
  ∀ (S : Type) [CommRing S] [Fintype S] [StarRing S] (n : ℕ) (Gm : Matrix (Fin n) (Fin n) S)
    (ψ : AddChar S ℂ) (φ : (Fin n → S) → ℂ),
    IsUnit Gm.det → (∀ u, ‖φ u‖ = 1) →
    (∀ u d, φ (u + d) = φ u * φ d * ψ (∑ i, ∑ j, u i * Gm i j * star (d j))) →
    ‖∑ u, φ u‖ ^ 2
      ≤ (Fintype.card S : ℝ) ^ n * (Nat.card {y : S // ∀ c, ψ (c * y) = 1} : ℝ) ^ n
def AnnihSize : Prop :=
  ∀ (o O S : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
    [Algebra o O] [CommRing S] (ϖ : o) (pr : O →+* S) (τ : AddChar o ℂ) (ψ : AddChar S ℂ) (q N i : ℕ),
    Unram o O → Irreducible ϖ → Nat.card (IsLocalRing.ResidueField o) = q → 2 ≤ q →
    Function.Surjective pr → (∀ y, pr y = 0 ↔ ∃ z, y = algebraMap o O (ϖ ^ N) * z) →
    i ≤ N → (∀ j, i ≤ j ↔ ∀ x, τ (ϖ ^ j * x) = 1) →
    (∀ (y : O) (t : o), algebraMap o O t = y + star y → ψ (pr y) = τ t) →
    Nat.card S = q ^ (2 * N) ∧ Nat.card {y : S // ∀ c, ψ (c * y) = 1} = q ^ (2 * (N - i))
def HermGaussCond : Prop :=
  ∀ (o O S : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
    [Algebra o O] [CommRing S] [Fintype S] [StarRing S] (ϖ : o) (pr : O →+* S) (τ : AddChar o ℂ)
    (ψ : AddChar S ℂ) (q N i n : ℕ) (Gm : Matrix (Fin n) (Fin n) S) (φ : (Fin n → S) → ℂ),
    Unram o O → Irreducible ϖ → Nat.card (IsLocalRing.ResidueField o) = q → 2 ≤ q →
    Function.Surjective pr → (∀ y, pr y = 0 ↔ ∃ z, y = algebraMap o O (ϖ ^ N) * z) →
    (∀ y, pr (star y) = star (pr y)) →
    i ≤ N → (∀ j, i ≤ j ↔ ∀ x, τ (ϖ ^ j * x) = 1) →
    (∀ (y : O) (t : o), algebraMap o O t = y + star y → ψ (pr y) = τ t) →
    IsUnit Gm.det → (∀ u, ‖φ u‖ = 1) →
    (∀ u d, φ (u + d) = φ u * φ d * ψ (∑ k, ∑ l, u k * Gm k l * star (d l))) →
    ‖∑ u, φ u‖ ≤ ((q : ℝ) ^ (i * n))⁻¹ * (Fintype.card S : ℝ) ^ n
def GaussSummand : Prop :=
  ∀ (U₀ U₁ : Type) [Fintype U₀] [Fintype U₁] (φ₀ : U₀ → ℂ) (φ₁ : U₁ → ℂ),
    (∀ u, ‖φ₁ u‖ ≤ 1) →
    ‖∑ u : U₀ × U₁, φ₀ u.1 * φ₁ u.2‖ ≤ ‖∑ u, φ₀ u‖ * (Fintype.card U₁ : ℝ)
def CondCount : Prop :=
  ∀ (o T : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [AddCommGroup T] [Fintype T]
    [DecidableEq T] (ϖ : o) (red : o →+ T) (cond : AddChar T ℂ → ℕ) (q a : ℕ),
    Irreducible ϖ → Nat.card (IsLocalRing.ResidueField o) = q → 2 ≤ q →
    Function.Surjective red → (∀ x, red x = 0 ↔ ϖ ^ a ∣ x) →
    (∀ ψ i, cond ψ ≤ i ↔ ∀ x, ψ (red (ϖ ^ i * x)) = 1) →
    Fintype.card T = q ^ a ∧ (∀ ψ, cond ψ = 0 ↔ ψ = 0) ∧ (∀ ψ, cond ψ ≤ a) ∧
    (∀ i, ((univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card : ℝ) ≤ (q : ℝ) ^ i) ∧
    (∀ i, 1 ≤ i → ((univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card : ℝ) < (q : ℝ) ^ i)
def GaussShare : Prop :=
  ∃ C : ℝ, ∀ (U T : Type) [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (χ : U → ℂ) (cond : AddChar T ℂ → ℕ) (q a ρ : ℕ),
    2 ≤ q → 4 ≤ ρ → Fintype.card T = q ^ a →
    (∀ ψ, cond ψ = 0 ↔ ψ = 0) →
    (∀ i, 1 ≤ i → ((univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card : ℝ) ≤ (q : ℝ) ^ i) →
    ∑ u, χ u = 0 →
    (∀ ψ : AddChar T ℂ, ψ ≠ 0 →
      ‖∑ u, ψ (Q u) * χ u‖ ≤ ((q : ℝ) ^ (cond ψ * ρ))⁻¹ * (Fintype.card U : ℝ)) →
    (∀ ψ : AddChar T ℂ, ψ ≠ 0 →
      ‖∑ u, ψ (Q u)‖ ≤ ((q : ℝ) ^ (cond ψ * ρ))⁻¹ * (Fintype.card U : ℝ)) →
    |((univ.filter fun u => Q u = 0).card : ℝ) - (Fintype.card U : ℝ) / (q : ℝ) ^ a|
        ≤ C * (q : ℝ) ^ (1 - (ρ : ℤ)) * ((Fintype.card U : ℝ) / (q : ℝ) ^ a) ∧
    ‖∑ u ∈ univ.filter (fun u => Q u = 0), χ u‖
        ≤ C * (q : ℝ) ^ (1 - (ρ : ℤ)) * ((univ.filter fun u => Q u = 0).card : ℝ)
def LeakProb : Prop :=
  ∀ (S : Type) [CommRing S] [Finite S] (P : Ideal S) (n : ℕ),
    Nat.card {u : Fin n → S // ∀ k, u k ∈ P} * Nat.card (S ⧸ P) ^ n = Nat.card S ^ n
def LeakShare : Prop :=
  ∃ C : ℝ, ∀ (U T : Type) [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (cond : AddChar T ℂ → ℕ) (q a ρ j : ℕ),
    2 ≤ q → 4 ≤ ρ → Fintype.card T = q ^ a →
    (∀ i, ((univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card : ℝ) ≤ (q : ℝ) ^ i) →
    (∀ ψ : AddChar T ℂ,
      ‖∑ u, ψ (Q u)‖ ≤ ((q : ℝ) ^ ((cond ψ - j) * ρ))⁻¹ * (Fintype.card U : ℝ)) →
    ((univ.filter fun u => Q u = 0).card : ℝ) ≤ C * (q : ℝ) ^ j * ((Fintype.card U : ℝ) / (q : ℝ) ^ a)
def RowSums : Prop :=
  ∀ C₁ C₂ : ℝ, ∃ C : ℝ, ∀ (B U Pl X Mv : Type) [Fintype B] [Fintype U] [Fintype Pl] [Fintype X]
    [Fintype Mv] [DecidableEq B] [DecidableEq U] [DecidableEq X]
    (vol : B → ℝ) (Z : Finset U) (UP : Pl → Finset U) (jj : Pl → ℕ) (χ : B → U → ℂ)
    (bb : Mv → B) (uu : Mv → U) (tgt : Mv → Option X) (μ : Mv → ℝ) (ω : X → ℂ) (ω₀ : ℂ) (q a ρ : ℕ),
    2 ≤ q → 4 ≤ ρ → Fintype.card Pl ≤ 2 → (∀ P, 1 ≤ jj P) → 0 < Fintype.card U →
    (∀ b, 0 ≤ vol b) → 0 < ∑ b, vol b → (∀ m, 0 ≤ μ m) →
    (∀ b u, ∑ m ∈ univ.filter (fun m => bb m = b ∧ uu m = u), μ m
      = if u ∈ Z then vol b / ((∑ b', vol b') * ((Fintype.card U : ℝ) / (q : ℝ) ^ a)) else 0) →
    |(Z.card : ℝ) - (Fintype.card U : ℝ) / (q : ℝ) ^ a|
        ≤ C₁ * (q : ℝ) ^ (1 - (ρ : ℤ)) * ((Fintype.card U : ℝ) / (q : ℝ) ^ a) →
    (∀ b, ‖∑ u ∈ Z, χ b u‖ ≤ C₁ * (q : ℝ) ^ (1 - (ρ : ℤ)) * (Z.card : ℝ)) →
    (∀ b u, ‖χ b u‖ = 1) →
    (∀ P, ((UP P).card : ℝ) = (Fintype.card U : ℝ) / (q : ℝ) ^ (jj P * ρ)) →
    (∀ P, ((Z ∩ UP P).card : ℝ) ≤ C₂ * (q : ℝ) ^ jj P * (((UP P).card : ℝ) / (q : ℝ) ^ a)) →
    (∀ m, tgt m = none → ∃ P, uu m ∈ UP P) →
    (∀ m x, tgt m = some x → ω x = ω₀ * χ (bb m) (uu m)) →
    |(∑ x, ∑ m ∈ univ.filter (fun m => tgt m = some x), μ m) - 1| ≤ C * (q : ℝ) ^ (1 - (ρ : ℤ)) ∧
    ‖∑ x, ((∑ m ∈ univ.filter (fun m => tgt m = some x), μ m : ℝ) : ℂ) * ω x‖
        ≤ C * (q : ℝ) ^ (1 - (ρ : ℤ)) * ‖ω₀‖
def UnfoldSym : Prop :=
  ∀ (G X : Type) [Group G] [MulAction G X] (μ : X → ℝ) (m : X → X → ℝ),
    (∀ (g : G) x, μ (g • x) = μ x) →
    (∀ x y, μ x * ((MulAction.stabilizer G y).relIndex (MulAction.stabilizer G x) : ℝ)
          = μ y * ((MulAction.stabilizer G x).relIndex (MulAction.stabilizer G y) : ℝ)) →
    (∀ x y, m x y = m y x) → (∀ (g : G) x y, m (g • x) (g • y) = m x y) →
    (∀ x, {y | m x y ≠ 0}.Finite) →
    ∀ x y, μ x * (∑ᶠ z ∈ MulAction.orbit G y, m x z) = μ y * (∑ᶠ z ∈ MulAction.orbit G x, m y z)
def KernelAvg : Prop :=
  ∀ (ι : Type) [Fintype ι] (μ : ι → ℝ) (M : ι → ι → ℝ) (ω : ι → ℂ) (ε₁ ε₂ : ℝ),
    (∀ i, 0 ≤ μ i) → (∀ i j, μ i * M i j = μ j * M j i) →
    (∀ i, |(∑ j, M i j) - 1| ≤ ε₁) →
    (∀ i, ‖∑ j, (M i j : ℂ) * ω j‖ ≤ ε₂ * ‖ω i‖) →
    ‖∑ i, (μ i : ℂ) * ω i‖ ≤ (ε₁ + ε₂) * ∑ i, μ i * ‖ω i‖
def KernelAvgSum : Prop :=
  ∀ (ι : Type) (μ : ι → ℝ) (M : ι → ι → ℝ) (ω : ι → ℂ) (ε₁ ε₂ : ℝ),
    (∀ i, 0 ≤ μ i) → Summable μ → (∀ i j, 0 ≤ M i j) → (∀ i, Summable (M i)) →
    (∀ i j, μ i * M i j = μ j * M j i) → (∀ i, ‖ω i‖ = 1) →
    (∀ i, |(∑' j, M i j) - 1| ≤ ε₁) →
    (∀ i, ‖∑' j, (M i j : ℂ) * ω j‖ ≤ ε₂) →
    ‖∑' i, (μ i : ℂ) * ω i‖ ≤ (ε₁ + ε₂) * ∑' i, μ i
def MaxSum : Prop :=
  ∀ (D : Type) [Fintype D] (w μ : D → ℝ) (amp : D → ℂ) (ε Mx : ℝ),
    (∀ d, 0 ≤ w d) → (∀ d, 0 ≤ μ d) → 0 ≤ ε → (∀ d, ‖amp d‖ ≤ ε * μ d) → (∀ d, μ d ≤ Mx) →
    ∑ d, w d * ‖amp d‖ ^ 2 ≤ ε ^ 2 * Mx * ∑ d, w d * μ d
def TypeCS : Prop :=
  ∀ (D Ty : Type) [Fintype D] [Fintype Ty] (w : D → ℝ) (amp : Ty → D → ℂ),
    (∀ d, 0 ≤ w d) →
    ∑ d, w d * ‖∑ t, amp t d‖ ^ 2 ≤ (Fintype.card Ty : ℝ) * ∑ t, ∑ d, w d * ‖amp t d‖ ^ 2
def AssemblyNG : Prop :=
  ∀ (c : ℕ) (C₀ : ℝ), ∃ C : ℕ, ∀ (k r q e : ℕ) (H nn : ℝ) (D Ty : Type) [Fintype D] [Fintype Ty]
    (w : D → ℝ) (amp : Ty → D → ℂ) (μ : Ty → D → ℝ) (be I : Ty → ℝ) (isBe : Ty → Prop),
    1 ≤ e → 4 * r + 7 ≤ k → 2 ≤ q → 1 ≤ H → (Nonempty Ty → (q : ℝ) ≤ H) → 0 ≤ nn →
    (∀ d, 0 ≤ w d) → (Fintype.card Ty : ℝ) ≤ H ^ (c * e) →
    (∀ t, 1 ≤ be t) → (∀ t, 0 ≤ I t) → (∀ t, I t ≤ be t) → (∀ t, ¬ isBe t → I t ≤ be t / q) →
    (∀ t d, 0 ≤ μ t d) →
    (∀ t d, μ t d ≤ H ^ (c * e) * I t ^ (k - 1)) →
    (∀ t, ∑ d, w d * μ t d ≤ H ^ (c * e) * (be t ^ (k - 1))⁻¹ * nn) →
    (∀ t d, ‖amp t d‖ ≤ μ t d) →
    (∀ t d, isBe t → ‖amp t d‖ ≤ C₀ * (q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * μ t d) →
    ∑ d, w d * ‖∑ t, amp t d‖ ^ 2 ≤ H ^ (C * e) * (q : ℝ) ^ (-((k : ℤ) - 2 * r - 5)) * nn
def AssemblyNG2 : Prop :=
  ∀ c : ℕ, ∃ C : ℕ, ∀ (k e : ℕ) (H nn : ℝ) (D Ty : Type) [Fintype D] [Fintype Ty]
    (w : D → ℝ) (amp : Ty → D → ℂ) (μ : Ty → D → ℝ) (be I : Ty → ℝ),
    1 ≤ H → 0 ≤ nn → (∀ d, 0 ≤ w d) → (Fintype.card Ty : ℝ) ≤ H ^ (c * e) →
    (∀ t, 1 ≤ be t) → (∀ t, 0 ≤ I t) → (∀ t, I t ≤ be t) → (∀ t d, 0 ≤ μ t d) →
    (∀ t d, μ t d ≤ H ^ (c * e) * I t ^ (k - 1)) →
    (∀ t, ∑ d, w d * μ t d ≤ H ^ (c * e) * (be t ^ (k - 1))⁻¹ * nn) →
    (∀ t d, ‖amp t d‖ ≤ μ t d) →
    ∑ d, w d * ‖∑ t, amp t d‖ ^ 2 ≤ H ^ (C * e) * nn
def EqualityNG : Prop :=
  ∀ (D : Type) [Fintype D] (w m : D → ℝ) (om amp : D → ℂ),
    (∀ d, m d = 0 ∨ m d = 1) → (∀ d, ‖om d‖ = 1) → (∀ d, amp d = om d * (m d : ℂ)) →
    ∑ d, w d * ‖amp d‖ ^ 2 = ∑ d, w d * m d
def ClassSquares : Prop :=
  ∀ (ι : Type) [Fintype ι] (s : Setoid ι) [DecidableRel s.r] [Fintype (Quotient s)]
    [DecidableEq (Quotient s)] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (v : ι → V),
    ∑ i, ∑ j, (if s.r i j then inner ℂ (v i) (v j) else 0)
      = ((∑ c : Quotient s, ‖∑ i ∈ univ.filter (fun i => Quotient.mk s i = c), v i‖ ^ 2 : ℝ) : ℂ)
def ProjW : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (z y : V) (T : E), h z z = -T → h (T • y + h y z • z) z = 0
def DivisorCount : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (I : Ideal (NumberField.RingOfIntegers K)), I ≠ ⊥ →
    {J : Ideal (NumberField.RingOfIntegers K) | J ∣ I}.Finite ∧
    {J : Ideal (NumberField.RingOfIntegers K) | J ∣ I}.ncard ≤ Ideal.absNorm I
def WeightedCS : Prop :=
  ∀ (ι : Type) [Fintype ι] (V : Type) [SeminormedAddCommGroup V] (v : ι → V) (W : ι → ℝ),
    (∀ i, 0 < W i) → ‖∑ i, v i‖ ^ 2 ≤ (∑ i, (W i)⁻¹) * ∑ i, W i * ‖v i‖ ^ 2
def OmCount : Prop :=
  ∀ (P : Type) (Om : Finset P) (H : P → ℝ), (∀ p ∈ Om, 2 ≤ H p) → (2 : ℝ) ^ Om.card ≤ ∏ p ∈ Om, H p
def Step4 : Prop :=
  ∀ (P : Type) [Fintype P] [DecidableEq P] (Om : Finset P) (D : P → Type) [∀ p, Fintype (D p)]
    (w : ∀ p, D p → ℝ) (aN aZ : ∀ p, D p → ℂ) (H nn ngen : P → ℝ) (q : P → ℕ) (c κ : ℕ),
    (∀ p d, 0 ≤ w p d) → (∀ p, 1 ≤ H p) → (∀ p, 2 ≤ q p) → (∀ p, 0 ≤ nn p) →
    (∀ p ∈ Om, ∑ d, w p d * ‖aN p d‖ ^ 2 ≤ H p ^ c * ((q p : ℝ) ^ κ)⁻¹ * nn p) →
    (∀ p, ∑ d, w p d * ‖aZ p d‖ ^ 2 ≤ H p ^ c * nn p) →
    (∀ p, nn p ≤ H p ^ c * ngen p) →
    ∑ d : (∀ p, D p), (∏ p, w p (d p)) *
        ‖∑ A ∈ Om.powerset.filter (fun A => A.Nonempty),
            ∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2
      ≤ (4 : ℝ) ^ Om.card * (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p
end Formalism.HermitianLatticeCounting.S4


