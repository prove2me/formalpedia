-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:59:38.727492+00:00
-- url     : https://prove2.me/theorems/5b95ba75-6ec6-4232-b8ae-e6416b23fcaa
-- title:
--   Superdiagonal Addition Invariance
-- statement:
--   Definitions and structural lemmas for Superdiagonal Addition Invariance, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SuperdiagonalAdditionInvariance.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last


set_option autoImplicit false
namespace Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
section unfold
variable {G X : Type} [Group G] [MulAction G X]
open MulAction
end unfold
section dualcap
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]
end dualcap
section sametrace
variable {E : Type} [CommRing E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
  (h : V →ₗ[E] V →ₗ⋆[E] E) {r : ℕ} (e : Fin r → V)
def shear (t : Fin r → V) : V →ₗ[E] V where
  toFun v := v + ∑ j, h v (e j) • t j
  map_add' v w := by
    simp only [map_add, LinearMap.add_apply, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c v := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add,
      Finset.smul_sum]
end sametrace
namespace Part2
end Part2
section dvrcard
variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]
end dvrcard
section count
variable {F : Type} [Field F] [Fintype F]
end count
section inert
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
lemma frob_add (x y : L) :
    (x + y) ^ Fintype.card K = x ^ Fintype.card K + y ^ Fintype.card K :=
  map_add (FiniteField.frobeniusAlgHom K L) x y
lemma card_L (h2 : Module.finrank K L = 2) : Fintype.card L = Fintype.card K ^ 2 := by
  rw [← h2]; exact Module.card_eq_pow_finrank
lemma frob_frob (h2 : Module.finrank K L = 2) (x : L) :
    (x ^ Fintype.card K) ^ Fintype.card K = x := by
  rw [← pow_mul, ← sq, ← card_L h2, FiniteField.pow_card]
@[reducible] def frobStar (h2 : Module.finrank K L = 2) : StarRing L where
  star x := x ^ Fintype.card K
  star_involutive := frob_frob h2
  star_mul x y := by rw [mul_pow, mul_comm]
  star_add := frob_add
end inert
section inert2
variable (K : Type) {L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
def hB {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L) (x y : Fin n → L) : L :=
  ∑ k, ∑ l, x k * Ph k l * y l ^ Fintype.card K
def hMat {n j : ℕ} (Ph : Matrix (Fin n) (Fin n) L) (X : Fin j → Fin n → L) :
    Matrix (Fin j) (Fin n) L :=
  Matrix.of fun b k => ∑ l, Ph k l * X b l ^ Fintype.card K
variable {K}
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)
end inert2
section inert3
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)
end inert3
section inert4
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)
end inert4
section unram2
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]
def mO (o O : Type) [CommRing o] [IsLocalRing o] [CommRing O] [Algebra o O] : Ideal O :=
  (IsLocalRing.maximalIdeal o).map (algebraMap o O)
end unram2
section orth
variable {O : Type} [CommRing O] [StarRing O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂]
  (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)
end orth
section unimod
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)
end unimod
section unimod2
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)
end unimod2
section annih
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]
def piO (O : Type) [CommRing O] {o : Type} [CommRing o] [Algebra o O] (ϖ : o) (M : ℕ) : AddSubgroup O where
  carrier := {y | ∃ z, y = algebraMap o O (ϖ ^ M) * z}
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by ring⟩
  zero_mem' := ⟨0, by ring⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩; exact ⟨-a, by ring⟩
end annih
section stdform
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)
end stdform
section hermjac
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]
omit [StarRing E] in
lemma hj_repr (β : Module.Basis (Fin 2) F E) (ω : E) (h0 : β 0 = 1) (h1 : β 1 = ω) (c0 c1 : F) :
    β.repr (algebraMap F E c0 + algebraMap F E c1 * ω) 0 = c0 ∧
    β.repr (algebraMap F E c0 + algebraMap F E c1 * ω) 1 = c1 := by
  have : algebraMap F E c0 + algebraMap F E c1 * ω = c0 • β 0 + c1 • β 1 := by
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one]
  rw [this]
  constructor <;> simp
omit [StarRing E] in
lemma hj_decomp (β : Module.Basis (Fin 2) F E) (ω : E) (h0 : β 0 = 1) (h1 : β 1 = ω) (e : E) :
    e = algebraMap F E (β.repr e 0) + algebraMap F E (β.repr e 1) * ω := by
  conv_lhs => rw [← β.sum_repr e, Fin.sum_univ_two, h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one]
end hermjac
section hermjacA
variable {E : Type} [CommRing E]
def rmulE (m : ℕ) (A : Matrix (Fin m) (Fin m) E) :
    Matrix (Fin m) (Fin m) E →ₗ[E] Matrix (Fin m) (Fin m) E :=
  { toFun := fun X : Matrix (Fin m) (Fin m) E => X * A
    map_add' := fun X Y => Matrix.add_mul X Y A
    map_smul' := fun c X => Matrix.smul_mul c X A }
def lmulE (m : ℕ) (B : Matrix (Fin m) (Fin m) E) :
    Matrix (Fin m) (Fin m) E →ₗ[E] Matrix (Fin m) (Fin m) E :=
  { toFun := fun X : Matrix (Fin m) (Fin m) E => B * X
    map_add' := fun X Y => Matrix.mul_add B X Y
    map_smul' := fun c X => Matrix.mul_smul B c X }
end hermjacA
section hermjacA2
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]
end hermjacA2
section hermjacB
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]
omit [StarRing E] in

noncomputable def dualNumberReal (β : Module.Basis (Fin 2) F E) (ε : E) (h0 : β 0 = 1) (h1 : β 1 = ε) (hε : ε * ε = 0) :
    E →+* F where
  toFun e := β.repr e 0
  map_one' := by
    have := (hj_repr β ε h0 h1 1 0).1
    simpa using this
  map_mul' x y := by
    have e1 : x * y = algebraMap F E (β.repr x 0 * β.repr y 0)
        + algebraMap F E (β.repr x 0 * β.repr y 1 + β.repr x 1 * β.repr y 0) * ε := by
      conv_lhs => rw [hj_decomp β ε h0 h1 x, hj_decomp β ε h0 h1 y]
      simp only [map_mul, map_add]
      linear_combination (algebraMap F E (β.repr x 1) * algebraMap F E (β.repr y 1)) * hε
    conv_lhs => rw [e1]
    exact (hj_repr β ε h0 h1 _ _).1
  map_zero' := by simp
  map_add' x y := by simp
end hermjacB
end Formalism.HermitianLatticeCounting.P.S4aux
namespace Formalism.HermitianLatticeCounting.P
end Formalism.HermitianLatticeCounting.P


