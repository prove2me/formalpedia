-- Prove2me | Definitions.Def_mme_little_endian_MM_power_flatten
-- name    : mme_little_endian_MM_power_flatten
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T05:16:18.91304+00:00
-- url     : https://prove2.me/theorems/97a3bee1-e01e-453f-86e8-9a47b1956007
-- title:
--   Little-endian coordinate maps for matrix-multiplication tensor powers
-- statement:
--   For a matrix-multiplication tensor \(\langle n,m,p\rangle\), define explicit modewise linear maps from its \(r\)-fold Kronecker power to \(\langle n^r,m^r,p^r\rangle\). At each recursive step, the newest tensor factor is placed in the least-significant finite coordinate. The package also records the zero- and successor-power equations needed for induction.\n\nThese maps make the usual power-flattening isomorphism coordinate-sensitive, so a named word of source channels can later be tracked to its exact standard matrix-multiplication basis coordinate.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3 and Appendix A, https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_little_endian_MM_coordinate_router
import Definitions.Def_mme_TypeGrading_kron

open PiTensorProduct TensorProduct BigOperators

namespace MME.DWZFineChannel

universe u

set_option autoImplicit false
set_option linter.unusedSimpArgs false

def singletonPairMap (K : Type u) [Field K] :
    K →ₗ[K] (Fin 1 × Fin 1 → K) where
  toFun x := fun _ => x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def littleEndianUnitMaps (K : Type u) [Field K] :
    ∀ s : Fin 3, K →ₗ[K] MMSpace K 1 1 1 s
  | ⟨0, _⟩ => singletonPairMap K
  | ⟨1, _⟩ => singletonPairMap K
  | ⟨2, _⟩ => singletonPairMap K

/-- Explicitly flatten an MM Kronecker power, placing position zero in the
least significant coordinate. -/
noncomputable def littleEndianPowerMaps
    (K : Type u) [Field K] (n m p : ℕ) :
    ∀ r : ℕ, ∀ s : Fin 3,
      ((MMObj K n m p).kronPow r).V s →ₗ[K]
        (MMObj K (n ^ r) (m ^ r) (p ^ r)).V s
  | 0, ⟨0, _⟩ =>
      singletonPairMap K
  | 0, ⟨1, _⟩ =>
      singletonPairMap K
  | 0, ⟨2, _⟩ =>
      singletonPairMap K
  | r + 1, ⟨0, _⟩ =>
      (littleEndianKronEquiv K n m (n ^ r) (m ^ r)).toLinearMap.comp
        (TensorProduct.map LinearMap.id
          (littleEndianPowerMaps K n m p r 0))
  | r + 1, ⟨1, _⟩ =>
      (littleEndianKronEquiv K m p (m ^ r) (p ^ r)).toLinearMap.comp
        (TensorProduct.map LinearMap.id
          (littleEndianPowerMaps K n m p r 1))
  | r + 1, ⟨2, _⟩ =>
      (littleEndianKronEquiv K p n (p ^ r) (n ^ r)).toLinearMap.comp
        (TensorProduct.map LinearMap.id
          (littleEndianPowerMaps K n m p r 2))

theorem littleEndianPowerMaps_zero
    (K : Type u) [Field K] (n m p : ℕ) :
    littleEndianPowerMaps K n m p 0 = littleEndianUnitMaps K := by
  funext s
  fin_cases s <;> rfl

theorem littleEndianPowerMaps_succ
    (K : Type u) [Field K] (n m p r : ℕ) :
    littleEndianPowerMaps K n m p (r + 1) =
      fun s =>
        (littleEndianModeEquiv K n m p (n ^ r) (m ^ r) (p ^ r) s).toLinearMap.comp
          (TensorProduct.map LinearMap.id
            (littleEndianPowerMaps K n m p r s)) := by
  funext s
  fin_cases s <;> rfl

end MME.DWZFineChannel


