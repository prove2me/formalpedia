-- Prove2me | Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
-- name    : QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:08:36.496239+00:00
-- url     : https://prove2.me/theorems/c6a35bd6-be6b-4cc0-a6a3-5db046f1c46e
-- title:
--   Multiplication Embedding
-- statement:
--   Definitions and structural lemmas for Multiplication Embedding, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/MultiplicationEmbedding.lean

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
set_option autoImplicit false
namespace QEC.Coding
abbrev F256MFEIndex := Fin 8 × (Fin 8 × Fin 8)
noncomputable def f256MFEIndexEquiv : F256MFEIndex ≃ Fin 512 :=
  ((Equiv.refl (Fin 8)).prodCongr (finProdFinEquiv (m := 8) (n := 8))).trans
    (finProdFinEquiv (m := 8) (n := 64))
noncomputable def f256MFEIndex (i j k : Fin 8) : Fin 512 :=
  f256MFEIndexEquiv (i, (j, k))
noncomputable def f256MFEpi2 : Equiv.Perm (Fin 512) :=
  (f256MFEIndexEquiv.symm.trans
    ((Equiv.prodComm (Fin 8) (Fin 8 × Fin 8)).trans
      (Equiv.prodAssoc (Fin 8) (Fin 8) (Fin 8)))).trans f256MFEIndexEquiv
noncomputable def f256MFEpi3 : Equiv.Perm (Fin 512) :=
  f256MFEpi2.trans f256MFEpi2
noncomputable def f256MFEPermutationAction (pi : Equiv.Perm (Fin 512)) :
    (Fin 512 → ZMod 2) →ₗ[ZMod 2] (Fin 512 → ZMod 2) where
  toFun v := fun q => v (pi q)
  map_add' v w := by
    ext q
    rfl
  map_smul' c v := by
    ext q
    rfl
noncomputable def f256MFEpi2Action : (Fin 512 → ZMod 2) →ₗ[ZMod 2] (Fin 512 → ZMod 2) :=
  f256MFEPermutationAction f256MFEpi2
noncomputable def f256MFEpi3Action : (Fin 512 → ZMod 2) →ₗ[ZMod 2] (Fin 512 → ZMod 2) :=
  f256MFEPermutationAction f256MFEpi3
noncomputable def f256MFESigma : F256 →ₗ[ZMod 2] (Fin 512 → ZMod 2) where
  toFun x := fun q => f256PolynomialBasis.equivFun x (f256MFEIndexEquiv.symm q).1
  map_add' x y := by
    ext q
    simp only [map_add, Pi.add_apply]
  map_smul' c x := by
    ext q
    have hsmul := congr_fun (f256PolynomialBasis.equivFun.map_smul c x)
      (f256MFEIndexEquiv.symm q).1
    simpa only [Pi.smul_apply, RingHom.id_apply] using hsmul
noncomputable def f256MFEPsi : (Fin 512 → ZMod 2) →ₗ[ZMod 2] F256 where
  toFun v :=
    ∑ i : Fin 8, ∑ j : Fin 8, ∑ k : Fin 8,
      v (f256MFEIndex i j k) •
        (f256PolynomialBasis i * f256PolynomialBasis j * f256PolynomialBasis k)
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    change
      (∑ i : Fin 8, ∑ j : Fin 8, ∑ k : Fin 8,
        (c * v (f256MFEIndex i j k)) •
          (f256PolynomialBasis i * f256PolynomialBasis j * f256PolynomialBasis k)) =
        c • ∑ i : Fin 8, ∑ j : Fin 8, ∑ k : Fin 8,
          v (f256MFEIndex i j k) •
            (f256PolynomialBasis i * f256PolynomialBasis j * f256PolynomialBasis k)
    simp only [Finset.smul_sum, smul_smul]
end QEC.Coding


