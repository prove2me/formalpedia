-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
-- name    : QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:58:20.501213+00:00
-- url     : https://prove2.me/theorems/9edd7915-4ebe-4ccf-9c86-a4c73c88c8c6
-- title:
--   Homology Dimension
-- statement:
--   Definitions and structural lemmas for Homology Dimension, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/HomologyDimension.lean

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Theorems.Thm_QEC_Coding_FiberBundle_boundary2_constantFiberTwoChain_eq_verticalFundamentalWord

set_option autoImplicit false
namespace QEC.Coding.FiberBundle
namespace RandomBase
end RandomBase
noncomputable def constantFiberTwoCycleLinearMap
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    (RandomBase.code baseSample).carrier →ₗ[ZMod 2]
      LinearMap.ker
        (boundary2
          (RandomTwist.fiberBundleData baseSample twistSample)) where
  toFun x := by
    refine ⟨constantFiberTwoChain
      (fiberOne := ZMod (ell * ell)) x.1, ?_⟩
    change boundary2
      (RandomTwist.fiberBundleData baseSample twistSample)
      (constantFiberTwoChain
        (fiberOne := ZMod (ell * ell)) x.1) = 0
    rw [boundary2_constantFiberTwoChain_eq_verticalFundamentalWord]
    have hx :
        Matrix.toLin' (RandomBase.boundary baseSample) x.1 = 0 := by
      exact (mem_parityCheckKernelCode
        (Matrix.toLin' (RandomBase.boundary baseSample)) x.1).mp x.2
    rw [hx]
    funext q
    rcases q with bi | aj
    · rfl
    · rfl
  map_add' x y := by
    ext bj
    rfl
  map_smul' coefficient x := by
    ext bj
    rfl
end QEC.Coding.FiberBundle


