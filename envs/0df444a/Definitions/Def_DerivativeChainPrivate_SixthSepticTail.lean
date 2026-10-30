-- Prove2me | Definitions.Def_DerivativeChainPrivate_SixthSepticTail
-- name    : DerivativeChainPrivate_SixthSepticTail
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-27T00:28:50.994195+00:00
-- url     : https://prove2.me/theorems/c1a7287d-8c07-4baa-9aba-3ae920fa6372
-- title:
--   The exact seventh-row square-root tail
-- statement:
--   Define $K_7=3\sqrt{15145}/2720$ and the complex tail $T^{\rm tail}_7(w)=-K_7w^{39}T_7(w^2)/(\sqrt{R_7(w^2)}+P_7(w^2))$, using the principal complex square root. This function is defined on all complex numbers by Lean field division; analytic statements carry explicit disk conditions.
-- source:
--   Local frozen formal commit 824c42957a59765fe3d9f7d6d32554cff9dbeba8 (not asserted pushed), submission_sync/new_formal/sixth_power/join67/SixthSepticTail.lean, lines 5-7, SHA-256 8598bb9e35a3ea85c33363553959b61fa1ad14eb9a4318b0457449e869f1aba9.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthSepticAlgebra
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainPrivate

noncomputable def sixthSepticTail (w : ℂ) : ℂ :=
  -((3*Real.sqrt 15145/2720:ℝ):ℂ)*w^39*sixthSepticResidual (w^2)/
    (Complex.sqrt (sixthSepticRadicand (w^2))+sixthSepticPoly (w^2))






end DerivativeChainPrivate


