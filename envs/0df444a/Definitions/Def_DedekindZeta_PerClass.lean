-- Prove2me | Definitions.Def_DedekindZeta_PerClass
-- name    : DedekindZeta_PerClass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T00:24:23.16329+00:00
-- url     : https://prove2.me/theorems/3dfe93bb-9828-4e5b-b042-3d91954fd3d4
-- title:
--   Per Class
-- statement:
--   Definitions and structural lemmas for Per Class, from Mathlib Initiative and contributors's pinned A real sum-product counterexample conditional on Martinet’s tower theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/PerClass.lean

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_GammaIntegral
set_option autoImplicit true
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
end
end DedekindZeta


