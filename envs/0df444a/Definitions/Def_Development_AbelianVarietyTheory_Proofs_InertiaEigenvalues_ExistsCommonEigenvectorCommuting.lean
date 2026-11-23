-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommonEigenvectorCommuting
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommonEigenvectorCommuting
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:48.269484+00:00
-- url     : https://prove2.me/theorems/2bfa713f-f419-45b1-bc16-8b2de6c5a7e2
-- title:
--   Exists Common Eigenvector Commuting
-- statement:
--   Definitions and structural lemmas for Exists Common Eigenvector Commuting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCommonEigenvectorCommuting.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsBisFurther
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
namespace GlobalTheory.CommTriang
end GlobalTheory.CommTriang
namespace GlobalTheory.CommTriang
end GlobalTheory.CommTriang
namespace GlobalTheory.CommTriang
end GlobalTheory.CommTriang
namespace GlobalTheory.CommTriang
open Matrix
def blockOne {k : Type} [Field k] {n : ℕ} (Q : Matrix (Fin n) (Fin n) k) : Matrix (Fin (n+1)) (Fin (n+1)) k :=
  Matrix.of fun a b => Fin.cases (motive := fun _ => k) (Fin.cases (motive := fun _ => k) 1 (fun _ => 0) b)
    (fun a' => Fin.cases (motive := fun _ => k) 0 (fun b' => Q a' b') b) a
section
variable {k : Type} [Field k] {n : ℕ}
end
end GlobalTheory.CommTriang
namespace GlobalTheory.CommTriang
open Matrix
end GlobalTheory.CommTriang
namespace GlobalTheory.CommTriang
open Matrix
end GlobalTheory.CommTriang


