-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuBasic
-- name    : Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:40.41405+00:00
-- url     : https://prove2.me/theorems/fc1cec60-ff37-4471-8af4-d2ff13631ad8
-- title:
--   Nu Basic
-- statement:
--   Definitions and structural lemmas for Nu Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/NuBasic.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuInf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace KStar.Tree
variable {Γ : Type} [Group Γ] (l : ℕ) [Fact l.Prime] (ε : Γ →* ℤ_[l]ˣ) (n : ℕ)
end KStar.Tree


