-- Prove2me | Definitions.Def_Formalism_ZetaNonvanishing_LandauLemma
-- name    : Formalism_ZetaNonvanishing_LandauLemma
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:53.21452+00:00
-- url     : https://prove2.me/theorems/4cf7a6eb-ebfd-4dd9-84b1-c3a4326aef65
-- title:
--   Landau Lemma
-- statement:
--   Definitions and structural lemmas for Landau Lemma, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/LandauLemma.lean

import Definitions.Def_Formalism_ZetaRealNonvanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace Formalism
namespace landauIteratedDerivatives
def Good (H : ℝ → ℝ) (σ : ℝ) : Prop :=
  IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1)
def J (H : ℝ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ x in Ioi (1:ℝ), (((-Real.log x) ^ n * H x : ℝ) : ℂ) * (x : ℂ) ^ (-z - 1)
end landauIteratedDerivatives
end Formalism


