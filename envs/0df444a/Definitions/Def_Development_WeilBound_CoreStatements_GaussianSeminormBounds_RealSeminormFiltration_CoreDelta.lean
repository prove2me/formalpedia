-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta
-- name    : Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T12:16:18.096089+00:00
-- url     : https://prove2.me/theorems/99526886-ae83-58fd-8d42-42ca4890dbda
-- title:
--   Core Delta
-- statement:
--   Definitions and structural lemmas for Core Delta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreDelta.lean

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace TensorProduct
namespace PositivityTheory.KReal
namespace Delta
section Gen
variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
end Gen
variable {p q r s : ℕ}
def dv (p q r s : ℕ) : Ln p q r s → Pol p q r 0 ⊗[ℂ] Pol p q 0 s
  | (a, .inl k) => (X (a, Sum.inl k) : Pol p q r 0) ⊗ₜ[ℂ] (1 : Pol p q 0 s)
  | (a, .inr l) => (1 : Pol p q r 0) ⊗ₜ[ℂ] (X (a, Sum.inr l) : Pol p q 0 s)
def dl (p q r s : ℕ) : Pol p q r s →ₐ[ℂ] Pol p q r 0 ⊗[ℂ] Pol p q 0 s := aeval (dv p q r s)
section Form
variable (b : Pol p q r 0 →ₗ[ℂ] Pol p q 0 s →ₗ[ℂ] ℂ)
end Form
def iA (p q r s : ℕ) : Ln p q r 0 → Ln p q r s := fun l => (l.1, Sum.elim Sum.inl Fin.elim0 l.2)
def iB (p q r s : ℕ) : Ln p q 0 s → Ln p q r s := fun l => (l.1, Sum.elim Fin.elim0 Sum.inr l.2)
end Delta
end PositivityTheory.KReal
end


