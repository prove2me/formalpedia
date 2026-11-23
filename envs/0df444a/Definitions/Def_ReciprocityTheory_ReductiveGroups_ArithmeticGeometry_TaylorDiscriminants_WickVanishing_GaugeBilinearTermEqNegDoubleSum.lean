-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:28.46939+00:00
-- url     : https://prove2.me/theorems/e5fa0f48-5da3-4463-94a2-981764c4b67e
-- title:
--   Gauge Bilinear Term Eq Neg Double Sum
-- statement:
--   Definitions and structural lemmas for Gauge Bilinear Term Eq Neg Double Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeBilinearTermEqNegDoubleSum.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] {d : ℕ}
def eZ (d : ℕ) : Fin 1 × Fin d ↪ Fin 2 × Fin d := ⟨fun p => (1, p.2), fun p q h => by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Subsingleton.elim _ _) h.2⟩
def eXv (d : ℕ) : Fin 1 × Fin d ↪ Fin 2 × Fin d := ⟨fun p => (0, p.2), fun p q h => by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Subsingleton.elim _ _) h.2⟩
def swE (d : ℕ) : Fin 2 × Fin d ↪ Fin 2 × Fin d := ⟨fun p => (Fin.rev p.1, p.2), fun p q h => by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [Prod.mk.injEq, Fin.rev_inj] at h
  exact Prod.ext h.1 h.2⟩
section Exp
variable [Algebra ℚ k]
end Exp
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing


