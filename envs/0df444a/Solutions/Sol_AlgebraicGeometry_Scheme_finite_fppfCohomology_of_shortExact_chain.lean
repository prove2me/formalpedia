-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.finite_fppfCohomology_of_shortExact_chain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/556c46b8-221d-5770-962d-5bfcfb04d4b2

import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import Theorems.Thm_AlgebraicGeometry_Scheme_finite_fppfCohomology_of_shortExact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_finite_fppfCohomology_of_shortExact_chain

set_option autoImplicit false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

universe u

theorem solution
    (S : Scheme.{u}) {k : ℕ} (F : Fin (k + 1) → Sheaf (smallFppfTopology S) Ab.{u + 1})
    (incl : ∀ i : Fin k, F i.castSucc ⟶ F i.succ) (n : ℕ)
    (h0 : Finite (fppfCohomology S (F 0) n))
    (hL : ∀ i : Fin k, ∃ (L : Sheaf (smallFppfTopology S) Ab.{u + 1}) (π : F i.succ ⟶ L)
      (w : incl i ≫ π = 0), (ShortComplex.mk (incl i) π w).ShortExact ∧
        Finite (fppfCohomology S L n)) :
    Finite (fppfCohomology S (F (Fin.last k)) n) := by
  suffices h : ∀ i : Fin (k + 1), Finite (fppfCohomology S (F i) n) from h (Fin.last k)
  intro i
  induction i using Fin.induction with
  | zero => exact h0
  | succ i ih =>
      obtain ⟨L, π, w, hses, hfin⟩ := hL i
      exact AlgebraicGeometry.Scheme.finite_fppfCohomology_of_shortExact S hses n ih hfin

end S_AlgebraicGeometry_Scheme_finite_fppfCohomology_of_shortExact_chain
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_finite_fppfCohomology_of_shortExact_chain (solution)
