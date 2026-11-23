-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:58.337516+00:00
-- url     : https://prove2.me/theorems/04983d03-d8d5-40d8-8398-52323868ce1c
-- title:
--   Exp Uniq Jet
-- statement:
--   Definitions and structural lemmas for Exp Uniq Jet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpUniqJet.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
open MvPolynomial Formalism.L2.Pj
variable {R : Type} [CommRing R]
abbrev zz {κ : Type} (m : ℕ) (j : κ) : Jet R κ m := Ideal.Quotient.mk _ (X j)
variable (R) in

def Ij (κ : Type) (m : ℕ) : Ideal (Jet R κ m) := Ideal.span (Set.range (zz (R := R) (κ := κ) m))
section Scale
abbrev sc {κ : Type} (m : ℕ) (c : R) : Jet R κ m →ₐ[R] Jet R κ m := jetScale (fun _ => c)
end Scale
section Kill
variable {n : ℕ}
def killS (i : Fin 2) (v : Fin 2 × Fin n) : MvPolynomial (Fin 2 × Fin n) R := if v.1 = i then 0 else X v
theorem killS_mem (i : Fin 2) (v : Fin 2 × Fin n) : killS (R := R) i v ∈ orig R (Fin 2 × Fin n) := by
  unfold killS
  split_ifs
  · exact Ideal.zero_mem _
  · exact X_mem_orig v
def kill (m : ℕ) (i : Fin 2) : Jet R (Fin 2 × Fin n) m →ₐ[R] Jet R (Fin 2 × Fin n) m :=
  jetMap (killS i) (killS_mem i)
def Kp (m : ℕ) (i : Fin 2) : Ideal (Jet R (Fin 2 × Fin n) m) :=
  Ideal.span (Set.range fun j : Fin n => zz (R := R) m (i, j))
end Kill
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet


