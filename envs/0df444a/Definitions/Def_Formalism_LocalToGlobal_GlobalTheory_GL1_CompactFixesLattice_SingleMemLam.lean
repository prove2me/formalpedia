-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_SingleMemLam
-- name    : Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_SingleMemLam
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:05.790135+00:00
-- url     : https://prove2.me/theorems/753325e6-8fe7-422c-bf77-763219c67533
-- title:
--   Single Mem Lam
-- statement:
--   Definitions and structural lemmas for Single Mem Lam, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL1/CompactFixesLattice/SingleMemLam.lean

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompact
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_incl_mem_SS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def lam {k : ℕ} (L : Submodule (SS F E) (Fin k → AE F E)) : Submodule (𝓞 E) (Fin k → E) where
  carrier := {x | (fun i => inclE (F := F) (AF F) (x i)) ∈ L}
  add_mem' := by
    intro a b ha hb
    have h : (fun i => inclE (F := F) (AF F) ((a + b) i)) =
        (fun i => inclE (F := F) (AF F) (a i)) + (fun i => inclE (F := F) (AF F) (b i)) := by
      funext i; simp
    show (fun i => inclE (F := F) (AF F) ((a + b) i)) ∈ L
    rw [h]
    exact L.add_mem ha hb
  zero_mem' := by
    have h : (fun i => inclE (F := F) (AF F) ((0 : Fin k → E) i)) = 0 := by
      funext i; simp
    show (fun i => inclE (F := F) (AF F) ((0 : Fin k → E) i)) ∈ L
    rw [h]
    exact L.zero_mem
  smul_mem' := by
    intro r x hx
    have h : (fun i => inclE (F := F) (AF F) ((r • x) i)) =
        (⟨inclE (F := F) (AF F) (r : E), incl_mem_SS ⟨r, rfl⟩⟩ : SS F E) •
          (fun i => inclE (F := F) (AF F) (x i)) := by
      funext i
      rw [Pi.smul_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Algebra.smul_def, map_mul]
    show (fun i => inclE (F := F) (AF F) ((r • x) i)) ∈ L
    rw [h]
    exact L.smul_mem _ hx
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
end


