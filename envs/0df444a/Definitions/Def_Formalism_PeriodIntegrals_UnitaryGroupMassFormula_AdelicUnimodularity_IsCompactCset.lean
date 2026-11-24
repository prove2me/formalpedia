-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_IsCompactCset
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_IsCompactCset
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:37:20.714803+00:00
-- url     : https://prove2.me/theorems/2871986d-4271-4606-86f1-765d8fea107c
-- title:
--   Is Compact Cset
-- statement:
--   Definitions and structural lemmas for Is Compact Cset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/IsCompactCset.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_MulVecMemLf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WAU
open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix
namespace Cpt
variable (I : AutInst)
abbrev sg : I.E ⊗[I.F] Af I.F →+* I.E ⊗[I.F] Af I.F := Formalism.UG.sigR I.cm.sig (Af I.F)
abbrev Jf : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))
def Bx (N : ℕ) : Set (Af I.F) := (fun u => algebraMap I.F (Af I.F) ((N : I.F)⁻¹) * u) '' Ohat I.F
def Cset (N : ℕ) : Set (Co I × Co I) :=
  {p | (∀ i j k, p.1 i j k ∈ Bx I N ∧ p.2 i j k ∈ Bx I N) ∧
    matOf I p.1 * matOf I p.2 = 1 ∧ matOf I p.2 * matOf I p.1 = 1 ∧
    Formalism.UG.cT (sg I) (matOf I p.1) * Jf I * matOf I p.1 = Jf I ∧
    (∀ l ∈ I.L, matOf I p.1 *ᵥ inclV (F := I.F) l ∈ I.Lf) ∧
    (∀ l ∈ I.L, matOf I p.2 *ᵥ inclV (F := I.F) l ∈ I.Lf)}
def psi (N : ℕ) (p : Cset I N) : I.Gf :=
  ⟨⟨matOf I p.1.1, matOf I p.1.2, p.2.2.1, p.2.2.2.1⟩, p.2.2.2.2.1⟩
end Cpt
end PI.WAU


