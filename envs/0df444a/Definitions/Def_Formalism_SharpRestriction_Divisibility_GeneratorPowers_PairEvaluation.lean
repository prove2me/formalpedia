-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:09.610797+00:00
-- url     : https://prove2.me/theorems/56c723af-f875-4ee4-bfeb-a4e8139a0005
-- title:
--   Pair Evaluation
-- statement:
--   Definitions and structural lemmas for Pair Evaluation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean

import Mathlib
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
open MvPolynomial
variable {S : Type} [CommRing S] {d : ℕ}
abbrev Io (S σ : Type) [CommRing S] : Ideal (MvPolynomial σ S) := idealOfVars σ S
def xs (S : Type) [CommRing S] {n : ℕ} (d : ℕ) (k : Fin n) : Fin d → MvPolynomial (Fin n × Fin d) S :=
  fun i => X (k, i)
def lin {n : ℕ} (A : Fin d → Fin d → S) (k : Fin n) : Fin d → MvPolynomial (Fin n × Fin d) S :=
  fun i => ∑ l, C (A i l) * X (k, l)
def ev2 {τ : Type} (h : MvPolynomial (Fin 2 × Fin d) S) (u v : Fin d → MvPolynomial τ S) : MvPolynomial τ S :=
  aeval (fun p : Fin 2 × Fin d => ![u, v] p.1 p.2) h
section Sub
variable {σ τ : Type}
end Sub
section Main
variable [Algebra ℚ S]
end Main
end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation


