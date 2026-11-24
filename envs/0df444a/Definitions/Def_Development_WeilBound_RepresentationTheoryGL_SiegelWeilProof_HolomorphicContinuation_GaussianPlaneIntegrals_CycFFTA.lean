-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTA
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTA
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:54:44.5791+00:00
-- url     : https://prove2.me/theorems/b6f82f91-12a2-467a-bf2e-8f2e060c1b88
-- title:
--   Cyc FFTA
-- statement:
--   Definitions and structural lemmas for Cyc FFTA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFTA.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace PositivityTheory.Rg.Sw.FFTSteps.CycF
variable {m n : ℕ} (ε : Fin m → Bool)
abbrev VV (ι : Type) (n : ℕ) := (ι × Fin n) ⊕ (ι × Fin n)
abbrev Rw (β : Bool) := {a : Fin m // ε a = β}
def jv (β : Bool) : VV (Rw ε β) n → Fin m × Fin n × Bool :=
  Sum.elim (fun x => (x.1.1, x.2, false)) (fun x => (x.1.1, x.2, true))
def emb (β : Bool) : PV (Rw ε β) (Fin n) (Fin n) →ₐ[ℂ] PX m n := rename (jv ε β)
def act (u : Matrix (Fin m) (Fin m) ℂ) : PX m n →ₐ[ℂ] PX m n :=
  aeval (fun k : Fin m × Fin n × Bool => if k.2.2 then ∑ b, C (star (u k.1 b)) * X (b, k.2.1, true)
    else ∑ b, C (u k.1 b) * X (b, k.2.1, false))
def blk (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) : Matrix (Fin m) (Fin m) ℂ := fun a b =>
  if ha : ε a = β then (if hb : ε b = β then v ⟨a, ha⟩ ⟨b, hb⟩ else 0) else (if a = b then 1 else 0)
variable {ε}
end PositivityTheory.Rg.Sw.FFTSteps.CycF


