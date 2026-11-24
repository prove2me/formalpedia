-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZGlueA
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZGlueA
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:06:19.945049+00:00
-- url     : https://prove2.me/theorems/6144e512-dc9d-4ffa-9867-0a84ed86964e
-- title:
--   Lat Dict ZGlue A
-- statement:
--   Definitions and structural lemmas for Lat Dict ZGlue A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZGlueA.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain
open scoped TensorProduct
namespace Formalism.L2.SG.Pf.LatDictZ.Z5
open Formalism.MainNotions.S PIW.AdelClassFin Formalism.L2.SG.Pf.LatDictZ
section Gl
variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {n : Type} [Fintype n] [DecidableEq n]
def gl (s : Finset ι) (e : ι → R) (M : Matrix n n R) (A : ι → Matrix n n R) : Matrix n n R :=
  M + ∑ i ∈ s, e i • (A i - M)
def Orth (s : Finset ι) (e : ι → R) : Prop := ∀ i ∈ s, ∀ j ∈ s, e i * e j = if i = j then e i else 0
end Gl
section Ad
variable {F : Type} [Field F] [NumberField F]
def mkI (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F) : Af F :=
  ⟨c, Filter.Eventually.of_forall hc⟩
def ev (v : HeightOneSpectrum (𝓞 F)) : Af F →+* v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
open Classical in

def eT (T : Set (HeightOneSpectrum (𝓞 F))) : Af F :=
  mkI (fun v => if v ∈ T then 1 else 0) (fun v => by split_ifs; exacts [one_mem _, zero_mem _])
end Ad
section Inst
variable (I : AutInst)
abbrev iA : Af I.F →ₐ[I.F] I.E ⊗[I.F] Af I.F := Algebra.TensorProduct.includeRight
def under (p : Ideal (𝓞 I.E)) (hp : p.IsMaximal) : HeightOneSpectrum (𝓞 I.F) where
  asIdeal := p.comap (algebraMap (𝓞 I.F) (𝓞 I.E))
  isPrime := by have := hp.isPrime; infer_instance
  ne_bot := fun h => Ring.ne_bot_of_isMaximal_of_not_isField hp (NumberField.RingOfIntegers.not_isField I.E)
    (Ideal.eq_bot_of_comap_eq_bot h)
end Inst
end Formalism.L2.SG.Pf.LatDictZ.Z5


