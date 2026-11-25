-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_AdeleEquiv
-- name    : GroundTheory_GlobalFields_Adele_BaseChange_AdeleEquiv
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:41:39.979653+00:00
-- url     : https://prove2.me/theorems/22460d07-8a1c-4c6f-a478-b6924ea6486a
-- title:
--   Adele Equiv
-- statement:
--   Definitions and structural lemmas for Adele Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/AdeleEquiv.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdeleTopology
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing
noncomputable section
namespace AdeleBaseChange
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (K L) in

def adeleMap : 𝔸[K] →+* 𝔸[L] :=
  RingHom.prodMap (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := K) (L := L))
    (finiteAdeleMap K L)
variable (K L) in

def adeleTensorEquiv : L ⊗[K] 𝔸[K] ≃ₐ[L] 𝔸[L] :=
  (Algebra.TensorProduct.prodRight K L L (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).trans
    (AlgEquiv.prodCongr GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv
      (finiteTensorEquiv K L))
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
def coord (i : ι) (y : 𝔸[L]) : 𝔸[K] :=
  (GroundTheory.Global.InfinitePlace.adeleCoord b i y.1, finiteCoord b i y.2)
def fstAddHom : 𝔸[L] →+ InfiniteAdeleRing L where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl
def sndAddHom : 𝔸[L] →+ FiniteAdeleRing (𝓞 L) L where
  toFun := Prod.snd
  map_zero' := rfl
  map_add' _ _ := rfl
end AdeleBaseChange
end
end GroundTheory.Global


