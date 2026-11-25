-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
-- name    : GroundTheory_AutomorphicForms_SphericalTriangular
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T12:21:21.561224+00:00
-- url     : https://prove2.me/theorems/3676db05-535e-566b-9e1e-4501b4b9a299
-- title:
--   Spherical Triangular
-- statement:
--   Definitions and structural lemmas for Spherical Triangular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake
import Theorems.Thm_GroundTheory_Automorphic_Cartan_existsUnique_mem_doubleCoset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra ValuativeRel
open scoped ValuativeRel
namespace Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable (F) in

def Bdd (t : ℤ) (x : F) : Prop := valuation F x ≤ valuation F (uniformizer F : F) ^ t
def tailEmb {m : ℕ} (hm : m ≤ n) (j : Fin m) : Fin n := ⟨n - m + j, by omega⟩
def tailSum (ν : Fin n → ℤ) {m : ℕ} (hm : m ≤ n) : ℤ := ∑ j : Fin m, ν (tailEmb hm j)
variable (F n) in

def cartanType (g : GL (Fin n) F) : Fin n → ℤ :=
  (Cartan.existsUnique_mem_doubleCoset F n g).exists.choose
def ell (l : Fin n → ℤ) : ℤ := ∑ m : Fin (n + 1), tailSum l (Nat.lt_succ_iff.1 m.2)
variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]
end Spherical
end GroundTheory.Automorphic


