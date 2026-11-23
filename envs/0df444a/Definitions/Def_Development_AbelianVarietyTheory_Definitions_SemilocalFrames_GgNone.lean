-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
-- name    : Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:30.2918+00:00
-- url     : https://prove2.me/theorems/5b881261-a966-4de4-addf-97491d4a4984
-- title:
--   Gg None
-- statement:
--   Definitions and structural lemmas for Gg None, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/GgNone.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise
namespace GlobalTheory.HL
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
structure Coord (P : LocNG.FPair H r) (S : Frames M.L r k) where
  e : V ≃ₗ[E] S.V
  h_eq : ∀ x y, S.h (e x) (e y) = H.h x y
  f_eq : ∀ a, S.f a = e (P.A.f a)
  f'_eq : ∀ a, S.f' a = e (P.B.f a)
  es_eq : ∀ a, S.es a = e (P.A.es a)
  es'_eq : ∀ a, S.es' a = e (P.B.es a)
  T_eq : (S.T : F) = P.A.T
  T'_eq : (S.T' : F) = P.B.T
  gg_none : M.split = none → S.gg = false
  gg_some : ∀ g, M.split = some g → S.gg = true ∧ S.ϖ = g.q
namespace Coord
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
def grp : (V ≃ₗ[E] V) ≃* S.GLV where
  toFun g := (c.e.symm.trans g).trans c.e
  invFun g := (c.e.trans g).trans c.e.symm
  left_inv g := by ext v; simp
  right_inv g := by ext v; simp
  map_mul' a b := by ext v; simp
def lat (Λ : Submodule M.L.O V) : Submodule M.L.O S.V :=
  Λ.map ((c.e : V →ₗ[E] S.V).restrictScalars M.L.O)
def inn (f : Fin (r + 1) → V) (L : Submodule M.L.O (H.Wb f)) : Submodule M.L.O S.V :=
  c.lat ((L.comap ((H.mkW f).restrictScalars M.L.O)).map ((H.perp (H.X f)).subtype.restrictScalars M.L.O))
def dat (d : LocNG.Datum P) : S.Datum :=
  (c.inn P.A.f d.L, c.inn P.B.f d.L',
    {p | ∃ (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))), p = (c.e x', c.e x) ∧
      ((M.split = none ∧ H.mkW P.B.f x' ∈ d.L' ∧ H.mkW P.A.f x ∈ d.L) ∨
        (H.mkW P.B.f x', H.mkW P.A.f x) ∈ d.io)})
end Coord
end GlobalTheory.HL


