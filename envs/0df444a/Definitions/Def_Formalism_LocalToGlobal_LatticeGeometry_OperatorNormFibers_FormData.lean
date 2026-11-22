-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_OperatorNormFibers_FormData
-- name    : Formalism_LocalToGlobal_LatticeGeometry_OperatorNormFibers_FormData
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:36.085944+00:00
-- url     : https://prove2.me/theorems/c14eb20e-d67f-4fad-bb02-3a539394d90b
-- title:
--   Form Data
-- statement:
--   Definitions and structural lemmas for Form Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/OperatorNormFibers/FormData.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped ComplexOrder
noncomputable section
namespace Formalism.L2.Geo.ExtensionFiltration
structure FormData (K R Hb : Type) [Field K] [NumberField K] [CommRing R] [Algebra K R] [Group Hb]
    [MulSemiringAction Hb R] where

  W : Type

  Pt : W → Type

  av : W → AbsoluteValue K ℝ
  av_int : ∀ w (a : 𝓞 K), av w (a : K) ≤ 1

  sn : ∀ w, Pt w → R → ℝ
  sn_nonneg : ∀ w y f, 0 ≤ sn w y f
  sn_smul : ∀ w y (a : K) f, sn w y (a • f) = av w a * sn w y f
  sn_add : ∀ w y f g, sn w y (f + g) ≤ max (sn w y f) (sn w y g)
  sn_mul : ∀ w y f g, sn w y (f * g) ≤ sn w y f * sn w y g

  mv : Hb → ∀ w, Pt w → Pt w
  sn_act : ∀ (h : Hb) w y f, sn w y (h • f) = sn w (mv h w y) f

  cusp : Submodule K R
  cusp_act : ∀ (h : Hb) f, f ∈ cusp → h • f ∈ cusp
  cusp_mul : ∀ f u, f ∈ cusp → f * u ∈ cusp

  ip : InfinitePlace K → R → R → ℂ
  ip_add_left : ∀ v f f' g, f ∈ cusp → f' ∈ cusp → g ∈ cusp → ip v (f + f') g = ip v f g + ip v f' g
  ip_add_right : ∀ v f g g', f ∈ cusp → g ∈ cusp → g' ∈ cusp → ip v f (g + g') = ip v f g + ip v f g'
  ip_smul_left : ∀ v (a : K) f g, f ∈ cusp → g ∈ cusp →
    ip v (a • f) g = star (v.embedding a) * ip v f g
  ip_smul_right : ∀ v (a : K) f g, f ∈ cusp → g ∈ cusp → ip v f (a • g) = v.embedding a * ip v f g
  ip_conj : ∀ v f g, f ∈ cusp → g ∈ cusp → ip v g f = star (ip v f g)
  ip_nonneg : ∀ v f, f ∈ cusp → 0 ≤ (ip v f f).re
  ip_act : ∀ v (h : Hb) f g, f ∈ cusp → g ∈ cusp → ip v (h • f) (h • g) = ip v f g

  supv : InfinitePlace K → R → ℝ
  supv_act : ∀ v (h : Hb) u, supv v (h • u) = supv v u
  ip_mul : ∀ v f u, f ∈ cusp → u ∈ cusp →
    (ip v (f * u) (f * u)).re ≤ supv v u ^ 2 * (ip v f f).re
def FormData.restrict {K R G : Type} [Field K] [NumberField K] [CommRing R] [Algebra K R] [Group G]
    [MulSemiringAction G R] (D : FormData K R G) (S : Subgroup G) : FormData K R S where
  W := D.W
  Pt := D.Pt
  av := D.av
  av_int := D.av_int
  sn := D.sn
  sn_nonneg := D.sn_nonneg
  sn_smul := D.sn_smul
  sn_add := D.sn_add
  sn_mul := D.sn_mul
  mv := fun h => D.mv (h : G)
  sn_act := fun h => D.sn_act (h : G)
  cusp := D.cusp
  cusp_act := fun h => D.cusp_act (h : G)
  cusp_mul := D.cusp_mul
  ip := D.ip
  ip_add_left := D.ip_add_left
  ip_add_right := D.ip_add_right
  ip_smul_left := D.ip_smul_left
  ip_smul_right := D.ip_smul_right
  ip_conj := D.ip_conj
  ip_nonneg := D.ip_nonneg
  ip_act := fun v h => D.ip_act v (h : G)
  supv := D.supv
  supv_act := fun v h => D.supv_act v (h : G)
  ip_mul := D.ip_mul
structure FormDataG (K R Hb : Type) [Field K] [NumberField K] [CommRing R] [Algebra K R] [Group Hb]
    [MulSemiringAction Hb R] extends FormData K R Hb where
  ip_posDef : ∀ v (m : ℕ) (e : Fin m → R), (∀ a, e a ∈ cusp) → LinearIndependent K e →
    (Matrix.of fun a c => ip v (e a) (e c)).PosDef
end Formalism.L2.Geo.ExtensionFiltration


