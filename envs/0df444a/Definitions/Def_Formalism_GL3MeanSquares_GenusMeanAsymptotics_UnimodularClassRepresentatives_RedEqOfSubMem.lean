-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RedEqOfSubMem
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RedEqOfSubMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:51:10.623801+00:00
-- url     : https://prove2.me/theorems/7a734d41-e02a-4730-94f8-4b4119b57dc2
-- title:
--   Red Eq Of Sub Mem
-- statement:
--   Definitions and structural lemmas for Red Eq Of Sub Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RedEqOfSubMem.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.PinG
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
def red (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    ↥(locF 𝔭 (spanO b)) →ₗ[𝓞 K] (κ → 𝓞 K ⧸ extP K 𝔭 ^ k) :=
  (qE b (extP K 𝔭 ^ k)).toLinearMap ∘ₗ (quotLocF h𝔭 (spanO b) k).symm.toLinearMap ∘ₗ
    Submodule.mkQ _
def bM (b : Basis κ K V) (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (j : κ) : ↥(locF 𝔭 (spanO b)) :=
  ⟨b j, le_locF 𝔭 _ (Submodule.subset_span (Set.mem_range_self j))⟩
variable [Fact (IsFixF K F)]
omit [Fact (IsFixF K F)] in
theorem map_mem {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule (𝓞 K) V} {g : V ≃ₗ[K] V}
    (hg : g ∈ autSub h M) {x : V} (hx : x ∈ M) : g x ∈ M := by
  have h2 : Formalism.HermitianLatticesTheory.gmap g M = M := hg.2
  rw [← h2]
  exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
def gM {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule (𝓞 K) V} {g : V ≃ₗ[K] V} (hg : g ∈ autSub h M) :
    ↥M →ₗ[𝓞 K] ↥M :=
  ((g : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict fun _ hx => map_mem hg hx
def gMat {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    [𝔭.IsPrime] (k : ℕ) {g : V ≃ₗ[K] V} (hg : g ∈ autSub h (locF 𝔭 (spanO b))) :
    Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Matrix.of fun i j => red b h𝔭 k (gM hg (bM b 𝔭 j)) i
end Formalism.HermitianLattices.Ext.L3.PinG


