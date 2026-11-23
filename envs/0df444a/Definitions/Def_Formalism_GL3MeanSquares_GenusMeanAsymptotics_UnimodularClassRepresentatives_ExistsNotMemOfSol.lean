-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:06:28.421035+00:00
-- url     : https://prove2.me/theorems/96c99cf2-3647-4dcc-9bbe-449ed741ac8f
-- title:
--   Exists Not Mem Of Sol
-- statement:
--   Definitions and structural lemmas for Exists Not Mem Of Sol, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNotMemOfSol.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
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
namespace Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms
section col
variable {A : Type*} [CommRing A] [StarRing A] {m : Type} [Fintype m] [DecidableEq m]
def colU : (m → A) ≃ Matrix m Unit A where
  toFun x := Matrix.of fun i _ => x i
  invFun X := fun i => X i ()
  left_inv _ := rfl
  right_inv _ := rfl
end col
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
abbrev fm {A : Type*} [CommRing A] [StarRing A] (H : Matrix m m A) (x y : m → A) : A :=
  star x ⬝ᵥ (H *ᵥ y)
section star
variable {A : Type*} [CommRing A] [StarRing A]
end star
def Qc (𝔭 : Ideal (𝓞 F)) (k c : ℕ) (H : Matrix m m (𝓞 K)) (x : m → 𝓞 K ⧸ extP K 𝔭 ^ k) : Prop :=
  ∃ j, (star x ᵥ* H.map (mkk K 𝔭 k)) j ∉ idQ K 𝔭 k (c + 1)
def nkQ (𝔭 : Ideal (𝓞 F)) (k c : ℕ) (H : Matrix m m (𝓞 K)) (n : 𝓞 F) : ℕ :=
  Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // Qc 𝔭 k c H x ∧
    fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)}
def nkM (𝔭 : Ideal (𝓞 F)) (k : ℕ) (H : Matrix m m (𝓞 K)) (n : 𝓞 F) : ℕ :=
  Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)}
end Formalism.HermitianLattices.Ext.L3.hermitianFormColumns


