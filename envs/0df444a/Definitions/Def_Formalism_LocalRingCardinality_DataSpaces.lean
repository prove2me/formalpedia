-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
-- name    : Formalism_LocalRingCardinality_DataSpaces
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:31.286053+00:00
-- url     : https://prove2.me/theorems/28e3d73f-3771-48f5-aa26-84af81a1d337
-- title:
--   Data Spaces
-- statement:
--   Definitions and structural lemmas for Data Spaces, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/DataSpaces.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions
open NumberField IsDedekindDomain
open scoped TensorProduct
structure CMData (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] : Prop where
  cmUnram : Formalism.HermitianLatticesTheory.IsCMUnram E
  totReal : NumberField.IsTotallyReal F
  deg2 : Module.finrank F E = 2
  fixed : ∀ a : E, star a = a ↔ a ∈ (algebraMap F E).range
def CMData.sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : CMData F E) : E →ₐ[F] E :=
  { starRingEnd E with
    commutes' := fun a => (hc.fixed (algebraMap F E a)).2 ⟨a, rfl⟩ }
structure HSpace (E : Type) [Field E] [NumberField E] [StarRing E] where
  V : Type
  [acg : AddCommGroup V]
  [modE : Module E V]
  [modO : Module (𝓞 E) V]
  [tower : IsScalarTower (𝓞 E) E V]
  [fd : FiniteDimensional E V]

  hT : V →ₗ⋆[E] V →ₗ[E] E
  herm : hT.IsSymm
  nondeg : hT.Nondegenerate
  rank : ℕ
  rank_eq : Module.finrank E V = rank

  frame : Module.Basis (Fin rank) E V

  sig : (E →+* ℂ) → ℕ × ℕ

  L0 : Submodule (𝓞 E) V
  standardTuple_isLattice : Submodule.IsLattice E L0
  baseLattice_isUnimodular : Formalism.HermitianLatticesTheory.IsUnimodular hT L0
attribute [instance] HSpace.acg HSpace.modE HSpace.modO HSpace.tower HSpace.fd
namespace HSpace
variable {E : Type} [Field E] [NumberField E] [StarRing E]
def gram (S : HSpace E) : Matrix (Fin S.rank) (Fin S.rank) E :=
  fun i j => S.hT (S.frame i) (S.frame j)
def hD (S : HSpace E) (x y : S.V) : E := S.hT y x
def SigOK (S : HSpace E) : Prop :=
  ∀ τ : E →+* ℂ, Formalism.UG.HasSignature (S.gram.map τ) (S.sig τ).1 (S.sig τ).2
def IsDefinite (S : HSpace E) : Prop :=
  ∀ τ : E →+* ℂ, S.sig τ = (S.rank, 0) ∨ S.sig τ = (0, S.rank)
def IsPosDef (S : HSpace E) : Prop := ∀ τ : E →+* ℂ, S.sig τ = (S.rank, 0)
def IsDefOneSign (S : HSpace E) : Prop :=
  (∀ τ : E →+* ℂ, S.sig τ = (S.rank, 0)) ∨ (∀ τ : E →+* ℂ, S.sig τ = (0, S.rank))
def IsIsomEmb (S S' : HSpace E) (ι : S.V →ₗ[E] S'.V) : Prop :=
  ∀ x y, S'.hT (ι x) (ι y) = S.hT x y
end HSpace
def sigYD (R : Ranks) (j : ℕ) : ℕ × ℕ := (R.rankY j - (R.m - j) / 2, (R.m - j) / 2)
structure Spaces (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] where
  cm : CMData F E

  T : ℕ
  T_prime : T.Prime

  X : ℕ → HSpace E
  X_sig : ∀ j, (X j).SigOK
  X_rank : ∀ j, j ≤ R.m → (X j).rank = R.N j
  X_def : ∀ j, j ≤ R.m → (X j).IsDefinite

  X' : HSpace E
  X'_sig : X'.SigOK
  X'_rank : X'.rank = R.rankX'
  iX' : X'.V →ₗ[E] (X R.m).V
  iX'_isom : HSpace.IsIsomEmb X' (X R.m) iX'
  z : (X R.m).V
  z_anis : (X R.m).hT z z ≠ 0
  z_orth : ∀ x, (X R.m).hT (iX' x) z = 0

  Y : ℕ → HSpace E
  Y_sig : ∀ j, (Y j).SigOK
  Y_rank : ∀ j, j ≤ R.m → (Y j).rank = R.rankY j

  iXY : ∀ j, (X j).V →ₗ[E] (Y j).V
  iXY_isom : ∀ j, j < R.m → HSpace.IsIsomEmb (X j) (Y j) (iXY j)

  eYm : X'.V ≃ₗ[E] (Y R.m).V
  eYm_isom : HSpace.IsIsomEmb X' (Y R.m) eYm.toLinearMap

  zm : (Y 0).V
  zm_norm : (Y 0).hT zm zm = -(T : E)
  zm_orth : ∀ x, (Y 0).hT (iXY 0 x) zm = 0
  hypE : Fin R.rS → (Y 0).V
  hypF : Fin R.rS → (Y 0).V
  hyp_ee : ∀ i i', (Y 0).hT (hypE i) (hypE i') = 0
  hyp_ff : ∀ i i', (Y 0).hT (hypF i) (hypF i') = 0
  hyp_ef : ∀ i i', (Y 0).hT (hypE i) (hypF i') = if i = i' then 1 else 0
  hyp_orthX : ∀ i x, (Y 0).hT (iXY 0 x) (hypE i) = 0 ∧ (Y 0).hT (iXY 0 x) (hypF i) = 0
  hyp_orthz : ∀ i, (Y 0).hT zm (hypE i) = 0 ∧ (Y 0).hT zm (hypF i) = 0

  baseSpace_signature_eq : ∀ τ : E →+* ℂ, (Y 0).sig τ = R.sigY0

  W : ℕ → HSpace E
  W_sig : ∀ j, (W j).SigOK
  W_rank : ∀ j, 1 ≤ j → j ≤ R.m → (W j).rank = R.r
  W_sigval : ∀ j, 1 ≤ j → j ≤ R.m → ∀ τ : E →+* ℂ, (W j).sig τ = R.sigW j

  baseSpace_isometric_graded : ∀ j, 1 ≤ j → j ≤ R.m → ∃ e : Fin (Y 0).rank ≃ Fin (W j).rank,
    ∃ g : GL (Fin (W j).rank) (E ⊗[F] FiniteAdeleRing (𝓞 F) F),
      Formalism.UG.cT (Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F))
                (g : Matrix (Fin (W j).rank) (Fin (W j).rank) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *
        (((Y 0).gram.reindex e e).map (Formalism.UG.inclE (FiniteAdeleRing (𝓞 F) F))) *
        (g : Matrix (Fin (W j).rank) (Fin (W j).rank) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      (W j).gram.map (Formalism.UG.inclE (FiniteAdeleRing (𝓞 F) F))

  V : ℕ → HSpace E
  V_sig : ∀ j, (V j).SigOK
  V_rank : ∀ j, 1 ≤ j → j ≤ R.m → (V j).rank = R.nV
  Vneg : ℕ → Bool
  V_std : ∀ j, 1 ≤ j → j ≤ R.m →
    Formalism.HermitianLatticesTheory.IsOrthoLattice (if Vneg j then -(V j).hT else (V j).hT) (V j).L0 R.nV
namespace Spaces
def bridge_hD : Prop := ∀ (E : Type) [Field E] [NumberField E] [StarRing E]
  (S : HSpace E) (x y : S.V), S.hD x y = star (S.hT x y)
def bridge_sigRank : Prop := ∀ (E : Type) [Field E] [NumberField E] [StarRing E]
  (S : HSpace E), S.SigOK → ∀ τ : E →+* ℂ, (S.sig τ).1 + (S.sig τ).2 = S.rank
end Spaces
variable (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E]
def BaseSpacePosDef : Prop := ∀ S : Spaces R F E, (S.X 0).IsPosDef
def FactXmDef : Prop := ∀ S : Spaces R F E, S.X'.IsDefinite ∧ (S.Y R.m).IsDefinite ∧
  ∀ τ : E →+* ℂ, (S.X R.m).sig τ = (R.N R.m, 0) ↔ S.X'.sig τ = (R.rankX', 0)
def FactVSig : Prop := ∀ S : Spaces R F E, ∀ j, 1 ≤ j → j ≤ R.m → ∀ τ : E →+* ℂ,
  (S.V j).sig τ = if S.Vneg j then (0, R.nV) else (R.nV, 0)
def FactWmPosDef : Prop := ∀ S : Spaces R F E, (S.W R.m).IsPosDef
def FactSigYD : Prop := sigYD R 0 = R.sigY0 ∧ sigYD R R.m = (R.rankY R.m, 0)
end Formalism.BasicNotions
end


