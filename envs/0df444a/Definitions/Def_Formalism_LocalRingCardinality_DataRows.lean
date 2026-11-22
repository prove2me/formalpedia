-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_DataRows
-- name    : Formalism_LocalRingCardinality_DataRows
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:13.5128+00:00
-- url     : https://prove2.me/theorems/f4e4463d-a64f-4d6f-a2a0-b6dfa75f085f
-- title:
--   Data Rows
-- statement:
--   Definitions and structural lemmas for Data Rows, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/DataRows.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.BasicNotions.Rows
structure OLat (O : Type) [CommRing O] (φ : O →+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] where
  gen : Finset V
  span_top : Submodule.span ℂ (gen : Set V) = ⊤
namespace OLat
variable {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V]
def carrier (L : OLat O φ V) : Set V :=
  {x | ∃ c : V → O, x = ∑ v ∈ L.gen, φ (c v) • v}
end OLat
structure Places (LL : Type) [Field LL] where
  Pl : Type
  val : Pl → AddValuation LL (WithTop ℤ)
  conj : Pl → Pl
  conj_conj : ∀ w, conj (conj w) = w
  resChar : Pl → ℕ
  resChar_prime : ∀ w, (resChar w).Prime
  ramIdx : Pl → ℕ
  ramIdx_pos : ∀ w, 0 < ramIdx w

  val_surj : ∀ w (n : ℤ), ∃ x : LL, val w x = ((n : ℤ) : WithTop ℤ)

  val_resChar : ∀ w, val w ((resChar w : ℕ) : LL) = (((ramIdx w : ℕ) : ℤ) : WithTop ℤ)
def unitRule {LL : Type} [Field LL] (P : Places LL) (w : P.Pl) (x : ℚ) : ℚ :=
  (P.ramIdx w : ℚ) * x
structure Data (R : Ranks) where

  LL : Type
  [instLL : Field LL]
  embLL : LL →+* ℂ
  places : Places LL

  O : Type
  [instO : CommRing O]
  OtoLL : O →+* LL

  Tau : Type
  [instTau : Fintype Tau]
  card_Tau : Fintype.card Tau = R.f

  Tup : Type
  mu0 : Tup
  muStar : Tup
  muStar' : Tup
  muAt : places.Pl → Tup
  muAt_conj : ∀ w, muAt (places.conj w) = muAt w

  muTw : places.Pl → Tup
  muTw_conj : ∀ w, muTw (places.conj w) = muTw w
  muAt_or : ∀ w, muAt w = mu0 ∨ muAt w = muTw w

  EE : Type
  [instEE : NormedAddCommGroup EE]
  [instEEi : InnerProductSpace ℂ EE]
  [instEEf : FiniteDimensional ℂ EE]
  Drows : ℕ
  onb : OrthonormalBasis (Fin Drows) ℂ EE
  Dall : ℕ
  delp : ℝ
  delp_le_one : delp ≤ 1
  D_eq : (Drows : ℝ) = (1 - delp) * Dall

  EE0 : Type
  [instEE0 : NormedAddCommGroup EE0]
  [instEE0i : InnerProductSpace ℂ EE0]
  [instEE0f : FiniteDimensional ℂ EE0]
  D0 : ℕ
  onb0 : OrthonormalBasis (Fin D0) ℂ EE0

  FT : Type
  [instFT : Fintype FT]
  [instFTd : DecidableEq FT]
  ft : Fin Drows → FT
  ft0 : Fin D0 → FT
  Dstar : ℝ

  Amb : Tup → Type
  [instAmb : ∀ μ, NormedAddCommGroup (Amb μ)]
  [instAmbi : ∀ μ, InnerProductSpace ℂ (Amb μ)]
  [instAmbf : ∀ μ, FiniteDimensional ℂ (Amb μ)]

  Mult : Tup → ℕ → Type
  [instMult : ∀ μ j, NormedAddCommGroup (Mult μ j)]
  [instMulti : ∀ μ j, InnerProductSpace ℂ (Mult μ j)]
  [instMultf : ∀ μ j, FiniteDimensional ℂ (Mult μ j)]
  multZero : ∀ μ, Mult μ 0 ≃ₗᵢ[ℂ] EE
  multTop : ∀ μ, Mult μ R.m ≃ₗᵢ[ℂ] Amb μ

  io : ∀ μ j, Mult μ (j + 1) →ₗ[ℂ] Mult μ j

  Mtilde : ∀ μ, OLat O (embLL.comp OtoLL) (Amb μ)

  eOp : ∀ μ, Amb μ →ₗ[ℂ] Amb μ
  eOp_idem : ∀ μ, eOp μ ∘ₗ eOp μ = eOp μ

  eOp_sa : ∀ μ, (eOp μ).IsSymmetric
  restRowsFiniteGroupCard : ℕ
  restRowsFiniteGroupCard_pos : 0 < restRowsFiniteGroupCard

  Word : Type

  Mu : Word → Type
  [instMu : ∀ u, NormedAddCommGroup (Mu u)]
  [instMui : ∀ u, InnerProductSpace ℂ (Mu u)]
  [instMuf : ∀ u, FiniteDimensional ℂ (Mu u)]
  perCol : ∀ u (μ : Tup), Mu u → Amb μ → ℂ

  Bu : ∀ u, Mu u → EE → ℂ

  ze : Word → Tup → LLˣ
  rowsRest_wordColumnUnit_baseTuple : ∀ u, ze u mu0 = 1

  Mj : ℕ → Type
  [instMj : ∀ j, NormedAddCommGroup (Mj j)]
  [instMji : ∀ j, InnerProductSpace ℂ (Mj j)]
  [instMjf : ∀ j, FiniteDimensional ℂ (Mj j)]

  MjLat : ∀ j, OLat O (embLL.comp OtoLL) (Mj j)

  kaBig : ∀ j, Tau → Fin (R.sigW j).1 → ℤ
  kaSmall : ∀ j, Tau → Fin (R.sigW j).2 → ℤ

  Mt : Tup → ℕ → Type
  [instMt : ∀ μ j, NormedAddCommGroup (Mt μ j)]
  [instMti : ∀ μ j, InnerProductSpace ℂ (Mt μ j)]
  [instMtf : ∀ μ j, FiniteDimensional ℂ (Mt μ j)]
  MtLat : ∀ μ j, OLat O (embLL.comp OtoLL) (Mt μ j)

  MtL : Tup → ℕ → Type
  [instMtL : ∀ μ j, AddCommGroup (MtL μ j)]
  [instMtLm : ∀ μ j, Module LL (MtL μ j)]
  jMt : ∀ μ j, MtL μ j →ₛₗ[embLL] Mt μ j
  jMt_basis : ∀ μ j, ∀ b : Module.Basis (Module.Free.ChooseBasisIndex LL (MtL μ j)) LL (MtL μ j),
    LinearIndependent ℂ (fun i => jMt μ j (b i)) ∧ Submodule.span ℂ (Set.range (fun i => jMt μ j (b i))) = ⊤
  MtLat_sub : ∀ μ j, ∀ x ∈ (MtLat μ j).gen, x ∈ Set.range (jMt μ j)

  eMt : ∀ μ j, Mt μ j →ₗ[ℂ] Mt μ j
  eMt_idem : ∀ μ j, eMt μ j ∘ₗ eMt μ j = eMt μ j
  eMt_sa : ∀ μ j, (eMt μ j).IsSymmetric

  eMt_LL : ∀ μ j (x : MtL μ j), ∃ y : MtL μ j, jMt μ j y = eMt μ j (jMt μ j x)

  thetaP : ∀ μ j, Mt μ j →ₗ[ℂ] Mj j

  isot : ∀ j, FT → Submodule ℂ (Mj j)

  lamP : Tup → ℕ → FT → ℝ

  Ij : Tup → ℕ → places.Pl → ℤ
  jw : Tup → ℕ → places.Pl → ℤ

  etaJ : ℕ → places.Pl → ℚ

  etaJ_nonneg : ∀ j w, 0 ≤ etaJ j w

  shaLen : ℕ → ℕ → ℚ

  shaLen_nonneg : ∀ l e, 0 ≤ shaLen l e
attribute [instance] Data.instLL Data.instO Data.instTau Data.instEE Data.instEEi Data.instEEf
  Data.instAmb Data.instAmbi Data.instAmbf Data.instMult Data.instMulti Data.instMultf
  Data.instMu Data.instMui Data.instMuf Data.instMj Data.instMji Data.instMjf Data.instMt Data.instMti
  Data.instMtf Data.instMtL Data.instMtLm Data.instEE0 Data.instEE0i Data.instEE0f Data.instFT Data.instFTd
namespace Data
variable {R : Ranks} (D : Data R)
def phiO : D.O →+* ℂ := D.embLL.comp D.OtoLL
def downTo (μ : D.Tup) : (j : ℕ) → D.Mult μ j →ₗ[ℂ] D.Mult μ 0
  | 0 => LinearMap.id
  | j + 1 => (downTo μ j).comp (D.io μ j)
noncomputable def iota (μ : D.Tup) : D.Amb μ →ₗ[ℂ] D.EE :=
  (D.multZero μ).toLinearEquiv.toLinearMap ∘ₗ D.downTo μ R.m ∘ₗ
    (D.multTop μ).symm.toLinearEquiv.toLinearMap
noncomputable def thetaUp (μ : D.Tup) : D.EE →ₗ[ℂ] D.Amb μ := LinearMap.adjoint (D.iota μ)
def V0 (μ : D.Tup) : Submodule ℂ (D.Amb μ) := LinearMap.range (D.eOp μ)
noncomputable def Usp (μ : D.Tup) : Submodule ℂ (D.Amb μ) := D.V0 μ ⊓ LinearMap.ker (D.iota μ)
noncomputable def Qsp (μ : D.Tup) : Submodule ℂ (D.Amb μ) := D.V0 μ ⊓ (D.Usp μ)ᗮ
noncomputable def LamSet (μ : D.Tup) : Set (D.Amb μ) :=
  (fun x => (D.Qsp μ).starProjection x) '' ((D.Mtilde μ).carrier ∩ (D.V0 μ : Set (D.Amb μ)))
noncomputable def RRset (μ : D.Tup) : Set D.EE := D.iota μ '' D.LamSet μ
noncomputable def thetaT (μ : D.Tup) (j : ℕ) : D.Mj j →ₗ[ℂ] D.Mt μ j :=
  LinearMap.adjoint (D.thetaP μ j)
noncomputable def Zj (μ : D.Tup) (j : ℕ) : Submodule ℂ (D.Mt μ j) := LinearMap.range (D.thetaT μ j)
noncomputable def TjSet (μ : D.Tup) (j : ℕ) : Set (D.Mt μ j) :=
  (fun x => D.eMt μ j ((D.Zj μ j).starProjection x)) '' (D.MtLat μ j).carrier
def nRows (π : D.FT) : ℕ := Fintype.card {σ : Fin D.Drows // D.ft σ = π}
def nRows0 (π : D.FT) : ℕ := Fintype.card {σ : Fin D.D0 // D.ft0 σ = π}
def EEpart (π : D.FT) : Submodule ℂ D.EE := Submodule.span ℂ (D.onb '' {σ | D.ft σ = π})
def IsotypicPart (π : D.FT) : Submodule ℂ D.EE0 := Submodule.span ℂ (D.onb0 '' {σ | D.ft0 σ = π})
def zeC (u : D.Word) (μ : D.Tup) : ℂ := D.embLL (D.ze u μ : D.LL)
def Aj (j : ℕ) (w : D.places.Pl) : ℤ :=
  D.Ij (D.muAt w) j w + D.Ij (D.muAt w) j (D.places.conj w) + D.jw (D.muAt w) j w
def VV (l : ℕ) : ℚ := ∑ e ∈ Finset.Ico 1 R.t, D.shaLen l e
end Data
def BuDef {R : Ranks} (D : Data R) : Prop :=
  ∀ u (φ : D.Mu u) (F : D.Amb D.mu0), F ∈ D.V0 D.mu0 → D.perCol u D.mu0 φ F = D.Bu u φ (D.iota D.mu0 F)
def LamPDef {R : Ranks} (D : Data R) : Prop :=
  ∀ μ j, 1 ≤ j → j ≤ R.m → ∀ σ, ∀ x ∈ D.isot j σ, D.thetaP μ j (D.thetaT μ j x) = ((D.lamP μ j σ : ℝ) : ℂ) • x
def DelpNonneg {R : Ranks} (D : Data R) : Prop := 0 ≤ D.delp
def AIntegral {R : Ranks} (D : Data R) : Prop :=
  ∀ μ x, x ∈ (D.Mtilde μ).carrier → ((D.restRowsFiniteGroupCard : ℂ) • D.eOp μ x) ∈ (D.Mtilde μ).carrier
def ZeUnit {R : Ranks} (D : Data R) : Prop :=
  ∀ u w, D.places.val w (D.ze u (D.muAt w) : D.LL) = 0 ∧
    D.places.val (D.places.conj w) (D.ze u (D.muAt w) : D.LL) = 0
def IsotInternal {R : Ranks} (D : Data R) : Prop :=
  ∀ j, 1 ≤ j → j ≤ R.m → DirectSum.IsInternal (D.isot j)
def IsotRank {R : Ranks} (D : Data R) : Prop :=
  ∀ j, 1 ≤ j → j ≤ R.m → ∀ π, Module.finrank ℂ (D.isot j π) = D.nRows0 π
def FactKaBlocks : Prop :=
  ∀ R : Ranks, ∀ j, 1 ≤ j → j ≤ R.m → (R.sigW j).1 = (R.k - 1) + j ∧ (R.sigW j).2 = R.m - j
def FactShimRange : Prop :=
  ∀ R : Ranks, ∀ j, 1 ≤ j → j ≤ R.m - 1 → 1 ≤ (R.sigW j).1 ∧ (R.sigW j).1 < R.r
def FactQZ : Prop :=
  ∀ (R : Ranks) (D : Data R) (μ : D.Tup),
    LinearMap.range (D.thetaUp μ) ≤ D.V0 μ → D.Qsp μ = LinearMap.range (D.thetaUp μ)
def FactBuDetermined : Prop :=
  ∀ (R : Ranks) (D : Data R), BuDef D → (∀ x : D.EE, ∃ F ∈ D.V0 D.mu0, D.iota D.mu0 F = x) →
    ∀ B' : ∀ u, D.Mu u → D.EE → ℂ,
      (∀ u φ F, F ∈ D.V0 D.mu0 → D.perCol u D.mu0 φ F = B' u φ (D.iota D.mu0 F)) → B' = D.Bu
def FactLamPNonneg : Prop :=
  ∀ (R : Ranks) (D : Data R), LamPDef D → ∀ μ j, 1 ≤ j → j ≤ R.m → ∀ σ, D.isot j σ ≠ ⊥ → 0 ≤ D.lamP μ j σ
def FactDleDall : Prop := ∀ (R : Ranks) (D : Data R), DelpNonneg D → D.Drows ≤ D.Dall
def FactZeMu0 : Prop := ∀ (R : Ranks) (D : Data R) (u : D.Word), D.zeC u D.mu0 = 1
def FactAjConj : Prop :=
  ∀ (R : Ranks) (D : Data R), ∀ j w,
    D.Aj j (D.places.conj w) - D.Aj j w =
      D.jw (D.muAt w) j (D.places.conj w) - D.jw (D.muAt w) j w
end Formalism.BasicNotions.Rows


