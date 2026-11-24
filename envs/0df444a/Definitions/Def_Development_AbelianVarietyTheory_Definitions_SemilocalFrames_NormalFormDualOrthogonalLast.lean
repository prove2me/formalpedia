-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
-- name    : Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T12:47:37.317683+00:00
-- url     : https://prove2.me/theorems/9b361ca9-af5f-4cc1-a324-5a928cbf1ecf
-- title:
--   Normal Form Dual Orthogonal Last
-- statement:
--   Definitions and structural lemmas for Normal Form Dual Orthogonal Last, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/NormalFormDualOrthogonalLast.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat
open scoped Pointwise ENNReal Classical nonZeroDivisors
namespace GlobalTheory.DegCnt
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def ipow (𝔡 : Ideal (𝓞 K)) (n : ℤ) : Submodule (𝓞 K) K :=
  (((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ n : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
def line (A : Submodule (𝓞 K) K) (v : V) : Submodule (𝓞 K) V :=
  A.map ((LinearMap.toSpanSingleton K V v).restrictScalars (𝓞 K))
def GenBy (A B : Submodule (𝓞 K) V) (e : ℕ) : Prop :=
  ∃ t : Finset V, t.card ≤ e ∧ A = B ⊔ Submodule.span (𝓞 K) (t : Set V)
def cf (K : Type) [Field K] [NumberField K] : ℝ := 1 + Real.logb 2 (Module.finrank ℚ K)
def HasOrtho (K : Type) [Field K] [NumberField K] [StarRing K] : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → GlobalTheory.Mass.PD k →
    (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ Formalism.HermitianLatticesTheory.IsUnimodular k L) →
    ∃ I : Submodule (𝓞 K) W, Formalism.HermitianLatticesTheory.IsOrthoLattice k I (Module.finrank K W)
structure NF (H : HermSpace K V) (r : ℕ) where
  F : FlagD H r
  F' : FlagD H r
  j : ℕ
  j_le : j ≤ r
  c : K
  c_norm : c * star c = 1
  T : ℕ
  hT : F.T = T
  hT' : F'.T = T
  same : ∀ a : Fin (r + 1), j ≤ a.val → F'.e a = c • F.e a
  w : Formalism.MainNotions.S.Loc.Pt K j
  sgn : Fin j → ℤˣ
  pair : ∀ a b : Fin j, H.B (F.e (Fin.castLE (j_le.trans (Nat.le_succ r)) a))
    (F'.e (Fin.castLE (j_le.trans (Nat.le_succ r)) b)) = w.mat a b * ((sgn b : ℤ) : K)
  ist : Fin r → V
  ist_e : ∀ a b : Fin r, j ≤ b.val → H.B (F.e a.castSucc) (ist b) = if a = b then 1 else 0
  ist_e' : ∀ a b : Fin r, a.val < j → j ≤ b.val → H.B (F'.e a.castSucc) (ist b) = 0
  normalForm_dual_orthogonal_last : ∀ b : Fin r, j ≤ b.val → H.B F.z (ist b) = 0
  ist_iso : ∀ a b : Fin r, j ≤ a.val → j ≤ b.val → H.B (ist a) (ist b) = 0
  posdef : ∀ σ : K →+* ℂ, F.PosDefAt σ
  𝔡 : Ideal (𝓞 K)
  𝔡_ne : 𝔡 ≠ ⊥
  𝔡_star : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)
namespace NF
variable {H : HermSpace K V} {r : ℕ} (N : NF H r)
def aa (a : Fin r) : Submodule (𝓞 K) K := ipow N.𝔡 (-((r : ℤ) - a.val))
def Ist : Submodule K V := Submodule.span K (N.ist '' {b | N.j ≤ b.val})
def Wt : Submodule K V := perp H (V0 N.F N.F' ⊔ N.Ist)
def Wn : Submodule K V := perp H (N.F.X ⊔ N.F'.X ⊔ N.Ist)
def Pi : Submodule K V := perp H N.Wt
def P0 : Submodule (𝓞 K) V :=
  (⨆ a : Fin r, line (N.aa a) (N.F.e a.castSucc)) ⊔
    (⨆ a : Fin r, ⨆ _ : a.val < N.j, line (N.aa a) (N.F'.e a.castSucc)) ⊔ line 1 N.F.z ⊔
    ⨆ a : Fin r, ⨆ _ : N.j ≤ a.val, line (ipow N.𝔡 ((r : ℤ) - a.val)) (N.ist a)
def Ref (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) V := N.P0 ⊔ (L ⊓ rs (𝓞 K) N.Wn)
def nD (l : ℕ) : ℝ :=
  if h : l ≤ r + 1 then |((Algebra.norm ℚ (Dl N.F N.F' l h) : ℚ) : ℝ)| *
    (Ideal.absNorm N.𝔡 : ℝ) ^ (-(2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a))) else 0
def Del : ℝ := N.nD N.j
def Db : ℝ := ∏ l ∈ (Finset.Icc 1 N.j).filter (fun l => N.nD l ≠ 0), N.nD l
def NT : ℝ := (N.T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K
def R : Subgroup (V ≃ₗ[K] V) := Subgroup.closure {s | N.F.InN (s : V →ₗ[K] V) ∧ N.F'.InN (s : V →ₗ[K] V)}
def fixing (_ : NF H r) (S : Submodule K V) : Subgroup (V ≃ₗ[K] V) := fixingSubgroup (V ≃ₗ[K] V) (S : Set V)
def R1 : Subgroup (V ≃ₗ[K] V) := N.R ⊓ N.fixing (V0 N.F N.F')
def ZI : Subgroup (V ≃ₗ[K] V) := N.R1 ⊓ N.fixing N.Wt
def Rs : Subgroup (V ≃ₗ[K] V) := N.R ⊓ N.fixing N.Wt
def Gam (Λ : Submodule (𝓞 K) V) : Subgroup (V ≃ₗ[K] V) := N.R ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ
def IsTerm (g : ℕ) (Λ : Submodule (𝓞 K) V) : Prop :=
  IsFramed N.F N.F' Λ N.aa ∧ IsAdm N.F N.F' Λ (g : 𝓞 K)
def gI (g : ℕ) (Λ : Submodule (𝓞 K) V) : ℕ := idx (flagPairDefinitePartLattice N.F N.F' Λ) (latLa N.F N.F' Λ (g : 𝓞 K))
def iI (g : ℕ) (Λ : Submodule (𝓞 K) V) : ℕ := idx (latLa N.F N.F' Λ (g : 𝓞 K)) (latTh N.F N.F' Λ)
def bI (Λ : Submodule (𝓞 K) V) : ℕ := bOne N.F N.F' Λ N.j
def om (Λ : Submodule (𝓞 K) V) : ℝ := GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ))) (N.Gam Λ)
def omSum (Q : Submodule (𝓞 K) V → Prop) : ℝ≥0∞ :=
  ∑' o : MulAction.orbitRel.Quotient N.R (Submodule (𝓞 K) V), if Q o.out then ENNReal.ofReal (N.om o.out) else 0
def SameDat (g : ℕ) (Λ₀ Λ : Submodule (𝓞 K) V) : Prop :=
  latL N.F N.F' Λ = latL N.F N.F' Λ₀ ∧ latL N.F' N.F Λ = latL N.F' N.F Λ₀ ∧
    iotaGraph N.F N.F' Λ (g : 𝓞 K) = iotaGraph N.F N.F' Λ₀ (g : 𝓞 K)
def Split (Λ : Submodule (𝓞 K) V) : Prop :=
  latTh N.F N.F' Λ = (Λ ⊓ rs (𝓞 K) N.Wt) ⊔ rs (𝓞 K) (II N.F N.F')
def Near (𝔠 : Ideal (𝓞 K)) (Λ : Submodule (𝓞 K) V) : Prop :=
  𝔠 • N.P0 ≤ Λ ⊓ rs (𝓞 K) N.Pi ∧ 𝔠 • (Λ ⊓ rs (𝓞 K) N.Pi) ≤ N.P0
end NF
def IsDat (H : HermSpace K V) (g : ℕ) (L₀ : Submodule (𝓞 K) V) (j x : ℕ)
    (d : Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) : Prop :=
  GlobalTheory.Mass.IsIntLat H.B.flip d.1 ∧ GlobalTheory.Mass.discN H.B.flip d.1 = GlobalTheory.Mass.discN H.B.flip L₀ ∧
    IsModIso H (g : 𝓞 K) d.1 L₀ d.2 ∧ idx L₀ (fixLat d.2) = x ∧ GenBy L₀ (fixLat d.2) j
def Trip (H : HermSpace K V) (g : ℕ) (L₀ : Submodule (𝓞 K) V) (j x x' : ℕ) :
    Set ((Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V)) :=
  {p | IsDat H g L₀ j x p.1 ∧ IsDat H g L₀ j x' p.2.1 ∧ p.2.2 ∈ isomGrp H ∧ imLat p.2.2 p.2.1.1 = p.1.1 ∧
    ∀ y y' : V, (y, y') ∈ p.2.1.2 ↔ (p.2.2 y, y') ∈ p.1.2}
def fixSp (η : V ≃ₗ[K] V) : Submodule K V := LinearMap.ker ((η : V →ₗ[K] V) - LinearMap.id)
end GlobalTheory.DegCnt


