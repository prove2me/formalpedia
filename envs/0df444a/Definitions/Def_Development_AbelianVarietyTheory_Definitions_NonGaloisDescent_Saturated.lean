-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_Saturated
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_Saturated
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T03:08:10.974642+00:00
-- url     : https://prove2.me/theorems/1ad82890-9555-5b2a-ac67-d8c4be5ca03e
-- title:
--   Saturated
-- statement:
--   Definitions and structural lemmas for Saturated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/Saturated.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.WachUse
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions GlobalTheory.AdmLoc
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)
def InvBasis : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
  ∃ b : Fin (Module.finrank O ↥T.L.T) → W.DD T, (∀ j, b j ∈ W.NΔ T) ∧ LinearIndependent (LetA O n) b ∧
    W.N T = Submodule.span (LetA O n) (Set.range b)
def Heights : Prop := ∀ (T : LocLat G Qp LL O) (U : ZMod n → Multiset ℤ) (M h : ZMod n → ℕ),
  CrysWith PD W.emb T.ρ U → (∀ i, ∀ u ∈ U i, -(M i : ℤ) ≤ u ∧ u ≤ h i) →
  ∀ i, (∀ x ∈ W.N T, W.Q ^ M i • (letE i : LetA O n) • W.φD T x ∈ W.N T) ∧
    ∀ y ∈ W.N T, W.Q ^ h i • (letE i : LetA O n) • y ∈ W.φpull T
def RankOne : Prop := ∀ (T : LocLat G Qp LL O) (a : ZMod n → ℤ), CrysWith PD W.emb T.ρ (fun i => {a i}) →
  Module.finrank LL T.V = 1 → ∀ i : ZMod n,
    (∀ x ∈ W.φpull T, ∃ y ∈ W.N T,
      W.Q ^ (-a i).toNat • (letE i : LetA O n) • x = W.Q ^ (a i).toNat • (letE i : LetA O n) • y) ∧
    ∀ y ∈ W.N T, ∃ x ∈ W.φpull T,
      W.Q ^ (-a i).toNat • (letE i : LetA O n) • x = W.Q ^ (a i).toNat • (letE i : LetA O n) • y
def Saturated : Prop := ∀ (T' T : LocLat G Qp LL O) (f : LatHom T'.L T.L), IsCrys PD T.ρ → Function.Bijective f.f →
  ∀ x, W.map f x ∈ W.N T → x ∈ W.N T'
def Additive : Prop := ∀ (T T' S : LocLat G Qp LL O) (f : LatHom T.L S.L) (g : LatHom T'.L S.L),
  IsCrys PD T.ρ → IsCrys PD T'.ρ → Function.Bijective (f.f.coprod g.f) →
  (∀ z ∈ S.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) →
  ∀ z ∈ W.N S, ∃ x ∈ W.N T, ∃ y ∈ W.N T', z = W.map f x + W.map g y
def IsC (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra O LL] (c : ℤ → O) : Prop :=
  ∀ a : ℤ, (PD.p : LL) * algebraMap O LL (c a) = 1 - (1 + (PD.p : LL)) ^ a
def SenOp : Prop := ∀ (T : LocLat G Qp LL O) (U : ZMod n → Multiset ℤ), CrysWith PD W.emb T.ρ U →
  ∀ (γ : W.Gam), (W.χΓ γ : O) = 1 + (PD.p : O) → ∀ c : ℤ → O, IsC PD LL c →
  ∃ ν : Module.End O ↥(W.NΔ T), (∀ y : ↥(W.NΔ T), W.γD T γ y - y = W.π₀ • ((ν y : ↥(W.NΔ T)) : W.DD T)) ∧
    (∀ (i : ZMod n) (s : ℕ) (y : ↥(W.NΔ T)), ∃ z ∈ W.N T, (letE i : LetA O n) •
      ((Polynomial.aeval ν (∏ m ∈ ((Finset.range s) ×ˢ (U i).toFinset).image (fun p => (p.1 : ℤ) - p.2),
        (Polynomial.X - Polynomial.C (c m))) y : ↥(W.NΔ T)) : W.DD T) = (W.π₀ + (PD.p : LetA O n)) ^ s • z) ∧
    ∀ (m : ℕ) (b : Fin m → ↥(W.NΔ T)), LinearIndependent (LetA O n) (fun j => (b j : W.DD T)) →
      W.N T = Submodule.span (LetA O n) (Set.range fun j => (b j : W.DD T)) →
      ∀ i : ZMod n, ∃ A : Matrix (Fin m) (Fin m) O,
        A.charpoly = ((U i).map fun u => Polynomial.X - Polynomial.C (c (-u))).prod ∧
        ∀ j, ∃ z ∈ W.N T, (letE i : LetA O n) • (((ν (b j) - ∑ j', A j' j • b j' : ↥(W.NΔ T))) : W.DD T) =
          (W.π₀ + (PD.p : LetA O n)) • z
def QN : Prop := InvBasis W ∧ Heights W ∧ RankOne W ∧ Saturated W ∧ Additive W ∧ SenOp W
end GlobalTheory.WachUse


