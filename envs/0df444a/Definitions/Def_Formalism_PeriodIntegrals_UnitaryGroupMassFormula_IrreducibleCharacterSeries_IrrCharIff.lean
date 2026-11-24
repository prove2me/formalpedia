-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T17:56:04.269466+00:00
-- url     : https://prove2.me/theorems/33a36c20-526b-4419-adbb-919cb33b1ac1
-- title:
--   Irr Char Iff
-- statement:
--   Definitions and structural lemmas for Irr Char Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IrreducibleCharacterSeries/IrrCharIff.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_HCDisjointO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
namespace PI.SerBridgeGLW
def IrrSys : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (I : Type) [Fintype I] (ρ : I → FDRep ℂ G),
    (∀ i, Simple (ρ i)) → (∀ i j, RepIso (ρ i).ρ (ρ j).ρ → i = j) →
    (∀ σ : FDRep ℂ G, Simple σ → ∃ i, RepIso σ.ρ (ρ i).ρ) →
    (∀ χ : G → ℂ, IsIrrChar χ ↔ ∃ i, χ = (ρ i).character) ∧
    (∀ i j, (ρ i).character = (ρ j).character → i = j)
def SerSum : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (cv : LabelConv (ZMod g)) (r : ℕ) (I : Type) [Fintype I]
    (ρ : I → FDRep ℂ (GL (Fin r) (ZMod g))),
    (∀ i, Simple (ρ i)) → (∀ i j, RepIso (ρ i).ρ (ρ j).ρ → i = j) →
    (∀ σ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple σ → ∃ i, RepIso σ.ρ (ρ i).ρ) →
    ∀ f, eSerC cv.ι cv.gen r f =
      ∑ i, (open Classical in if InSeries cv.ι cv.gen (ρ i).character f then zIdem (ρ i) else 0)
def SerStep : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (cv : LabelConv (ZMod g)) (r : ℕ) (V : FDRep ℂ (GL (Fin r) (ZMod g))),
    Simple V → ∀ f, InSeries cv.ι cv.gen V.character f ↔ HasLabel cv V f
def ConjChar : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (V : FDRep ℂ G) (x : G), star (V.character x) = V.character x⁻¹
def IrrCharIff : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ), IsIrrChar χ ↔ ∃ V : FDRep ℂ G, Simple V ∧ χ = V.character
open Classical in

def FrobSum : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (ι : Type) [Fintype ι] [DecidableEq ι] (s : ℕ)
    (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (V : FDRep ℂ (GL ι K)),
    IsConstituent V (hcRep K b lam) ↔
      ∑ p : parab K b, V.character p.1 * star (∏ c, (lam c).character (levi K b c p)) ≠ 0
open Classical in

def BlockSum : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (c : Fin s → ℕ)
    (e : ∀ j, {i // b i = j} ≃ Fin (c j)) (χ : GL (Fin r) K → ℂ) (ψ : ∀ j, GL (Fin (c j)) K → ℂ),
    (∀ x y, χ (y * x * y⁻¹) = χ x) → (∀ j x y, ψ j (y * x * y⁻¹) = ψ j x) →
    ∑ p : parab K b, χ p.1 * star (∏ j, ψ j (glEquiv K (e j) (levi K b j p))) =
      ∑ p : GL (Fin r) K, (if IsParab c p then
        χ p * star (∏ j, onMat (ψ j) (blkOf (r := r) c j (p : Matrix (Fin r) (Fin r) K))) else 0)
open Classical in

def CuspIff : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (κ : Type) [Fintype κ] [DecidableEq κ] (d : ℕ)
    (e : κ ≃ Fin d) (τ : FDRep ℂ (GL κ K)),
    IsCuspidal K τ ↔ ∀ a, 0 < a → a < d →
      ∑ u : GL (Fin d) K, (if u ∈ (unipBlock d a : Set (GL (Fin d) K)) then
        τ.character ((glEquiv K e).symm u) else 0) = 0
def GreenFwd : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (cv : LabelConv (ZMod g)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : ℕ)
    (e : κ ≃ Fin d) (τ : FDRep ℂ (GL κ (ZMod g))) (k : ℕ),
    (labCusp cv.gen d k).natDegree = d →
    GreenAt cv.ι (fun x => τ.character ((glEquiv (ZMod g) e).symm x)) k →
    HasCuspLabel cv τ (labCusp cv.gen d k)
def GreenBwd : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (cv : LabelConv (ZMod g)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : ℕ)
    (e : κ ≃ Fin d) (τ : FDRep ℂ (GL κ (ZMod g))) (P : (ZMod g)[X]),
    HasCuspLabel cv τ P →
    ∃ k, labCusp cv.gen d k = P ∧ (labCusp cv.gen d k).natDegree = d ∧
      GreenAt cv.ι (fun x => τ.character ((glEquiv (ZMod g) e).symm x)) k
end PI.SerBridgeGLW


