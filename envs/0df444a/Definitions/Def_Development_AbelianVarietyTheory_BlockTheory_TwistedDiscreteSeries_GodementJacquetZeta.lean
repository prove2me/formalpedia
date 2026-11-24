-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_GodementJacquetZeta
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_GodementJacquetZeta
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:26:16.965799+00:00
-- url     : https://prove2.me/theorems/9491fbd3-d1f4-4954-970c-e933a744942e
-- title:
--   Godement Jacquet Zeta
-- statement:
--   Definitions and structural lemmas for Godement Jacquet Zeta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/GodementJacquetZeta.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_inSupport_detRep
import Theorems.Thm_GlobalTheory_SmGL_isSpherical_detRep
import Theorems.Thm_GlobalTheory_SmGL_isUnram_absPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix MeasureTheory
namespace GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces
def FinInSupport {F n Y : Type} [Field F] [Fintype n] [DecidableEq n] [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (GL n F) Y) (χ : Fˣ →* ℂˣ) : Prop :=
  ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ n) (a : Fin s), d a = 1 ∧
    ∃ (Z : Type) (_ : AddCommGroup Z) (_ : Module ℂ Z)
      (ρ : Representation ℂ (Levi F fun a => Fin (d a)) Z),
      ρ.IsIrreducible ∧ IsSubquotient ρ (jacU e τ) ∧
        ∀ (g : GL (Fin (d a)) F) (z : Z),
          ρ (Pi.mulSingle a g) z = (χ (GeneralLinearGroup.det g) : ℂ) • z
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]
def IsLevelOneConstituent (σ : Representation ℂ (GL n k) V) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (GL n 𝓀[k]) Y) : Prop :=
  τ.IsIrreducible ∧ ∃ f : Y →ₗ[ℂ] V, Function.Injective f ∧
    ∀ (g : GL n 𝒪[k]) (y : Y),
      σ (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) (f y) =
        f (τ (GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g) y)
def HasTamePart (μ : kˣ →* ℂˣ) (χ : 𝓀[k]ˣ →* ℂˣ) : Prop :=
  ∀ u : 𝒪[k]ˣ, μ (Units.map (algebraMap 𝒪[k] k).toMonoidHom u) =
    χ (Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom u)
def AvoidsTame (σ : Representation ℂ (GL n k) V) (χ : 𝓀[k]ˣ →* ℂˣ) : Prop :=
  ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (GL n 𝓀[k]) Y),
    IsLevelOneConstituent σ τ ∧ ¬ FinInSupport τ χ ∧ ¬ FinInSupport τ χ⁻¹
def TypedPlace (σ : Representation ℂ (GL n k) V) (μ : kˣ →* ℂˣ) : Prop :=
  ∃ χ : 𝓀[k]ˣ →* ℂˣ, HasTamePart μ χ⁻¹ ∧ AvoidsTame σ χ
def TwistPlace (σ : Representation ℂ (GL n k) V) (μ : kˣ →* ℂˣ) : Prop :=
  IsSpherical σ ∧ ¬ IsUnram μ
abbrev blockSizes (r t j : ℕ) : Fin (j + 1) → ℕ := Fin.cons r fun _ => t
theorem sum_blockSizes (r t j : ℕ) : ∑ a, blockSizes r t j a = r + j * t := by
  simp [Fin.sum_univ_succ]
def chainLevi {r : ℕ} (t : ℕ) {j : ℕ} (σ : Representation ℂ (GL (Fin r) k) V)
    (μ : Fin j → kˣ →* ℂˣ) :
    Representation ℂ (Levi k fun a => Fin (blockSizes r t j a)) V :=
  twist (σ.comp (Pi.evalMonoidHom (fun a => GL (Fin (blockSizes r t j a)) k) 0))
    (∏ i : Fin j, (detChar (Fin (blockSizes r t j i.succ)) (μ i)).comp
      (Pi.evalMonoidHom (fun a => GL (Fin (blockSizes r t j a)) k) i.succ))
def chain {r : ℕ} (t : ℕ) {j : ℕ} (σ : Representation ℂ (GL (Fin r) k) V) (μ : Fin j → kˣ →* ℂˣ) :=
  parInd (stdBlocks (blockSizes r t j) (sum_blockSizes r t j)) (chainLevi t σ μ)
def NoHighTwist (π : Representation ℂ (GL n k) V) (μ : kˣ →* ℂˣ) (t : ℕ) : Prop :=
  ∀ e : ℝ, ((t : ℝ) + 1) / 2 ≤ e →
    ¬ InSupport π (μ * absPow k (e : ℂ)) ∧ ¬ InSupport π (μ * absPow k (-(e : ℂ))) ∧
    ¬ InSupport π (μ⁻¹ * absPow k (e : ℂ)) ∧ ¬ InSupport π (μ⁻¹ * absPow k (-(e : ℂ)))
def NoUnramTwist (π : Representation ℂ (GL n k) V) (μ : kˣ →* ℂˣ) : Prop :=
  ∀ ν : kˣ →* ℂˣ, IsUnram ν → ¬ InSupport π (μ * ν)
variable [MeasurableSpace k] [BorelSpace k]
def gjIntegrand (π : Representation ℂ (GL n k) V) (Φ : Matrix n n k → ℂ) (v : V)
    (l : smoothPart π.dual) (s : ℂ) (g : GL n k) : ℂ :=
  Φ g.val * (l : Module.Dual ℂ V) (π g v) *
    (absPow k (s + ((Fintype.card n : ℂ) - 1) / 2) (GeneralLinearGroup.det g) : ℂ)
def gjZeta (ν : Measure k) (π : Representation ℂ (GL n k) V) (Φ : Matrix n n k → ℂ) (v : V)
    (l : smoothPart π.dual) (s : ℂ) : ℂ :=
  ∫ g, gjIntegrand π Φ v l s g ∂(volGL ν n)
def IsGJFactor (ν : Measure k) (π : Representation ℂ (GL n k) V) (P : Polynomial ℂ) : Prop :=
  P.eval 0 = 1 ∧
  (∀ Φ ∈ SB (Matrix n n k), ∀ (v : V) (l : smoothPart π.dual),
    ∃ (c : ℝ) (N : ℕ) (Q : Polynomial ℂ), ∀ s : ℂ, c < s.re →
      Integrable (gjIntegrand π Φ v l s) (volGL ν n) ∧
      gjZeta ν π Φ v l s * P.eval ((resCard k : ℂ) ^ (-s)) * ((resCard k : ℂ) ^ (-s)) ^ N =
        Q.eval ((resCard k : ℂ) ^ (-s))) ∧
  ∃ (m : ℕ) (Φ : Fin m → Matrix n n k → ℂ) (v : Fin m → V) (l : Fin m → smoothPart π.dual) (c : ℝ),
    (∀ i, Φ i ∈ SB (Matrix n n k)) ∧ ∀ s : ℂ, c < s.re →
      (∑ i, gjZeta ν π (Φ i) (v i) (l i) s) * P.eval ((resCard k : ℂ) ^ (-s)) = 1
end Local
def ChainSupport : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V)
    (μs : Fin j → kˣ →* ℂˣ) (μ : kˣ →* ℂˣ),
    IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ →
    (∀ i, IsSmoothChar (μs i) ∧ IsUnitaryChar (μs i)) → IsSmoothChar μ → IsUnitaryChar μ →
    (TypedPlace σ μ ∨ TwistPlace σ μ ∨ (IsSpherical σ ∧ r ≤ t)) →
    (chain t σ μs).IsIrreducible ∧ IsUnitarisable (chain t σ μs) ∧ NoHighTwist (chain t σ μs) μ t
def RamifiedSupport : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V)
    (μ : kˣ →* ℂˣ),
    IsSmooth σ → σ.IsIrreducible → IsSmoothChar μ → (TypedPlace σ μ ∨ TwistPlace σ μ) →
    NoUnramTwist σ μ
def LocalFactors : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    (∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V)
      (μ : kˣ →* ℂˣ),
      IsSmooth σ → σ.IsIrreducible → IsSmoothChar μ → (TypedPlace σ μ ∨ TwistPlace σ μ) →
      IsGJFactor ν (twist σ (detChar (Fin r) μ⁻¹)) 1 ∧
        IsGJFactor ν (twist (contra σ) (detChar (Fin r) μ)) 1) ∧
    (∀ (μ' μ : kˣ →* ℂˣ) (χ' χ : 𝓀[k]ˣ →* ℂˣ), HasTamePart μ' χ'⁻¹ → HasTamePart μ χ⁻¹ → χ' ≠ χ →
      IsGJFactor ν (detRep (Fin 1) (μ' / μ)) 1 ∧ IsGJFactor ν (detRep (Fin 1) (μ / μ')) 1) ∧
    ∀ μ'₀ μ₀ ξ : kˣ →* ℂˣ, IsUnram μ'₀ → IsUnram μ₀ →
      (μ'₀ * ξ) / (μ₀ * ξ) = μ'₀ / μ₀ ∧ IsUnram ((μ'₀ * ξ) / (μ₀ * ξ))
def GoodSupport : Prop := ChainSupport ∧ RamifiedSupport ∧ LocalFactors
section Examples
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
example {N : ℕ} (μ : kˣ →* ℂˣ) : ¬ NoUnramTwist (detRep (Fin (N + 1)) μ) μ := fun h =>
  h _ (isUnram_absPow k _) (inSupport_detRep μ 0)
example {N : ℕ} {μ : kˣ →* ℂˣ} (h : ¬ IsUnram μ) : TwistPlace (detRep (Fin N) (1 : kˣ →* ℂˣ)) μ :=
  ⟨isSpherical_detRep fun _ _ => rfl, h⟩
end Examples
end GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces


