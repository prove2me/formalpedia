-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:16.132605+00:00
-- url     : https://prove2.me/theorems/68ac7404-fd0b-46e2-b650-73ca89bbc50d
-- title:
--   Block Poly Level Move
-- statement:
--   Definitions and structural lemmas for Block Poly Level Move, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/BlockPolyLevelMove.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial
section Lattice
variable {E : Type} [Field E] [NumberField E]
def unitLat (E : Type) [Field E] [NumberField E] (n : ℕ) : GenLat E n := ⟨stdLat E n⟩
def blockLat {n₁ n₂ : ℕ} (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) : GenLat E (n₁ + n₂) :=
  ⟨Λ₁.La.comap (LinearMap.funLeft (𝓞 E) E (Fin.castAdd n₂)) ⊓
    Λ₂.La.comap (LinearMap.funLeft (𝓞 E) E (Fin.natAdd n₁))⟩
example {n₁ n₂ : ℕ} (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (v : Fin (n₁ + n₂) → E) :
    v ∈ (blockLat Λ₁ Λ₂).La ↔
      (fun i => v (Fin.castAdd n₂ i)) ∈ Λ₁.La ∧ (fun j => v (Fin.natAdd n₁ j)) ∈ Λ₂.La := Iff.rfl
example (n₁ n₂ : ℕ) : (blockLat (unitLat E n₁) (unitLat E n₂)).La = (unitLat E (n₁ + n₂)).La := by
  ext v
  change ((fun i => v (Fin.castAdd n₂ i)) ∈ stdLat E n₁ ∧ (fun j => v (Fin.natAdd n₁ j)) ∈ stdLat E n₂) ↔
    v ∈ stdLat E (n₁ + n₂)
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left]
  exact ⟨fun h i => Fin.addCases (motive := fun i => v i ∈ (1 : Submodule (𝓞 E) E)) h.1 h.2 i,
    fun h => ⟨fun i => h _, fun j => h _⟩⟩
end Lattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
def LatAdm (l : Level H) (bad : ℕ) {n : ℕ} (Λ : GenLat E n) : Prop :=
  Λ.Unimod ∧ Λ.TrivAt bad ∧ Λ.TrivAt l.M
def letL (Dw : Datum H) (n₁ n₂ : ℕ) (ℓ : LtN Dw n₁) : LtN Dw (n₁ + n₂) := ⟨ℓ.1, ℓ.2.1, Fin.castAdd n₂ ℓ.2.2⟩
def letR (Dw : Datum H) (n₁ n₂ : ℕ) (ℓ : LtN Dw n₂) : LtN Dw (n₁ + n₂) := ⟨ℓ.1, ℓ.2.1, Fin.natAdd n₁ ℓ.2.2⟩
def blockPoly {K : Type} [Field K] {n₁ n₂ : ℕ} (P₁ : MvPolynomial (LtN Dw n₁) K)
    (P₂ : MvPolynomial (LtN Dw n₂) K) : MvPolynomial (LtN Dw (n₁ + n₂)) K :=
  rename (letL Dw n₁ n₂) P₁ * rename (letR Dw n₁ n₂) P₂
def blockDat {K : Type} [Field K] {n₁ n₂ : ℕ} (w₁ : (Fin n₁ → LevQ Dw l) → K) (w₂ : (Fin n₂ → LevQ Dw l) → K) :
    (Fin (n₁ + n₂) → LevQ Dw l) → K :=
  fun q => w₁ (fun i => q (Fin.castAdd n₂ i)) * w₂ (fun j => q (Fin.natAdd n₁ j))
def levMap (l : Level H) (g : Dw.La →ₗ[𝓞 E] Dw.La) : LevQ Dw l →ₗ[𝓞 E] LevQ Dw l :=
  Submodule.mapQ _ _ g (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)
def moveDat {K : Type} {n : ℕ} (g : Dw.La →ₗ[𝓞 E] Dw.La) (w : (Fin n → LevQ Dw l) → K) :
    (Fin n → LevQ Dw l) → K :=
  fun q => w (fun b => levMap l g (q b))
variable (Xo : Moduli Dw l) (c : Coeff l)
def IsBeta (Dw : Datum H) {l : Level H} (c : Coeff l) {n : ℕ} (Λ : GenLat E n) (β : c.F) : Prop :=
  β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β
def FreeOfLevel (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n : ℕ) (Λ : GenLat E n), LatAdm l bad Λ →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ a →
    ∀ (w : (Fin n → LevQ Dw l) → c.F) (β : c.F), β ≠ 0 →
    ∀ (N N' : ℕ), Λ.LevOK N l.M → Λ.LevOK N' l.M →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v v' : S),
      ShortValAt Xo c nab w Λ β N P y v → (ShortValAt Xo c nab w Λ β N' P y v' ↔ v' = v)
def BlockProduct (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂), LatAdm l bad Λ₁ → LatAdm l bad Λ₂ →
    ∀ N : ℕ, Λ₁.LevOK N l.M → Λ₂.LevOK N l.M →
    (LatAdm l bad (blockLat Λ₁ Λ₂) ∧ (blockLat Λ₁ Λ₂).LevOK N l.M) ∧
    ∀ (a₁ a₂ : (E →+* ℂ) × ℕ → ℕ) (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F),
      P₁ ∈ harmL c Λ₁ a₁ → P₂ ∈ harmL c Λ₂ a₂ →
      blockPoly P₁ P₂ ∈ harmL c (blockLat Λ₁ Λ₂) (a₁ + a₂) ∧
      ∀ (w₁ : (Fin n₁ → LevQ Dw l) → c.F) (w₂ : (Fin n₂ → LevQ Dw l) → c.F)
        (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v₁ v₂ v : S),
        ShortValAt Xo c nab w₁ Λ₁ 1 N P₁ y v₁ → ShortValAt Xo c nab w₂ Λ₂ 1 N P₂ y v₂ →
        (ShortValAt Xo c nab (blockDat w₁ w₂) (blockLat Λ₁ Λ₂) 1 N (blockPoly P₁ P₂) y v ↔ v = v₁ * v₂)
def BlockBeta (Dw : Datum H) {l : Level H} (c : Coeff l) (bad : ℕ) : Prop :=
  (∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂), LatAdm l bad Λ₁ → LatAdm l bad Λ₂ →
    ∀ β₁ β₂ β : c.F, IsBeta Dw c Λ₁ β₁ → IsBeta Dw c Λ₂ β₂ →
      (IsBeta Dw c (blockLat Λ₁ Λ₂) β ↔ ∃ ζ : c.F, IsOfFinOrder ζ ∧ β = ζ * (β₁ * β₂))) ∧
  ∀ (n₁ n₂ : ℕ) (Λ₂ : GenLat E n₂), LatAdm l bad Λ₂ →
    IsBeta Dw c (unitLat E n₁) 1 ∧
      ∀ β : c.F, IsBeta Dw c (blockLat (unitLat E n₁) Λ₂) β ↔ IsBeta Dw c Λ₂ β
def LevelMove (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n : ℕ) (Λ : GenLat E n), LatAdm l bad Λ →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ a →
    ∀ (w : (Fin n → LevQ Dw l) → c.F) (β : c.F), β ≠ 0 →
    ∀ N : ℕ, Λ.LevOK N l.M →
    ∀ (g gA : Dw.La →ₗ[𝓞 E] Dw.La) (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S),
      levR (g, gA) y y' →
      ∀ v : S, ShortValAt Xo c nab (moveDat g w) Λ β N P y' v ↔ ShortValAt Xo c nab w Λ β N P y v
def LevelMoveClass (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n : ℕ) (Λ : GenLat E n), LatAdm l bad Λ →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ a →
    ∀ (x₀ : Fin n → Dw.La) (β : c.F), β ≠ 0 →
    ∀ N : ℕ, Λ.LevOK N l.M →
    ∀ (g gA : Dw.La →ₗ[𝓞 E] Dw.La), (∀ u v : Dw.La, (l.M : ℤ) ∣ Dw.EF (g u) (g v) - Dw.EF u v) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S), levR (g, gA) y y' →
      ∀ v : S, ShortValAt Xo c nab (x0Dat c x₀) Λ β N P y' v ↔
        ShortValAt Xo c nab (x0Dat c fun b => g (x₀ b)) Λ β N P y v
def ShortLaws [StarRing (𝓞 E)] : Prop :=
  (∀ nab : NabV Xo c, IsNab Xo c nab → ∀ bad : ℕ,
    FreeOfLevel Xo c nab bad ∧ BlockProduct Xo c nab bad ∧ LevelMove Xo c nab bad) ∧
  ∀ bad : ℕ, BlockBeta Dw c bad
end GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility


