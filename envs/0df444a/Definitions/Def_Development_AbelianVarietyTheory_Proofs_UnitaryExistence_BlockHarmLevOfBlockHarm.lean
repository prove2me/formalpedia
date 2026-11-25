-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:16.551015+00:00
-- url     : https://prove2.me/theorems/a00736c0-3f74-486c-b7de-44f25fe12a5c
-- title:
--   Block Harm Lev Of Block Harm
-- statement:
--   Definitions and structural lemmas for Block Harm Lev Of Block Harm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BlockHarmLevOfBlockHarm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockProductLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BaseClassMove
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
namespace GlobalTheory.ShortLawsCompare
open NumberField MvPolynomial Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke
section Lattice
variable {E : Type} [Field E] [NumberField E]
variable {n₁ n₂ : ℕ}
end Lattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
section Beta
variable (c : Coeff l)
end Beta
section Level
variable {Xo : Moduli Dw l} {c : Coeff l}
end Level
section Objects
variable (c : Coeff l) {n₁ n₂ : ℕ}
end Objects
variable (Xo : Moduli Dw l) (c : Coeff l)
def CarryN (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n : ℕ) (Λ : GenLat E n) (N N' : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (w : (Fin n → LevQ Dw l) → c.F) (β : c.F),
    BlockProductLattices.LatOK bad l.M Λ → Λ.LevOK N l.M → Λ.LevOK N' l.M → P ∈ harmL c Λ a → β ≠ 0 →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S),
      (∃ v, ShortValAt Xo c nab w Λ β N P y v) → ∃ v', ShortValAt Xo c nab w Λ β N' P y v'
def CarryBlock (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (N : ℕ) (a₁ a₂ : (E →+* ℂ) × ℕ → ℕ)
    (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F)
    (w₁ : (Fin n₁ → LevQ Dw l) → c.F) (w₂ : (Fin n₂ → LevQ Dw l) → c.F),
    BlockProductLattices.LatOK bad l.M Λ₁ → BlockProductLattices.LatOK bad l.M Λ₂ → Λ₁.LevOK N l.M → Λ₂.LevOK N l.M →
    P₁ ∈ harmL c Λ₁ a₁ → P₂ ∈ harmL c Λ₂ a₂ →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S),
      (∃ v₁, ShortValAt Xo c nab w₁ Λ₁ 1 N P₁ y v₁) → (∃ v₂, ShortValAt Xo c nab w₂ Λ₂ 1 N P₂ y v₂) →
      ∃ v, ShortValAt Xo c nab (BlockProductLattices.blockDat c w₁ w₂) (BlockProductLattices.blockLat Λ₁ Λ₂) 1 N (BlockProductLattices.blockPol c P₁ P₂) y v
def CarryMove (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (w : (Fin n → LevQ Dw l) → c.F) (β : c.F) (g gA : Dw.La →ₗ[𝓞 E] Dw.La),
    BlockProductLattices.LatOK bad l.M Λ → Λ.LevOK N l.M → P ∈ harmL c Λ a → β ≠ 0 →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S), levR (g, gA) y y' →
      ((∃ v', ShortValAt Xo c nab (BlockLatticeAdmissibility.moveDat g w) Λ β N P y' v') ↔ ∃ v, ShortValAt Xo c nab w Λ β N P y v)
def ValuesExist (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (w : (Fin n → LevQ Dw l) → c.F) (β : c.F),
    BlockProductLattices.LatOK bad l.M Λ → Λ.LevOK N l.M → P ∈ harmL c Λ a → β ≠ 0 →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃ v, ShortValAt Xo c nab w Λ β N P y v
def BlockHarmLev (Dw : Datum H) (c : Coeff l) (bad : ℕ) : Prop :=
  ∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) (N : ℕ) (a₁ a₂ : (E →+* ℂ) × ℕ → ℕ)
    (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F),
    BlockProductLattices.LatOK bad l.M Λ₁ → BlockProductLattices.LatOK bad l.M Λ₂ → Λ₁.LevOK N l.M → Λ₂.LevOK N l.M →
    P₁ ∈ harmL c Λ₁ a₁ → P₂ ∈ harmL c Λ₂ a₂ →
      BlockProductLattices.blockPol c P₁ P₂ ∈ harmL c (BlockProductLattices.blockLat Λ₁ Λ₂) (a₁ + a₂)
variable [StarRing (𝓞 E)] {Xo c} {nab : NabV Xo c}
def LawsAt (nab : NabV Xo c) (bad : ℕ) : Prop :=
  BlockLatticeAdmissibility.FreeOfLevel Xo c nab bad ∧ BlockLatticeAdmissibility.BlockProduct Xo c nab bad ∧ BlockLatticeAdmissibility.LevelMove Xo c nab bad ∧
    BlockLatticeAdmissibility.BlockBeta Dw c bad
end GlobalTheory.ShortLawsCompare


