-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCStmt
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCStmt
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:52:51.324545+00:00
-- url     : https://prove2.me/theorems/af62aea0-f9c5-4b20-b168-3dce295a8529
-- title:
--   PBCStmt
-- statement:
--   Definitions and structural lemmas for PBCStmt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBCStmt.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBC
open Formalism.FourierDecayAlt Finset Filter Topology NumberField MeasureTheory
noncomputable section
open Classical
def Lstd (f : ℕ) (R : ℝ) : Submodule ℤ (crystallineComparison.V f) :=
  Submodule.span ℤ (Set.range fun p : Fin f × Bool =>
    (Pi.single p.1 (if p.2 then (R : ℂ) * Complex.I else (R : ℂ)) : crystallineComparison.V f))
def LstdFacts : Prop :=
  ∀ (f : ℕ) (R : ℝ), 0 < R →
    ∃ (_ : DiscreteTopology (Lstd f R)) (_ : IsZLattice ℝ (Lstd f R)),
      ZLattice.covolume (Lstd f R) = R ^ (2 * f) ∧
      ∀ σ : crystallineComparison.V f, σ ∈ crystallineComparison.dualSet (Lstd f R) ↔
        ∀ v, ∃ a b : ℤ, σ v = ((a : ℂ) + (b : ℂ) * Complex.I) / (2 * (R : ℂ))
def LstdSum : Prop :=
  ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ (f : ℕ) (R g : ℝ) (L : Fin f → ℝ), 0 < R → 0 < g → (∀ v, 0 ≤ L v) →
    Summable (fun σ : crystallineComparison.dualSet (Lstd f R) => crystallineComparison.mL C.Kst L (g • (σ : crystallineComparison.V f))) ∧
    ∑' σ : crystallineComparison.dualSet (Lstd f R), crystallineComparison.mL C.Kst L (g • (σ : crystallineComparison.V f)) ≤
      ∏ v, Cs * (1 + (R * L v / g) ^ 2)
section setting
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]
def embV (S : C.HidaSetting E Wp Wq) : E →+ crystallineComparison.V S.f where
  toFun t := fun v => S.σ v t
  map_zero' := by funext v; simp
  map_add' a b := by funext v; simp
def latV (S : C.HidaSetting E Wp Wq) (L : AddSubgroup E) : Submodule ℤ (crystallineComparison.V S.f) :=
  (AddSubgroup.toIntSubmodule L).map (embV S).toIntLinearMap
def thr (S : C.HidaSetting E Wp Wq) (b s : ℕ) (v : Fin S.f) : ℝ :=
  J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s (S.pl v)
end setting
def SizesSup : Prop :=
  ∀ Cs : ℝ, 1 ≤ Cs → ∃ B : ℝ, 1 ≤ B ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
      [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
      [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
      0 < S.G.g1 → 0 < S.G.g2 → S6.Unram E → ∀ b n, 1 ≤ b → 1 ≤ n → (∀ v, 0 < thr S b n v) →
        ∃ R : ℝ, 0 < R ∧
          (∏ _v : Fin S.f, KB.dlB S b n) * (∏ v, Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ (2 * S.f) ≤
            B ^ S.f * S.base.vol b n
def BlockLatV : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
      [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
      [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
      0 < S.G.g1 → 0 < S.G.g2 → S6.Unram E → ∀ b s, 1 ≤ b → 1 ≤ s →
        ∃ (_ : DiscreteTopology (latV S (J.LaB E S.g S.G.r b s)))
          (_ : IsZLattice ℝ (latV S (J.LaB E S.g S.G.r b s))),
          ZLattice.covolume (latV S (J.LaB E S.g S.G.r b s)) = ∏ _v : Fin S.f, KB.dlB S b s ∧
          (∃ (Lm : Submodule ℤ (crystallineComparison.V S.f)) (_ : DiscreteTopology Lm) (_ : IsZLattice ℝ Lm),
            ∀ σ ∈ crystallineComparison.dualSet (latV S (J.LaB E S.g S.G.r b s)), (S.g : ℝ) • σ ∈ Lm) ∧
          ∀ Λ : Fin S.f → ℝ, (∀ v, 0 ≤ Λ v ∧ Λ v ≤ thr S b s v) → S.base.vol b s ≤ 1 →
            Summable (fun σ : crystallineComparison.dualSet (latV S (J.LaB E S.g S.G.r b s)) =>
              crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) ∧
            ∑' σ : crystallineComparison.dualSet (latV S (J.LaB E S.g S.G.r b s)),
              crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f)) ≤ A ^ S.f
end
end Formalism.FourierDecayAlt.P.PBC


