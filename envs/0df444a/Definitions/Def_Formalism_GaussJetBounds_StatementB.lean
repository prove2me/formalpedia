-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_StatementB
-- name    : Formalism_GaussJetBounds_StatementB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:07:30.408446+00:00
-- url     : https://prove2.me/theorems/337cdafe-31e7-4618-86b0-886d5ab383e3
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/StatementB.lean

import Definitions.Def_Formalism_GaussJetBounds_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
def PureFormula : Prop :=
  ∀ (K : Type u) [Field K] (l d N0 N1 : ℕ) [NeZero d], 2 ≤ l →
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (lt : ι → ZMod d) (M : ZV d N0 N1 → ι → K),
      (∀ x i, M x i ≠ 0 → lt i = x.1) →
    ∀ be : MvPowerSeries (ZMod d) K, ∀ (i j : ι) (α β : ℕ), lt i ≠ lt j →
      MvPowerSeries.coeff (pureMon l i j α β) (bSum M be) =
        MvPowerSeries.coeff (Finsupp.single (lt i) (l ^ α) + Finsupp.single (lt j) (l ^ β)) be *
          ∑ ab : Fin N0 × Fin N1, M (lt i, ab.1, ab.2) i ^ (l ^ α) * M (lt j, ab.1, ab.2) j ^ (l ^ β)
def FrobCong : Prop :=
  ∀ (R : Type u) [CommRing R] (l : ℕ), l.Prime → ∀ (ι : Type v) [Fintype ι] (u w : ι → R)
    (j β : ℕ), ∃ r : R,
      (∑ a, u a ^ (l ^ (j + β)) * w a ^ (l ^ β)) - (∑ a, u a ^ (l ^ j) * w a) ^ (l ^ β) = (l : R) * r
def SpecialIndep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (J : ℕ) (j : Fin J → ℕ), Function.Injective j →
    (Matrix.of fun (i a : Fin J) =>
      (MvPolynomial.X a : MvPolynomial (Fin J) (ZMod l)) ^ (l ^ j i)).det ≠ 0
def SpecialRank : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (T : Type) [Fintype T] [DecidableEq T] (J : T → ℕ)
    (j : ∀ t, Fin (J t) → ℕ), (∀ t, Function.Injective (j t)) → ∀ N0 : ℕ,
    (∑ t, J t) ≤ N0 →
    ∃ f : (Σ t, Fin (J t)) → Fin N0, Function.Injective f ∧
      (Matrix.of fun (r c : Σ t, Fin (J t)) =>
        (MvPolynomial.X (r.1, f c) : MvPolynomial (T × Fin N0) (ZMod l)) ^ (l ^ j r.1 r.2)).det ≠ 0
def MinorDeg : Prop :=
  ∀ (R : Type u) [CommRing R] (m p : ℕ) (top : Fin (p + 1) → R) (T : Fin p → Fin m → R),
    ∀ mono ∈ (Matrix.of fun (i c : Fin (p + 1)) =>
        (Fin.cases (fun c => MvPolynomial.C (top c))
          (fun i' c => ∑ k, MvPolynomial.C (T i' k) * MvPolynomial.X (k, c)) i c :
          MvPolynomial (Fin m × Fin (p + 1)) R)).det.support,
      ∀ k : Fin m, (∑ c : Fin (p + 1), mono (k, c)) ≤ 1
end Formalism.DworkPowerSeriesWeights


