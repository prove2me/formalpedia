-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_StatementC
-- name    : Formalism_GaussJetBounds_StatementC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:46.388807+00:00
-- url     : https://prove2.me/theorems/ba3ba916-4c0f-4ef7-bebc-b02633be5049
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/StatementC.lean

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
universe u
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
def SpecialRankSpan : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (T : Type) [Fintype T] [DecidableEq T] (J : T → ℕ)
    (j : ∀ t, Fin (J t) → ℕ), (∀ t, Function.Injective (j t)) → ∀ N0 n : ℕ,
    (∑ t, J t) ≤ N0 → (∑ t, J t) ≤ n →
    ∃ f : (Σ t, Fin (J t)) → Fin n, Function.Injective f ∧
      (Matrix.of fun (r c : Σ t, Fin (J t)) =>
        ∑ a : Fin N0, (MvPolynomial.X (Sum.inl (r.1, a)) :
            MvPolynomial ((T × Fin N0) ⊕ (Fin n × Fin N0)) (ZMod l)) ^ (l ^ j r.1 r.2) *
          MvPolynomial.X (Sum.inr (f c, a))).det ≠ 0
def frameM {K : Type u} [Field K] {d N0 N1 : ℕ} (x : ZMod d × Fin N0 × Fin N0 → K) :
    ZV d N0 N1 → ZV d N0 N1 → K :=
  fun z y => if y.1 = z.1 ∧ y.2.2 = z.2.2 then x (z.1, y.2.1, z.2.1) else 0
def FramePure : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d],
    l.Prime → ‖(l : K)‖ < 1 → ∀ (h0 : 0 < N0) (x : ZMod d × Fin N0 × Fin N0 → K), (∀ y, ‖x y‖ ≤ 1) →
    ∀ be : MvPowerSeries (ZMod d) K,
      WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1) - 1) be →
    ∀ (s s' : ZMod d), s ≠ s' → ∀ (k : Fin N0) (b b' : Fin N1) (α β : ℕ),
      (b ≠ b' → MvPowerSeries.coeff (pureMon l ((s, ⟨0, h0⟩, b) : ZV d N0 N1) (s', k, b') α β)
          (bSum (frameM (N1 := N1) x) be) = 0) ∧
      ((if β ≤ α then ‖∑ a : Fin N0, x (s, ⟨0, h0⟩, a) ^ (l ^ (α - β)) * x (s', k, a)‖
          else ‖∑ a : Fin N0, x (s, ⟨0, h0⟩, a) * x (s', k, a) ^ (l ^ (β - α))‖) ≤ ‖(l : K)‖ →
        MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1))
          (pureMon l ((s, ⟨0, h0⟩, b) : ZV d N0 N1) (s', k, b) α β)
          (MvPowerSeries.coeff (pureMon l ((s, ⟨0, h0⟩, b) : ZV d N0 N1) (s', k, b) α β)
            (bSum (frameM (N1 := N1) x) be)))
end Formalism.DworkPowerSeriesWeights


