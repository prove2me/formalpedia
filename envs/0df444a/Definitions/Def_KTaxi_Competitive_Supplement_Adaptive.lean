-- Prove2me | Definitions.Def_KTaxi_Competitive_Supplement_Adaptive
-- name    : KTaxi_Competitive_Supplement_Adaptive
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:31:16.263506+00:00
-- url     : https://prove2.me/theorems/fb2a0837-1107-44b7-8a4a-ec8aac73aaac
-- title:
--   Appendices A–B — unrestricted integer strategies and visible adaptive play
-- statement:
--   A visible adaptive online adversary receives the completed public rounds and its own current taxi configuration. It either stops or chooses a request $(r,s)$ together with its own serving taxi, before the algorithm responds. A public round records the request, the algorithm’s paid configuration before pickup, its serving label, and its configuration after the free passenger leg and any further paid movement. No private seed, memory or ranking is exposed.
--
--   For the integer-line lower bound, the general causal policy returns arbitrary configurations before pickup and after drop-off, a serving label, and a finite nonnegative surcharge for detours. Its round cost is
--   $$\sum_\ell |x_\ell-z_\ell|+|z_i-r|+\sum_\ell |(z[i\leftarrow s])_\ell-w_\ell|+\delta.$$
--   The comparator pays only $|y_j-r|$. The surcharge records actual path length beyond endpoint distances; dropping detours can only decrease online cost. There is no laziness assumption. Private randomness lives on an arbitrary probability space. Costs are nonnegative integrals over its seed, with a finite horizon and optional earlier stopping.
--
--   For Algorithm 1, a replay adapter reconstructs public configurations and requests from past serving labels alone and embeds this adversary into the published game. It ignores every internal-state component, including the hidden permutation, and gives the comparator only ordinary serving moves. The construction reuses the published algorithm and cost functions exactly.
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, STOC 2027 submission #96 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, §2, PDF p. 4 (printed p. 3); Appendix A, PDF pp. 17–19 (printed pp. 16–18); Appendix B, PDF pp. 19–22 (printed pp. 18–21)

import Mathlib
import Definitions.Def_KTaxi_Competitive_Model
import Definitions.Def_KTaxi_Competitive_Algorithm1
import Definitions.Def_KTaxi_Competitive_Supplement_PrivatePolicy

open MeasureTheory
open scoped ENNReal NNReal

namespace KTaxi.Competitive.Supplement

universe u

/-- A visible round: request, paid configuration before pickup, serving label, and
configuration after the free passenger leg and any further paid moves. Private state and
private random seeds are absent. -/
abbrev VisibleRound (V : Type*) (k : ℕ) :=
  (V × V) × (Fin k → V) × Fin k × (Fin k → V)

/-- The adversary sees only completed visible rounds and its own current configuration.
It chooses the request AND its own serving taxi before the current randomized response.
It may stop. Extra comparator repositioning is unnecessary for these lower bounds. -/
structure VisibleAdversary (V : Type*) (k : ℕ) where
  move : List (VisibleRound V k) → (Fin k → V) → Option ((V × V) × Fin k)

/-- Endpoint action on the integer line: arbitrary paid moves before pickup, serving taxi,
arbitrary paid moves after drop-off, and a nonnegative detour surcharge. The latter records
any excess of actual path lengths over endpoint distances. No laziness is required. -/
abbrev PaidAction (k : ℕ) := (Fin k → ℤ) × Fin k × (Fin k → ℤ) × ℝ≥0

/-- Unrestricted history-dependent randomized strategy on ℤ, including continuous private
randomness and paid moves. The common initial configuration is part of its information.
Visible histories are countable, so per-history seed measurability suffices for measurable
finite-horizon costs against every VisibleAdversary. -/
abbrev IntegerStrategy (k : ℕ) :=
  PrivatePolicy ((Fin k → ℤ) × List (VisibleRound ℤ k)) (ℤ × ℤ) (PaidAction k)

/-- Realized hard costs on a fixed private seed. Both serving choices are causal.
All taxi moves except the passenger leg are charged. Fuel bounds the horizon, including
adversaries which would otherwise continue forever. -/
noncomputable def integerPathCost {k : ℕ} (A : IntegerStrategy.{u} k)
    (D : VisibleAdversary ℤ k) (ω : A.Seed) (x₀ : Fin k → ℤ) :
    ℕ → (Fin k → ℤ) → (Fin k → ℤ) → List (VisibleRound ℤ k) → ℝ≥0∞ × ℝ≥0∞
  | 0, _, _, _ => (0, 0)
  | T + 1, x, y, h =>
    match D.move h y with
    | none => (0, 0)
    | some (q, j) =>
      let a := A.act ω (x₀, h) q
      let z := a.1
      let i := a.2.1
      let w := a.2.2.1
      let δ := a.2.2.2
      let next := integerPathCost A D ω x₀ T w (Function.update y j q.2)
        (h ++ [(q, z, i, w)])
      ((∑ l, edist (x l) (z l)) + edist (z i) q.1 +
        (∑ l, edist ((Function.update z i q.2) l) (w l)) + (δ : ℝ≥0∞) + next.1,
       edist (y j) q.1 + next.2)

/-- Nonnegative expectations on the arbitrary private probability space; no Bochner
integrability convention or countable-support assumption is used. -/
noncomputable def integerAlgCost {k : ℕ} (A : IntegerStrategy.{u} k)
    (D : VisibleAdversary ℤ k) (T : ℕ) (x₀ : Fin k → ℤ) : ℝ≥0∞ :=
  letI := A.seedSpace
  ∫⁻ ω, (integerPathCost A D ω x₀ T x₀ x₀ []).1 ∂A.law

noncomputable def integerAdvCost {k : ℕ} (A : IntegerStrategy.{u} k)
    (D : VisibleAdversary ℤ k) (T : ℕ) (x₀ : Fin k → ℤ) : ℝ≥0∞ :=
  letI := A.seedSpace
  ∫⁻ ω, (integerPathCost A D ω x₀ T x₀ x₀ []).2 ∂A.law

/-- Replay only the public serving labels of the base game's outcomes. The first
component S is ignored throughout: in particular Algorithm 1's rank is NEVER inspected. -/
noncomputable def replay {V : Type*} {S : Type} {k : ℕ} (D : VisibleAdversary V k)
    (x₀ y₀ : Fin k → V) (outcomes : List (S × Fin k)) :
    (Fin k → V) × (Fin k → V) × List (VisibleRound V k) :=
  outcomes.foldl (fun st o =>
    match D.move st.2.2 st.2.1 with
    | none => st
    | some (q, j) =>
      let w := Function.update st.1 o.2 q.2
      (w, Function.update st.2.1 j q.2, st.2.2 ++ [(q, st.1, o.2, w)])) (x₀, y₀, [])

/-- Embed a visible adversary into the published model, with ordinary serving moves
(z is exactly the current comparator configuration). This is a restriction of the base
adversary model, necessary for lower bounds. -/
noncomputable def toBaseAdversary {V : Type*} {S : Type} {k : ℕ} (D : VisibleAdversary V k)
    (x₀ y₀ : Fin k → V) : Adversary V k S where
  move outcomes :=
    let st := replay D x₀ y₀ outcomes
    match D.move st.2.2 st.2.1 with
    | none => none
    | some (q, j) => some (q.1, q.2, st.2.1, j)

end KTaxi.Competitive.Supplement


