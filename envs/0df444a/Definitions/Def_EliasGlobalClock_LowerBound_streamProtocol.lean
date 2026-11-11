-- Prove2me | Definitions.Def_EliasGlobalClock_LowerBound_streamProtocol
-- name    : EliasGlobalClock_LowerBound_streamProtocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:21.498272+00:00
-- url     : https://prove2.me/theorems/fa3d6ae5-278f-4477-9759-e48853d3195b
-- title:
--   Anonymous GlobalClock stream laws and the first-success coupling
-- statement:
--   Let $\Omega$ be the space of shared random inputs. An anonymous GlobalClock rule is represented by a probability kernel $\mu(w,y)$ on infinite binary attempt streams, depending only on its own wake-up slot $w$ and shared input $y\in\Omega$. Coordinates within a stream may have arbitrary dependence, retaining private memory and all earlier attempts. For an analyst-labelled finite population with wake-up assignment $w_u$, the conditional joint law is
--
--   $$\bigotimes_u \mu(w_u,y).$$
--
--   An attempt is masked to zero at every slot $t\le w_u$. A singleton is a slot with exactly one attempted transmission. The actual execution is constructed from these streams by keeping attempts through the first singleton and making every later slot silent. Its first-success time is the minimum singleton time, or $+\infty$ if there is none. Auxiliary failure means no singleton in the specified interval $(t_0,t_0+\ell]$.
--
--   Every source protocol induces these kernels by running with perpetual FAIL feedback and its full private tape. Conversely a sampled stream can be followed one slot at a time. Binary feedback has only the FAIL path until termination, so this representation preserves every possible first-success event. Labels, the population and other players' histories are never inputs to the rule. This interface supports arbitrary shared random strings and is not restricted to the paper's upper-bound algorithm.
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), printed pp.1, 8–9, PDF pp.2, 9–10, §1 and §4.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Mathlib

open MeasureTheory ProbabilityTheory

namespace EliasGlobalClock.LowerBound

/-- Full all-FAIL attempt streams. Their coordinates need not be independent. -/
abbrev AttemptStream := ℕ → Bool

/-- A single anonymous rule, indexed only by its own wake-up time and the shared
random input. A source causal protocol induces these kernels by running its private
tape against perpetual FAIL; conversely a sampled stream can be followed causally.
The kernel is a Mathlib probability kernel, not a success/packing certificate. -/
structure StreamProtocol (Ω : Type*) [MeasurableSpace Ω] where
  attempts : ℕ → Kernel Ω AttemptStream
  probability : ∀ w, IsMarkovKernel (attempts w)

instance {Ω : Type*} [MeasurableSpace Ω] (P : StreamProtocol Ω) (w : ℕ) :
    IsMarkovKernel (P.attempts w) := P.probability w

/-- Private streams are sampled independently conditional on the shared input.
Population labels are used only by the analyst, never supplied to the rule. -/
noncomputable def privateLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : StreamProtocol Ω) {r : ℕ} (wake : Fin r → ℕ) (y : Ω) :
    Measure (Fin r → AttemptStream) :=
  Measure.pi (fun u => P.attempts (wake u) y)

/-- Wake-up slots themselves are silent. -/
def attempted {r : ℕ} (wake : Fin r → ℕ) (a : Fin r → AttemptStream)
    (u : Fin r) (t : ℕ) : Prop := wake u < t ∧ a u t = true

noncomputable def singletonSlot {r : ℕ} (wake : Fin r → ℕ)
    (a : Fin r → AttemptStream) (t : ℕ) : Prop :=
  ∃! u, attempted wake a u t

/-- The actual execution follows the all-FAIL tapes until the first singleton,
including that singleton slot, and halts afterwards. This is a constructed coupling. -/
noncomputable def actualStreams {r : ℕ} (wake : Fin r → ℕ)
    (a : Fin r → AttemptStream) : Fin r → AttemptStream := by
  classical
  exact fun u t => decide (attempted wake a u t ∧
    ∀ s, s < t → ¬ singletonSlot wake a s)

/-- Infimum in ENat: no singleton has value infinity, never a real default zero. -/
noncomputable def firstSingleton {r : ℕ} (wake : Fin r → ℕ)
    (a : Fin r → AttemptStream) : ℕ∞ :=
  ⨅ t : {t : ℕ // singletonSlot wake a t}, (t.val : ℕ∞)

noncomputable def actualFirstSuccess {r : ℕ} (wake : Fin r → ℕ)
    (a : Fin r → AttemptStream) : ℕ∞ :=
  firstSingleton wake (actualStreams wake a)

/-- Auxiliary failure on the source's open-left, closed-right window. -/
def auxiliaryFail {r : ℕ} (wake : Fin r → ℕ) (t₀ ℓ : ℕ) :
    Set (Fin r → AttemptStream) :=
  {a | ∀ t ∈ Finset.Ioc t₀ (t₀ + ℓ), ¬ singletonSlot wake a t}

/-- Actual nontermination by a deadline includes executions with no success ever. -/
noncomputable def actualFail {r : ℕ} (wake : Fin r → ℕ) (deadline : ℕ) :
    Set (Fin r → AttemptStream) :=
  {a | (deadline : ℕ∞) < actualFirstSuccess wake a}

end EliasGlobalClock.LowerBound


