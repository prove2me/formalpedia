-- Prove2me | Definitions.Def_PrivateContinualCounting_Kraft_Envelopes
-- name    : PrivateContinualCounting_Kraft_Envelopes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:30.659774+00:00
-- url     : https://prove2.me/theorems/8cfc79e1-3b8b-49b2-b12c-6ee8ac33331b
-- title:
--   Real doubling envelopes and the Kraft condition
-- statement:
--   An envelope is a function $g:[1,\infty)\to[1,\infty)$ that is nondecreasing and has a doubling constant $D\ge1$:
--   $$g(2u)\le Dg(u)\quad(u\ge1).$$
--   Continuity is not required. The Kraft condition and an anytime variance bound are respectively
--   $$K(g):\ \sum_{k=0}^{\infty}\frac1{g(2^k)}<\infty,\qquad
--   \exists C>0\ \forall t\ge3:\ v_t\le C(\ln t)^2g(\ln t).$$
--   The convergence condition uses summability, so a divergent series cannot receive a default finite value. The constant is chosen before all times and may depend on the counter and envelope. These definitions are shared by the necessity and sufficiency directions. In Lean $g$ is extended arbitrarily below $1$; none of those values is used.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 6, PDF p. 8, §2.3, Envelopes

import Mathlib

open MeasureTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft

/-- Real, possibly discontinuous envelopes on the whole half-line. Values below 1 are unused. -/
def IsEnvelopeWith (g : ℝ → ℝ) (D : ℝ) : Prop :=
  1 ≤ D ∧ (∀ u : ℝ, 1 ≤ u → 1 ≤ g u) ∧
  MonotoneOn g (Set.Ici 1) ∧ (∀ u : ℝ, 1 ≤ u → g (2 * u) ≤ D * g u)

def IsEnvelope (g : ℝ → ℝ) : Prop := ∃ D : ℝ, IsEnvelopeWith g D

/-- Convergence is explicit; a divergent real tsum is never read as zero. -/
def KraftCondition (g : ℝ → ℝ) : Prop := Summable (fun k : ℕ => 1 / g ((2 : ℝ) ^ k))

def HasEnvelope (v : ℕ → ℝ) (g : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, 3 ≤ t → v t ≤ C * (Real.log (t : ℝ)) ^ 2 * g (Real.log (t : ℝ))

end PrivateContinualCounting.Kraft


