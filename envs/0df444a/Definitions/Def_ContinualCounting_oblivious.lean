-- Prove2me | Definitions.Def_ContinualCounting_oblivious
-- name    : ContinualCounting_oblivious
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:39.373511+00:00
-- url     : https://prove2.me/theorems/d59c53ea-f0e7-4de0-8248-80a6fcfe0cce
-- title:
--   Oblivious mechanisms $M(x)=Ax+z$
-- statement:
--   A mechanism has **oblivious noise** if $M(x)=Ax+z$ for a noise vector $z$ independent of $x$. Given a law $\nu$ on $\mathbb R^n$, the oblivious mechanism with noise law $\nu$ sends $x\in\{0,1\}^n$ to the law of $Ax+z$ with $z\sim\nu$.
--
--   Lemma 2 reduces an arbitrary mechanism to such a mechanism, on a shorter input.
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), Lemma 2, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_ContinualCounting_prefixSum

set_option autoImplicit false

open MeasureTheory

namespace ContinualCounting

/-- **Oblivious noise.** Bairaktari, Dahl, Larsen, arXiv:2607.00876 (sha256 986e6426…), Lemma 2, p.17:
"oblivious noise means that M′(x) = Ax + z for z independent of x". The mechanism with noise law `ν`
sends `x` to the law of `Ax + z`, `z ∼ ν`.

**Formalization Note.** The map `z ↦ Ax + z` is measurable, so this `Measure.map` is the true
pushforward, a probability measure when `ν` is. -/
noncomputable def oblivious {n : ℕ} (ν : Measure (Fin n → ℝ)) (x : Fin n → Bool) :
    Measure (Fin n → ℝ) :=
  ν.map fun z => prefixSum (bitVec x) + z

end ContinualCounting


