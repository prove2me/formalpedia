-- Prove2me | Definitions.Def_SubsetConvFPRAS_JVV
-- name    : SubsetConvFPRAS_JVV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:45.867897+00:00
-- url     : https://prove2.me/theorems/8068cd1a-1c49-4dc4-86be-a9c011be88d3
-- title:
--   The Jerrum–Valiant–Vazirani estimator of Lemma 3.1, written out
-- statement:
--   Let $w:\{0,1\}^m\to\mathbb R_{\ge0}$ and write $\pi\propto w$. For a partial assignment (a pin) the **conditional law** is $\pi$ restricted to the assignments compatible with it, renormalized; $\|p-q\|_{TV}=\tfrac12\sum_\sigma|p(\sigma)-q(\sigma)|$.
--
--   A **conditional sampler** for $w$ is a family of distributions, indexed by a pin, a starting state and an accuracy $\tau$, such that whenever the starting state is compatible with the pin and has positive weight and $0<\tau<1$, every output is compatible with the pin and has positive weight, and the output law is within total variation $\tau$ of the conditional law.
--
--   The **estimator** (the standard self-reduction): for $i=1,\dots,m$ in order, draw $s$ samples from the law conditioned on the current pin, each started from the previous sample (first from $\sigma_0$); let $b$ be the majority value of bit $i$ and $\hat p_i$ its frequency; pin bit $i$ to $b$ and continue from a sample with that bit. With $\sigma$ the final, fully pinned state, return
--   $$\hat Z=\frac{w(\sigma)}{\prod_{i=1}^m\hat p_i}.$$
--   The run counts its sampler calls and its arithmetic operations (one per sample and two per coordinate). Randomness is a product of independent draws, one per sampler call.
--
--   Lemma 3.1 is the accuracy and cost guarantee of this estimator.
--
--   **Formalization Note** The page cites [JVV86] without writing the estimator, and "one can compute $\hat Z$" under a bare existential would be trivial for a Lean function that can read $w$. So the estimator is this explicit function of the sampler's outputs and of one evaluation of $w$.
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Lemma 3.1, p.18 (citing Jerrum, Valiant, Vazirani 1986); total variation, p.17

import Mathlib

open scoped Classical

namespace SubsetConvFPRAS

/-!
# The Jerrum–Valiant–Vazirani estimator of Lemma 3.1

X. Chen, K. Liu, *An FPRAS for Counting Common Bases of Two Matroids*, arXiv:2610.06724 (version held,
sha256 6c1d68c2…), Lemma 3.1, p.18.

**Formalization Note.** The page cites [JVV86] and gives no algorithm, and "one can compute `Ẑ`" under a
bare existential would be trivial for a Lean function that may read `w`. So this file writes the standard
estimator out, as an explicit function of the sampler's outputs:
for each coordinate `i` in order, draw `s` samples from the law conditioned on the current prefix, each
started from the previous sample; let `b` be the majority value of bit `i` and `p̂_i` its frequency;
fix bit `i` to `b`, and continue from a sample having that bit. Return `w(σ) / ∏ p̂_i` for the final
state `σ`. The randomness is `PMF.bind`, so each sampler call is fresh and independent given its inputs.
The counter `ops` charges one per sample plus two per coordinate for the arithmetic. The single evaluation
of `w` is the one in the returned formula.
-/

variable {m : ℕ}

/-- `σ` agrees with the fixed coordinates of `pin`. -/
def Compat (pin : Fin m → Option Bool) (σ : Fin m → Bool) : Prop :=
  ∀ i b, pin i = some b → σ i = b

/-- The conditional law of `π ∝ w` given the fixed coordinates of `pin`. -/
noncomputable def condLaw (w : (Fin m → Bool) → ℝ) (pin : Fin m → Option Bool) :
    (Fin m → Bool) → ℝ :=
  fun σ => if Compat pin σ then w σ / ∑ τ, (if Compat pin τ then w τ else 0) else 0

/-- `‖p - q‖_TV = ½ ∑_σ |p(σ) - q(σ)|`, p.17. -/
noncomputable def tvDist (p : PMF (Fin m → Bool)) (q : (Fin m → Bool) → ℝ) : ℝ :=
  (1 / 2) * ∑ σ, |(p σ).toReal - q σ|

/-- The sampler hypothesis of Lemma 3.1, p.18: for every conditional law, any starting state in its
support (so the law is nonempty) and every `0 < τ < 1`, the sampler's output lies in that support and is
within total variation distance `τ` of the conditional law. -/
def IsCondSampler (w : (Fin m → Bool) → ℝ)
    (samp : (Fin m → Option Bool) → (Fin m → Bool) → ℝ → PMF (Fin m → Bool)) : Prop :=
  ∀ pin start τ, Compat pin start → 0 < w start → 0 < τ → τ < 1 →
    (∀ σ ∈ (samp pin start τ).support, Compat pin σ ∧ 0 < w σ) ∧
      tvDist (samp pin start τ) (condLaw w pin) ≤ τ

/-- `s` successive sampler calls, each started from the previous sample. -/
noncomputable def jvvDraw (samp : (Fin m → Option Bool) → (Fin m → Bool) → ℝ → PMF (Fin m → Bool))
    (pin : Fin m → Option Bool) (τ : ℝ) : ℕ → (Fin m → Bool) → PMF (List (Fin m → Bool))
  | 0, _ => PMF.pure []
  | s + 1, σ => (samp pin σ τ).bind fun σ' => (jvvDraw samp pin τ s σ').map (fun l => σ' :: l)

/-- The state of the estimator: the fixed coordinates, the current starting state, the product of the
frequencies, and the counters. -/
structure JVVState (m : ℕ) where
  pin : Fin m → Option Bool
  start : Fin m → Bool
  prodP : ℝ
  samplerCalls : ℕ
  ops : ℕ

/-- The update after the samples `l` of coordinate `i`. -/
noncomputable def jvvUpdate (s : ℕ) (i : Fin m) (st : JVVState m) (l : List (Fin m → Bool)) :
    JVVState m :=
  let b : Bool := decide (s ≤ 2 * (l.filter (fun σ => σ i = true)).length)
  let cb : ℕ := (l.filter (fun σ => σ i = b)).length
  { pin := Function.update st.pin i (some b)
    start := (l.find? (fun σ => σ i = b)).getD st.start
    prodP := st.prodP * ((cb : ℝ) / s)
    samplerCalls := st.samplerCalls + s
    ops := st.ops + s + 2 }

/-- The estimator's final state, on sampler `samp`, start `σ₀`, accuracy `τ` and `s` samples per
coordinate. -/
noncomputable def jvvRun (samp : (Fin m → Option Bool) → (Fin m → Bool) → ℝ → PMF (Fin m → Bool))
    (σ₀ : Fin m → Bool) (τ : ℝ) (s : ℕ) : PMF (JVVState m) :=
  (List.finRange m).foldl
    (fun acc i => acc.bind fun st => (jvvDraw samp st.pin τ s st.start).map (jvvUpdate s i st))
    (PMF.pure ⟨fun _ => none, σ₀, 1, 0, 0⟩)

/-- The returned estimate `Ẑ = w(σ) / ∏ p̂_i`. -/
noncomputable def jvvEstimate (w : (Fin m → Bool) → ℝ) (st : JVVState m) : ℝ :=
  w st.start / st.prodP

end SubsetConvFPRAS


