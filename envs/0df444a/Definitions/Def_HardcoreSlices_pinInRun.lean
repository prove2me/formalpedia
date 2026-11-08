-- Prove2me | Definitions.Def_HardcoreSlices_pinInRun
-- name    : HardcoreSlices_pinInRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:36:29.255198+00:00
-- url     : https://prove2.me/theorems/dadae40c-e7bb-4802-961f-8c5600cb4ce7
-- title:
--   The pin-in estimator of Lemma 6.4
-- statement:
--   Let $X$ be a complex on $[n]$ with a sampler `samp`. One **stage** from a pinned set $\tau$ draws $M$ independent samples from `samp τ η`, computes the empirical frequency $\hat p_v$ of each $v\in\mathcal X_\tau(1)$, picks a vertex of maximum $\hat p_v$, pins it in, and multiplies $\hat p_v$ into a running product. The estimator is $\ell=k-|\tau|$ stages, with
--   $$h=\frac{\varepsilon}{8\ell n},\qquad M=\Bigl\lceil\frac{2\log(2\ell n/\delta)}{h^2}\Bigr\rceil,\qquad\eta=\frac h2,$$
--   and its output on a final state with pinned set $S$ and product $\Pi$ is $\hat Z_\tau=w(S)/\Pi$.
--
--   **Formalization Note** `pinInRun` is the law on final states, a `PMF`. Ties in the argmax go to the smallest vertex of $[n]$, and the state counts sampler calls.
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), proof of Lemma 6.4, p.29

import Mathlib
import Definitions.Def_SteurerHDX_faces
import Definitions.Def_HDXConc_linkWeight

open Classical

namespace HardcoreSlices

/-- `M` independent draws from `p`, as a list. -/
noncomputable def drawList {α : Type} (p : PMF α) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | M + 1 => p.bind fun x => (drawList p M).map (x :: ·)

/-- The empirical frequency `p̂v = (1/m) Σ_i 1{v ∈ S_i}` of p.29. -/
noncomputable def empFreq {n : ℕ} (L : List (Finset (Fin n))) (v : Fin n) : ℝ :=
  (L.countP (fun S => v ∈ S) : ℝ) / L.length

/-- `v∗ = argmax_{v∈W} f(v)` (p.29). Ties go to the smallest vertex of `[n]`; `none` when `W` is empty. -/
noncomputable def pickVertex {n : ℕ} (W : Finset (Fin n)) (f : Fin n → ℝ) : Option (Fin n) :=
  if h : (W.filter (fun v => ∀ u ∈ W, f u ≤ f v)).Nonempty then
    some ((W.filter (fun v => ∀ u ∈ W, f u ≤ f v)).min' h)
  else none

/-- The state of the estimator of Lemma 6.4: the pinned set, the running product of the `p̂r`, and the number of sampler
calls so far. -/
structure PinState (n : ℕ) where
  /-- The pinned set. -/
  pinned : Finset (Fin n)
  /-- The running product `Π p̂r`. -/
  prod : ℝ
  /-- The sampler calls so far. -/
  calls : ℕ

/-- One iteration of the estimator (p.29): draw `M` samples within accuracy `η` of the law of the current link, take a
vertex of maximum empirical frequency in `Xτ(1)`, pin it in, and multiply its frequency into the product. -/
noncomputable def pinStage {n : ℕ} (X : Finset (Finset (Fin n))) (samp : Finset (Fin n) → ℝ → PMF (Finset (Fin n)))
    (η : ℝ) (M : ℕ) (st : PinState n) : PMF (PinState n) :=
  (drawList (samp st.pinned η) M).map fun L =>
    match pickVertex (HDXConc.linkVerts X st.pinned) (empFreq L) with
    | some v => ⟨insert v st.pinned, st.prod * empFreq L v, st.calls + M⟩
    | none => ⟨st.pinned, st.prod, st.calls + M⟩

/-- **The pin-in estimator of Lemma 6.4**, as a law on final states: `r` iterations of `pinStage` from the pinned set `τ`.
Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), proof of Lemma 6.4, p.29. -/
noncomputable def pinInRun {n : ℕ} (X : Finset (Finset (Fin n)))
    (samp : Finset (Fin n) → ℝ → PMF (Finset (Fin n))) (η : ℝ) (M : ℕ) (τ : Finset (Fin n)) :
    ℕ → PMF (PinState n)
  | 0 => PMF.pure ⟨τ, 1, 0⟩
  | r + 1 => (pinInRun X samp η M τ r).bind (pinStage X samp η M)

/-- `h = ε/(8ℓn)` (p.29). -/
noncomputable def pinH (n ℓ : ℕ) (ε : ℝ) : ℝ := ε / (8 * ℓ * n)

/-- `m = ⌈2 log(2ℓn/δ) / h²⌉` (p.29). -/
noncomputable def pinM (n ℓ : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈2 * Real.log (2 * ℓ * n / δ) / pinH n ℓ ε ^ 2⌉₊

end HardcoreSlices


