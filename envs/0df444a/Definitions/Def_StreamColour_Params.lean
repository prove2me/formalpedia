-- Prove2me | Definitions.Def_StreamColour_Params
-- name    : StreamColour_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:00.522729+00:00
-- url     : https://prove2.me/theorems/839d4dca-cf4d-420b-8561-6304e7ae7e43
-- title:
--   (1) — $\ell$, $h$, palette size, and the probability conventions
-- statement:
--   The mission's shared parameters, from equation (1): $\ell=\max\{1,\lceil\log_2(n+1)\rceil\}$ and $h=\lceil C(k+\ell^{10})\rceil$, where $C$ is a fixed constant, together with the palette size $t=\lceil C_{\mathrm{pal}}\ell^2\rceil$.
--
--   Two probability conventions are also fixed. "$E$ has probability at least $c$" under a measure $\mu$ means that some measurable $A\subseteq E$ has $\mu(A)\ge c$. For independent uniform samples on a finite set, the joint law is the uniform law on the product, so the probability of an event is the fraction of the product where it holds.
--
--   **Formalization Note** $\lceil\log_2 m\rceil$ is `Nat.clog 2 m`. The $t$-element subsets of $[q]$ are a subtype of `Finset (Fin q)`. On an empty sample space the counting fraction is $0/0=0$, which fails every positive lower bound.
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), §3, p.20 (PDF 22), eq. (1)

import Mathlib

namespace StreamColour

open MeasureTheory
open scoped ENNReal

/-! # Parameters and probability conventions

Chakraborty, Chatterjee, Kundu, Mishra, *Streaming Graph Colouring Meets Molloy–Reed via
Kernelization* (STOC 2027 submission, sha256 31a813b3…), §3, p.20 (PDF 22), equation (1):
`ℓ = max{1, ⌈log₂(n+1)⌉}` and `h = ⌈C(k + ℓ¹⁰)⌉`.

**Formalization Note.** `Nat.clog 2 m` is `⌈log₂ m⌉`. `C` is a real constant; `h` is its ceiling in `ℕ`,
and `⌈x⌉₊ = 0` for `x ≤ 0`, which no statement of the mission uses, since each takes `C` large.
"With probability at least `c`" is an inner bound (`ProbAtLeast`): some measurable event of measure at
least `c` lies inside the event, so an unmeasurable event is not overstated by outer measure. On a finite
sample space with independent uniform coordinates the law is the uniform law on the product, so
`unifProb` is the counting fraction; an empty sample space gives `0 / 0 = 0`, which fails every positive
lower bound. -/

/-- `ℓ = max{1, ⌈log₂(n+1)⌉}`, equation (1), p.20. -/
def ell (n : ℕ) : ℕ := max 1 (Nat.clog 2 (n + 1))

/-- `h = ⌈C(k + ℓ¹⁰)⌉`, equation (1), p.20. -/
noncomputable def hParam (C : ℝ) (n k : ℕ) : ℕ := ⌈C * ((k : ℝ) + (ell n : ℝ) ^ 10)⌉₊

/-- `t = ⌈C_pal ℓ²⌉`, the palette size of Lemmas 5.16, 5.19 and Step 1 of Algorithm B. -/
noncomputable def sampleSize (Cp : ℝ) (n : ℕ) : ℕ := ⌈Cp * (ell n : ℝ) ^ 2⌉₊

/-- The event `E` has probability at least `c` under `μ`: a measurable subevent has measure `≥ c`. -/
def ProbAtLeast {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E : Set Ω) (c : ℝ≥0∞) : Prop :=
  ∃ A, MeasurableSet A ∧ A ⊆ E ∧ c ≤ μ A

open Classical in
/-- The probability of `E` under the uniform law on a finite type: the counting fraction. -/
noncomputable def unifProb (Ω : Type*) [Fintype Ω] (E : Ω → Prop) : ℝ :=
  ((Finset.univ.filter E).card : ℝ) / (Fintype.card Ω : ℝ)

/-- The `t`-element subsets of the colour set `[q]`, here `Fin q`. -/
abbrev TSubset (q t : ℕ) : Type := {s : Finset (Fin q) // s.card = t}

end StreamColour


