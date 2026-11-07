-- Prove2me | Definitions.Def_SubsetConvFPRAS_CoordinateDescent
-- name    : SubsetConvFPRAS_CoordinateDescent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:42.653056+00:00
-- url     : https://prove2.me/theorems/8791766f-9826-43b4-9baa-edb1a4270dc1
-- title:
--   The stochastic coordinate-descent algorithm of Theorem 3.2 (Appendix A.4)
-- statement:
--   The algorithm of Appendix A.4, written as an explicit function. Fix $d$, a gradient oracle $G:\mathbb R^d\times\Xi\to\mathbb R^d$ and a tape $\omega=(\omega_0,\omega_1,\dots)$ of independent draws, the $j$-th oracle call reading $\omega_j$. With parameters $L,\sigma,H_0,\eta,\delta$, a step $s$ and a coordinate-selection rule, put (26)
--   $$K=\lceil128LH_0\eta^{-2}\rceil+1,\qquad \hat m=\bigl\lceil32\sigma^2\eta^{-2}\log(2d(K+1)/\delta)\bigr\rceil.$$
--   Start at $x=x_0$. At each iteration average $\hat m$ fresh oracle vectors at $x$ to get $\hat g$. Return $x$ if $\|\hat g\|_\infty\le\eta/2$; otherwise declare failure if $K$ updates have already occurred; otherwise choose $i$ with $|\hat g_i|>\eta/2$ and set $x\leftarrow x-s\,\operatorname{sign}(\hat g_i)e_i$.
--
--   The run records its output (a point, or failure), the list of queried points, the number of oracle calls, and the number of batches. Its time is charged $T$ per oracle call plus $d\hat m$ per batch for averaging and selecting (p.38). The file also defines $Q$ of (16) and the partial derivative $\partial_if(x)$.
--
--   This is the algorithm whose guarantees Theorem 3.2 states; Corollary 5.12 runs it on $\Phi$.
--
--   **Formalization Note** "Choose $i$ with $|\hat g_i|>\eta/2$" is a selection rule supplied as a parameter. The loop has fuel $K+1$ batches, which the algorithm never exceeds.
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Appendix A.4, (25)–(27), p.38; (16), p.18

import Mathlib

open scoped Classical

namespace SubsetConvFPRAS

/-!
# The stochastic coordinate-descent algorithm of Theorem 3.2

X. Chen, K. Liu, *An FPRAS for Counting Common Bases of Two Matroids*, arXiv:2610.06724 (version held,
sha256 6c1d68c2…), Appendix A.4, (25)–(27), p.38.

**Formalization Note.**
* The gradient oracle is `G : (Fin d → ℝ) → Ξ → (Fin d → ℝ)`; fresh independent randomness is a tape
  `ω : ℕ → Ξ` of independent draws, and the `j`-th oracle call reads `ω j`.
* "Choose `i` with `|ĝ_i| > η/2`" is a selection rule `sel`, a parameter of the algorithm.
* `cdRun` makes at most `K + 1` batches: it returns or fails by the batch after `K` updates.
* The trace records the point of every batch (the queried points), and counts oracle calls and batches.
  Time is charged by `cdTime`: `T` per oracle call and `d·m̂` per batch for averaging and selecting (p.38).
-/

variable {d : ℕ}

/-- What one execution produced: the returned point (`none` is failure), the queried points, the number
of oracle calls, and the number of batches. -/
structure CDTrace (d : ℕ) where
  out : Option (Fin d → ℝ)
  queried : List (Fin d → ℝ)
  calls : ℕ
  batches : ℕ

/-- `ĝ = m⁻¹ ∑_{l < m} G(x, ω_{j+l})`, the average of a batch of `m` fresh oracle vectors at `x`. -/
noncomputable def batchMean {Ξ : Type} (G : (Fin d → ℝ) → Ξ → (Fin d → ℝ)) (x : Fin d → ℝ) (m : ℕ)
    (ω : ℕ → Ξ) (j : ℕ) : Fin d → ℝ :=
  fun i => (m : ℝ)⁻¹ * ∑ l ∈ Finset.range m, G x (ω (j + l)) i

/-- The loop of p.38, from point `x`, after `k` updates, with `j` tape entries used. If `‖ĝ‖∞ ≤ η/2` return
`x`; otherwise fail if `K` updates have occurred; otherwise update `x ← x - s·sign(ĝ_i) e_i` with
`i = sel ĝ`, where `sign(u) = u/|u|`. -/
noncomputable def cdLoop {Ξ : Type} (G : (Fin d → ℝ) → Ξ → (Fin d → ℝ)) (s η : ℝ) (K m : ℕ)
    (sel : (Fin d → ℝ) → Fin d) (ω : ℕ → Ξ) :
    ℕ → (Fin d → ℝ) → ℕ → ℕ → CDTrace d
  | 0, _, _, _ => ⟨none, [], 0, 0⟩
  | fuel + 1, x, k, j =>
    let g := batchMean G x m ω j
    if ∀ i, |g i| ≤ η / 2 then ⟨some x, [x], m, 1⟩
    else if K ≤ k then ⟨none, [x], m, 1⟩
    else
      let i := sel g
      let rest := cdLoop G s η K m sel ω fuel
        (Function.update x i (x i - s * (g i / |g i|))) (k + 1) (j + m)
      ⟨rest.out, x :: rest.queried, m + rest.calls, 1 + rest.batches⟩

/-- `K := ⌈128 L H₀ η⁻²⌉ + 1`, (26), p.38. -/
noncomputable def cdK (L H₀ η : ℝ) : ℕ := ⌈128 * L * H₀ * (η⁻¹) ^ 2⌉₊ + 1

/-- `m̂ := ⌈32 σ² η⁻² log(2d(K+1)/δ)⌉`, (26), p.38. -/
noncomputable def cdBatch (σ η : ℝ) (d K : ℕ) (δ : ℝ) : ℕ :=
  ⌈32 * σ ^ 2 * (η⁻¹) ^ 2 * Real.log (2 * d * (K + 1) / δ)⌉₊

/-- An execution of the algorithm from `x₀` on tape `ω`: at most `K + 1` batches. -/
noncomputable def cdRun {Ξ : Type} (G : (Fin d → ℝ) → Ξ → (Fin d → ℝ)) (x₀ : Fin d → ℝ)
    (L σ H₀ η δ s : ℝ) (sel : (Fin d → ℝ) → Fin d) (ω : ℕ → Ξ) : CDTrace d :=
  cdLoop G s η (cdK L H₀ η) (cdBatch σ η d (cdK L H₀ η) δ) sel ω (cdK L H₀ η + 1) x₀ 0 0

/-- The total time charged to an execution: `T` per oracle call, `d·m̂` per batch (p.38). -/
noncomputable def cdTime (T : ℝ) (d m : ℕ) (tr : CDTrace d) : ℝ :=
  T * tr.calls + (d : ℝ) * m * tr.batches

/-- `Q` of (16), p.18. -/
noncomputable def cdQ (L σ H₀ η δ : ℝ) (d : ℕ) : ℝ :=
  (1 + σ ^ 2 / η ^ 2) * (1 + L * H₀ / η ^ 2) * Real.log (2 * d / δ * (1 + L * H₀ / η ^ 2))

/-- `∂_i f(x)`. -/
noncomputable def partialAt (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (i : Fin d) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

end SubsetConvFPRAS


