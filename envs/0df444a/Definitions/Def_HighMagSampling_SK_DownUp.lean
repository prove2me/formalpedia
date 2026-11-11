-- Prove2me | Definitions.Def_HighMagSampling_SK_DownUp
-- name    : HighMagSampling_SK_DownUp
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:26:48.879987+00:00
-- url     : https://prove2.me/theorems/322f096b-311d-4198-b22b-1607df718360
-- title:
--   The Hamming slice $\mathcal X^d_k$, the fixed-magnetization Ising measure and the down-up walk $\mathcal T^{\mathrm{DU},\pi}$
-- statement:
--   Let $d,k\in\mathbb N$ and $\mathcal X=\{\pm1\}$. The **Hamming slice** is
--   $$\mathcal X^d_k=\Big\{x\in\mathcal X^d:\ \textstyle\sum_{i\in[d]}x_i=-d+2k\Big\},$$
--   the vectors with exactly $k$ entries $+1$; $\sum_i x_i$ is the **magnetization**. Each $x\in\mathcal X^d_k$ corresponds to the $k$-set $S=\mathrm{set}(x)\subseteq[d]$ of its $+1$ coordinates, and conversely $\mathrm{vec}(S)=2\cdot\mathbf 1_S-\mathbf 1_d$.
--
--   **Down-up walk.** For a probability measure $\pi$ on $\mathcal X^d_k$ ($k\in[d]$), one step of $\mathcal T^{\mathrm{DU},\pi}$ from $S$ (i) chooses a uniformly random $T\subseteq S$ with $|T|=k-1$, then (ii) samples $S'\supseteq T$ with $|S'|=k$ with probability proportional to $\pi(S')$. Hence
--   $$\mathcal T^{\mathrm{DU},\pi}_S(S')=\sum_{\substack{T\subseteq S\cap S'\\|T|=k-1}}\frac1k\cdot\frac{\pi(S')}{\sum_{S''\supseteq T,\ |S''|=k}\pi(S'')} ,$$
--   and $S'=S$ is allowed.
--
--   **Fixed-magnetization Ising measure.** For an interaction matrix $J\in\mathbb R^{d\times d}$, an external field $h\in\mathbb R^d$ and an inverse temperature $\beta$,
--   $$\pi(x)\propto\exp\Big(\beta\big(\tfrac12x^\top Jx+h^\top x\big)\Big)\cdot\mathbb I(x\in\mathcal X^d_k),$$
--   normalised by the finite sum over the slice. It has full support on $\mathcal X^d_k$.
--
--   The down-up walk is the sampler whose mixing the paper analyses; the Ising measure on the slice is its target.
--
--   **Formalization Note.** Coordinates are `Fin d` (0-based). The slice is encoded through the paper's bijection $x\mapsto\mathrm{set}(x)$: `Slice d k` is the type of `k`-element `Finset (Fin d)`, finite, with the discrete σ-algebra, and `vec S` is the $\pm1$ vector. `downUp π` is a Mathlib kernel given by the displayed formula, with the down step enumerated as the `(k−1)`-subsets of `S` (written `T.card + 1 = k`). The page leaves the up step undefined when its normaliser vanishes, which can only happen from a $\pi$-null state; there the term is $0$ (`ENNReal` division $0/0=0$). `isingMeasure k β J h` is a finite sum of point masses with real weights $\exp(\beta(\frac12 x^\top Jx+h^\top x))/Z$.
-- source:
--   Kumar, Sarkar, Tian, Zhu, High-Magnetization Sampling at Low Temperatures, arXiv:2609.08873v1, p. 10, §2.2 (X^d_k, set/vec, the down-up walk); p. 12, Eq. (10); p. 15, Eq. (16); p. 14, Algorithm 1

import Mathlib

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace HighMagSampling.SK

/-!
# The Hamming slice, the fixed-magnetization Ising measure and the down-up walk

Kumar, Sarkar, Tian, Zhu, *High-Magnetization Sampling at Low Temperatures*, arXiv:2609.08873v1,
§2.2, p. 10 (PDF p. 12); Eq. (10), p. 12 (PDF p. 14); Eq. (16), p. 15 (PDF p. 17); Algorithm 1,
p. 14 (PDF p. 16).

**Formalization Note.**
* Coordinates are `Fin d` (the paper's `[d]`, shifted to start at `0`).
* The slice `X^d_k = {x ∈ {±1}^d : Σ_i x_i = −d + 2k}` is encoded by the paper's own bijection
  `x ↦ set(x)`: `Slice d k` is the type of `k`-element subsets `S ⊆ [d]`, and `vec S = 2·1_S − 1_d`
  is the `±1` vector with `+1` exactly on `S`. It is finite and carries the discrete σ-algebra.
* `downUp π` is the down-up walk `T^{DU,π}` as a kernel: from `S`, a uniformly random
  `(k−1)`-subset `T ⊆ S` (probability `1/k` each), then `S' ⊇ T` in the slice with probability
  `π(S') / Σ_{S'' ⊇ T} π(S'')`. So
  `T^{DU,π}_S(S') = Σ_{T ⊆ S ∩ S', |T| = k−1} (1/k) π(S') / Σ_{S'' ⊇ T} π(S'')`; `S' = S` is
  allowed. When the normaliser is `0` (only possible from a `π`-null state) the term is `0`.
* `isingMeasure k β J h` is `π(x) ∝ exp(β(½ xᵀJx + hᵀx))` restricted to `X^d_k` (Eq. (16)),
  normalised by the finite sum over the slice.
-/

/-- The Hamming slice `X^d_k`, encoded as the `k`-subsets `set(x)` of `[d]` (p. 10). -/
def Slice (d k : ℕ) : Type := {S : Finset (Fin d) // S.card = k}

instance (d k : ℕ) : Fintype (Slice d k) := by unfold Slice; infer_instance

instance (d k : ℕ) : DecidableEq (Slice d k) := by unfold Slice; infer_instance

instance (d k : ℕ) : MeasurableSpace (Slice d k) := ⊤

instance (d k : ℕ) : DiscreteMeasurableSpace (Slice d k) := ⟨fun _ => trivial⟩

/-- `vec(S) ∈ {±1}^d`: `+1` on `S`, `−1` off `S` (p. 10). -/
noncomputable def vec {d k : ℕ} (S : Slice d k) : Fin d → ℝ :=
  fun i => if i ∈ S.1 then 1 else -1

/-- The up-step normaliser `Σ_{S'' ∈ X^d_k, S'' ⊇ T} π(S'')`. -/
noncomputable def upMass {d k : ℕ} (π : Measure (Slice d k)) (T : Finset (Fin d)) : ℝ≥0∞ :=
  ∑ S'' : Slice d k, if T ⊆ S''.1 then π {S''} else 0

/-- The transition probability `T^{DU,π}_S(S')` of the down-up walk (§2.2, p. 10; Algorithm 1). -/
noncomputable def downUpProb {d k : ℕ} (π : Measure (Slice d k)) (S S' : Slice d k) : ℝ≥0∞ :=
  ∑ T ∈ S.1.powerset.filter (fun T => T.card + 1 = k ∧ T ⊆ S'.1),
    (k : ℝ≥0∞)⁻¹ * (π {S'} / upMass π T)

/-- The down-up walk `T^{DU,π}` on `X^d_k` as a kernel (§2.2, p. 10; Algorithm 1, p. 14). -/
noncomputable def downUp {d k : ℕ} (π : Measure (Slice d k)) : Kernel (Slice d k) (Slice d k) where
  toFun S := ∑ S' : Slice d k, downUpProb π S S' • Measure.dirac S'
  measurable' := Measurable.of_discrete

/-- The unnormalised Ising weight `exp(β(½ xᵀJx + hᵀx))` at `x = vec(S)` (Eq. (10)). -/
noncomputable def isingWeight {d k : ℕ} (β : ℝ) (J : Matrix (Fin d) (Fin d) ℝ) (h : Fin d → ℝ)
    (S : Slice d k) : ℝ :=
  Real.exp (β * ((1 / 2) * (vec S ⬝ᵥ (J *ᵥ vec S)) + h ⬝ᵥ vec S))

/-- The fixed-magnetization Ising measure `π ∝ exp(β(½ xᵀJx + hᵀx)) · I(x ∈ X^d_k)` (Eq. (16)). -/
noncomputable def isingMeasure {d : ℕ} (k : ℕ) (β : ℝ) (J : Matrix (Fin d) (Fin d) ℝ)
    (h : Fin d → ℝ) : Measure (Slice d k) :=
  ∑ S : Slice d k,
    ENNReal.ofReal (isingWeight β J h S / ∑ S' : Slice d k, isingWeight β J h S') • Measure.dirac S

end HighMagSampling.SK


