-- Prove2me | Definitions.Def_HochbaumShmoys_Uniform_AllPack
-- name    : HochbaumShmoys_Uniform_AllPack
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:31.579536+00:00
-- url     : https://prove2.me/theorems/e0bee428-f48d-40a1-9acf-70dd403ca90b
-- title:
--   The procedure all-pack as a relation between inputs and answers (§3, pp. 541–549)
-- statement:
--   Fix $N\ge2$ and $\delta=1/N$. Given piece sizes $p_1,\dots,p_n$ and bin sizes $b_1,\dots,b_m$, the procedure **all-pack** sorts the bins by non-increasing size, normalizes all sizes by the largest bin size $\max_i b_i$ (so the largest bin has size $1$), builds the layered graph of the normalized instance, looks for a path from initial to success, and, if possible, converts it into a packing.
--
--   1. all-pack **may output** the packing $\sigma$ when all $b_i>0$, all $p_j>0$, every $p_j\le\max_i b_i$, and for some ordering $o$ of the bins with $b_{o(1)}\ge\dots\ge b_{o(m)}$, $\sigma=o\circ\tau$ where $\tau$ is a packing of the normalized instance $\big(b_{o(t)}/\max_i b_i\big)_t$, $\big(p_j/\max_i b_i\big)_j$ traced from an initial–success path of its layered graph.
--   2. all-pack **may answer** "no truly feasible packing" exactly when it may output no packing at all.
--   3. A **resolution** of all-pack is a map $D$ from instances to answers that, on every instance, gives an answer all-pack may give.
--
--   The paper's procedure makes arbitrary choices (ties in sorting, which path, which pieces of a class go into a bin, where each small piece goes); a resolution fixes one way of making them. Statements about all-pack are made for every resolution.
--
--   **Formalization Note** all-pack is modeled as a relation, not a function, because its choices are arbitrary. A piece larger than the largest bin, or a nonpositive size, means all-pack outputs no packing (the paper leaves this implicit: after normalization it assumes the pieces lie in $(0,1]$). Answering "none" when no packing can be traced follows the paper's "and then (if possible) converting the path to a packing". Every instance has at least one admissible answer, so resolutions exist.
-- source:
--   Hochbaum & Shmoys, A Polynomial Approximation Scheme for Scheduling on Uniform Processors: Using the Dual Approximation Approach, SIAM J. Comput. 17(3) 1988, p. 541 (s₁ ≥ ··· ≥ s_m), p. 543 (normalization s₁ = 1), p. 549, §3 (the procedure all-pack)

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_Packing
import Definitions.Def_HochbaumShmoys_Uniform_LayeredGraph

namespace HochbaumShmoys.Uniform

/-- The largest bin size `max_i b i`. -/
noncomputable def largestBin {m : ℕ} (b : Fin m → ℝ) : ℝ := ⨆ i, b i

/-- Bins listed in the order `ord` and normalized so that the largest has size 1. -/
noncomputable def normalizedBins {m : ℕ} (b : Fin m → ℝ) (ord : Fin m ≃ Fin m) : Fin m → ℝ :=
  fun t => b (ord t) / largestBin b

/-- Pieces normalized by the largest bin size. -/
noncomputable def normalizedPieces {m n : ℕ} (p : Fin n → ℝ) (b : Fin m → ℝ) : Fin n → ℝ :=
  fun j => p j / largestBin b

/-- all-pack at parameter `δ = 1/N` may output the packing `σ` of the pieces `p` into the bins
`b`: sizes are positive, no piece exceeds the largest bin, and for some ordering `ord` of the
bins by non-increasing size, `σ` is a packing traced from an initial–success path of the layered
graph of the normalized instance, with bins renamed back through `ord`. -/
def AllPackOutputs (N : ℕ) {m n : ℕ} (p : Fin n → ℝ) (b : Fin m → ℝ)
    (σ : Fin n → Fin m) : Prop :=
  (∀ i, 0 < b i) ∧ (∀ j, 0 < p j ∧ p j ≤ largestBin b) ∧
  ∃ ord : Fin m ≃ Fin m, Antitone (fun t => b (ord t)) ∧
    ∃ τ : Fin n → Fin m,
      IsTracedPacking N (normalizedBins b ord) (normalizedPieces p b) τ ∧
      σ = fun j => ord (τ j)

/-- The answers all-pack may give on `(p, b)`: a packing it may output, or `none` ("no truly
feasible packing") exactly when it can output no packing. -/
def AllPackAnswer (N : ℕ) {m n : ℕ} (p : Fin n → ℝ) (b : Fin m → ℝ) :
    Option (Fin n → Fin m) → Prop
  | some σ => AllPackOutputs N p b σ
  | none => ¬ ∃ σ, AllPackOutputs N p b σ

/-- `D` is a resolution of all-pack at `δ = 1/N`: on every input it gives an answer all-pack may
give (the arbitrary choices of the procedure resolved in some way). -/
def IsAllPackResolution (N : ℕ) {m n : ℕ}
    (D : (Fin n → ℝ) → (Fin m → ℝ) → Option (Fin n → Fin m)) : Prop :=
  ∀ p b, AllPackAnswer N p b (D p b)

end HochbaumShmoys.Uniform


