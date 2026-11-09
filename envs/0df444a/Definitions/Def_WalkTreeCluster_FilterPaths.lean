-- Prove2me | Definitions.Def_WalkTreeCluster_FilterPaths
-- name    : WalkTreeCluster_FilterPaths
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:39:59.274093+00:00
-- url     : https://prove2.me/theorems/49d8822e-264a-4835-ad7b-33bd7be722b7
-- title:
--   Filter paths, the weights $\omega(\sigma)=a^{40\theta(\sigma)}$, filter path collisions $\langle X,Y\rangle_w$ and tensor moments
-- statement:
--   A *filter path* of length $i$ is a word $\sigma=\sigma_1\cdots\sigma_i\in\{L,H\}^i$ (low-pass/high-pass), and a stage-$i$ sample is a matrix $X\in\mathbb R^{\{L,H\}^i\times V}$ with one row per filter path. The root letter $\sigma_i$ is chosen first by the walk tree. The collision weight of $\sigma$ is (Eq. (17))
--   $$\omega(\sigma)=a^{40\theta(\sigma)},\qquad \theta(\sigma)=\max_{0\le r\le i}\big(|\sigma_i\cdots\sigma_{i-r+1}|-ar\big)_+,$$
--   where $|\cdot|$ counts high-pass letters, so $\theta$ inspects every prefix read from the root. The number of filter path collisions and the weighted Frobenius norm are (Definition 2.7)
--   $$\langle X,Y\rangle_w=\sum_{\sigma\in\{L,H\}^i}\sum_{z\in V}\omega(\sigma)X(\sigma,z)Y(\sigma,z),\qquad \|X\|_{F,w}^2=\langle X,X\rangle_w .$$
--   For a random matrix $X$, the weighted tensor moment is (Definition 6.1)
--   $$\big\|\mathbb E[X^{\otimes r}]\big\|_{F,w}^2=\sum_{(\sigma_1,z_1),\dots,(\sigma_r,z_r)}\Big(\prod_{j=1}^r\omega(\sigma_j)\Big)\,\mathbb E\big[X(\sigma_1,z_1)\cdots X(\sigma_r,z_r)\big]^2 .$$
--   For a stage-$j$ matrix $X$, $X\oplus0$ and $0\oplus X$ are the stage-$(j+1)$ matrices that place $X$ in the rows with root letter $L$, respectively $H$ (Eq. (27)). The unweighted norm $\sum_\sigma\|X_\sigma\|_2^2$ is also used.
--
--   **Formalization Note.** A filter path is a function $\{0,\dots,i-1\}\to\{\text{false},\text{true}\}$ (true $=H$); the letter $\sigma_k$ is the value at $k-1$, so the root letter is the last value. Moments are Bochner integrals, and a separate predicate states that all products of $r$ entries are integrable.
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Definition 2.7, p.9; Definition 2.8, Eq. (17), p.12; Definition 6.1, p.20; Eq. (27), p.24

import Mathlib

open MeasureTheory

namespace WalkTreeCluster

/-!
# Filter paths, collision weights, filter path collisions and tensor moments

Kapralov–Kochetkova, *Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027
submission (manuscript sha256 638eeef1…), Definition 2.6, p.8; Definition 2.7, p.9; Definition 2.8,
Eq. (17), p.12; Definition 6.1, p.20; Eq. (27) (the blocks `X ⊕ 0`, `0 ⊕ X`), p.24.

A filter path of length `i` is a word `σ = σ_1 ⋯ σ_i ∈ {L, H}^i`; a stage-`i` sample is a matrix
`X ∈ ℝ^{{L,H}^i × V}`. The weights are `ω(σ) = a^{40 θ(σ)}` with
`θ(σ) = max_{0 ≤ r ≤ i} (|σ_i ⋯ σ_{i−r+1}| − a r)₊`, where `|·|` counts high-pass letters.
`⟨X, Y⟩_w = Σ_σ Σ_z ω(σ) X(σ, z) Y(σ, z)` and `‖X‖²_{F,w} = ⟨X, X⟩_w`. For a random matrix `X` with
law `μ`, `‖E[X^{⊗r}]‖²_{F,w} = Σ_{(σ_1,z_1),…,(σ_r,z_r)} (Π_j ω(σ_j)) (E[X(σ_1,z_1)⋯X(σ_r,z_r)])²`.

**Formalization Note.**
* A filter path is `σ : Fin i → Bool`, `true` = `H`, `false` = `L`. The page's letter `σ_k` is
  `σ ⟨k − 1, _⟩`; the **root** letter `σ_i`, chosen first by the walk tree (and applied first to the
  vector, see the filter module), is `σ ⟨i − 1, _⟩ = σ (Fin.last _)`. `θ` counts high-pass letters in
  the prefixes `σ_i σ_{i−1} ⋯ σ_{i−r+1}` read from the root, i.e. in the indices `i − r, …, i − 1`.
* `lowBlock X = X ⊕ 0` puts a stage-`j` matrix into the rows of stage `j + 1` whose root letter is
  `L` (the remaining letters being the row of `X`); `highBlock X = 0 ⊕ X` likewise for `H`
  ("We order the rows with paths beginning with L first", p.24).
* Expectations are Bochner integrals; `MomentIntegrable r μ` states that every product of `r`
  entries is integrable, so that the moment tensors are the page's expectations and not Lean's
  default value `0`.
-/

/-- Filter paths of length `i` (`true` = `H`). -/
abbrev FPath (i : ℕ) := Fin i → Bool

/-- Stage-`i` matrices `ℝ^{{L,H}^i × V}`. -/
abbrev Mat (n i : ℕ) := FPath i → Fin n → ℝ

/-- `|σ_i ⋯ σ_{i−r+1}|`: the number of high-pass letters among the `r` letters next to the root. -/
def highCount {i : ℕ} (σ : FPath i) (r : ℕ) : ℕ :=
  (Finset.univ.filter (fun k : Fin i => i - r ≤ k.val ∧ σ k = true)).card

/-- `θ(σ) = max_{0 ≤ r ≤ i} (|σ_i ⋯ σ_{i−r+1}| − a r)₊`, Eq. (17). -/
noncomputable def theta (a : ℝ) {i : ℕ} (σ : FPath i) : ℝ :=
  (Finset.range (i + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos i)⟩
    (fun r => max 0 ((highCount σ r : ℝ) - a * r))

/-- `ω(σ) = a^{40 θ(σ)}`, Eq. (17). -/
noncomputable def omega (a : ℝ) {i : ℕ} (σ : FPath i) : ℝ :=
  a ^ (40 * theta a σ)

/-- `⟨X, Y⟩_w = Σ_σ Σ_z ω(σ) X(σ, z) Y(σ, z)`, Definition 2.7. -/
noncomputable def wInner (a : ℝ) {n i : ℕ} (X Y : Mat n i) : ℝ :=
  ∑ σ : FPath i, ∑ z : Fin n, omega a σ * X σ z * Y σ z

/-- `‖X‖²_{F,w} = ⟨X, X⟩_w`, Definition 2.7. -/
noncomputable def wNormSq (a : ℝ) {n i : ℕ} (X : Mat n i) : ℝ :=
  wInner a X X

/-- The unweighted squared Frobenius norm `Σ_σ ‖X_σ‖²₂ = Σ_σ Σ_z X(σ, z)²`. -/
noncomputable def frobSq {n i : ℕ} (X : Mat n i) : ℝ :=
  ∑ σ : FPath i, ∑ z : Fin n, X σ z ^ 2

/-- `X ⊕ 0`: a stage-`j` matrix in the rows of stage `j + 1` with root letter `L`. -/
def lowBlock {n j : ℕ} (X : Mat n j) : Mat n (j + 1) :=
  fun σ z => if σ (Fin.last j) = false then X (Fin.init σ) z else 0

/-- `0 ⊕ X`: a stage-`j` matrix in the rows of stage `j + 1` with root letter `H`. -/
def highBlock {n j : ℕ} (X : Mat n j) : Mat n (j + 1) :=
  fun σ z => if σ (Fin.last j) = true then X (Fin.init σ) z else 0

/-- Every product of `r` entries of `X` is integrable under `μ`. -/
def MomentIntegrable {n i : ℕ} (r : ℕ) (μ : Measure (Mat n i)) : Prop :=
  ∀ c : Fin r → FPath i × Fin n, Integrable (fun X : Mat n i => ∏ j, X (c j).1 (c j).2) μ

/-- `‖E[X^{⊗r}]‖²_{F,w}` for `X ∼ μ`, Definition 6.1. -/
noncomputable def momentNormSq (a : ℝ) {n i : ℕ} (r : ℕ) (μ : Measure (Mat n i)) : ℝ :=
  ∑ c : Fin r → FPath i × Fin n,
    (∏ j, omega a (c j).1) * (∫ X, ∏ j, X (c j).1 (c j).2 ∂μ) ^ 2

/-- `‖E[X^{⊗2}]‖²_{F,w}`. -/
noncomputable def secondMomentNormSq (a : ℝ) {n i : ℕ} (μ : Measure (Mat n i)) : ℝ :=
  momentNormSq a 2 μ

/-- `‖E[X^{⊗4}]‖²_{F,w}`. -/
noncomputable def fourthMomentNormSq (a : ℝ) {n i : ℕ} (μ : Measure (Mat n i)) : ℝ :=
  momentNormSq a 4 μ

end WalkTreeCluster


