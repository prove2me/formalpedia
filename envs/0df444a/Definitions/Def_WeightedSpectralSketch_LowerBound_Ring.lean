-- Prove2me | Definitions.Def_WeightedSpectralSketch_LowerBound_Ring
-- name    : WeightedSpectralSketch_LowerBound_Ring
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:01:51.529756+00:00
-- url     : https://prove2.me/theorems/ffea2708-c995-4777-a1c4-e9a92f502ee3
-- title:
--   The block ring: cyclic distance $L(i,j)$, base weights (3), the query edge and the unanchored Yes/No inputs
-- statement:
--   Fix integers $b\ge1$ and an even $\ell\ge2$. A **ring template** has $\ell$ cyclically ordered blocks indexed $0,\dots,\ell-1$, each with $b$ slots; slot $(i,j)$ is the $j$-th slot of block $i$. A **ring labeling** of a vertex set $R$ with $|R|=\ell b$ is a bijection $\sigma$ from slots to $R$, the vertex $\sigma(i,j)$ occupying slot $(i,j)$; the blocks are $B_i=\{\sigma(i,j)\}_j$. A uniformly random labeling is the paper's uniform permutation $\pi$ placing vertex $\pi(t)$ in slot $t$.
--
--   1. **Cyclic distance:** $L(i,j)=\min\{|i-j|,\ \ell-|i-j|\}$.
--   2. **Base weights** (Eq. (3)) with within-block weight $w_{\mathrm{int}}$ and $w_{\mathrm{ext}}=\ell/(16b^2)$:
--   $$w_e=\begin{cases}w_{\mathrm{int}},& e\in\binom{B_i}{2}\text{ for some } i,\\ w_{\mathrm{ext}}\,L(i,j)^{-4},& e=uv,\ u\in B_i,\ v\in B_j,\ i\ne j.\end{cases}$$
--   3. **Query edge:** for fixed distinguished slots $(0,j_x)$ and $(\ell/2,j_y)$, $x=\sigma(0,j_x)$, $y=\sigma(\ell/2,j_y)$ and $q=xy$.
--   4. **Unanchored inputs** (§4.1, $w_{\mathrm{int}}=(\ell b)^2$): for noise values $z$, No gives $\tilde w_e=w_ez_e$ and Yes gives $\tilde w_e=w_ez_e+\mathbf 1\{e=q\}$. The **support** of the two distributions is the set of all such inputs with every $z_e\in[\tfrac12,\tfrac32]$, over all labelings and both cases.
--   5. The **test success probability** of a test $T(\sigma,\widehat L)\in\{\text{Yes},\text{No}\}$ under one case is the probability, over a uniform labeling, the product noise and the sketch seed (all independent), that $T$ applied to the labeling and the recovery output $D(\omega,A(\omega)\tilde w)$ returns that case.
--
--   This is the hard instance of §4.1. The edge weights decay as the inverse fourth power of the cyclic block distance.
--
--   **Formalization Note.** The labeling is a bijection from the slot type `Fin ℓ × Fin b` to an arbitrary finite vertex type; block $\ell/2$ is `Fin.ofNat ℓ (ℓ/2)`. The query edge is a `Sym2` element, which is a genuine edge slot whenever $\ell\ge2$.
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, pp. 9–10, §4.1 (template, blocks, query edge, L(i,j), Eq. (3) base weights, perturbed weights); p. 13 (joint distribution with π), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_WeightedSpectralSketch_LowerBound_Graph
import Definitions.Def_WeightedSpectralSketch_LowerBound_Stat

open MeasureTheory Matrix
open scoped ENNReal

namespace WeightedSpectralSketch.LowerBound

/-- The cyclic block distance `L(i, j) = min{|i - j|, ℓ - |i - j|}` on `ℓ` cyclically ordered
blocks (p. 9). -/
def cycDist (ℓ i j : ℕ) : ℕ := min (Nat.dist i j) (ℓ - Nat.dist i j)

theorem cycDist_comm (ℓ i j : ℕ) : cycDist ℓ i j = cycDist ℓ j i := by
  simp [cycDist, Nat.dist_comm]

/-- The cyclic distance between the two blocks of an unordered pair of block indices. -/
def symDist (ℓ : ℕ) : Sym2 (Fin ℓ) → ℕ :=
  Sym2.lift ⟨fun i j => cycDist ℓ i j, fun i j => cycDist_comm ℓ i j⟩

/-- The block index `ℓ / 2`, opposite to block `0`. -/
def halfBlock (ℓ : ℕ) [NeZero ℓ] : Fin ℓ := Fin.ofNat ℓ (ℓ / 2)

/-- The base weight (3), p. 9, between two ring slots `p = (i, ·)` and `p' = (j, ·)` (block,
position in block): `w_int` inside a block and `w_ext L(i, j)^{-4}` with `w_ext = ℓ / (16 b²)`
between different blocks. -/
noncomputable def slotWeight (ℓ b : ℕ) (wint : ℝ) (p p' : Fin ℓ × Fin b) : ℝ :=
  if p.1 = p'.1 then wint else ((ℓ : ℝ) / (16 * (b : ℝ) ^ 2)) / (cycDist ℓ p.1 p'.1 : ℝ) ^ 4

theorem slotWeight_comm (ℓ b : ℕ) (wint : ℝ) (p p' : Fin ℓ × Fin b) :
    slotWeight ℓ b wint p p' = slotWeight ℓ b wint p' p := by
  unfold slotWeight
  by_cases h : p.1 = p'.1
  · simp [h]
  · simp [h, Ne.symm h, cycDist_comm]

/-- The block of a ring vertex under the labeling `σ` (slot `(i, j)` holds vertex `σ (i, j)`). -/
def blockOf {ℓ b : ℕ} {R : Type*} (σ : Fin ℓ × Fin b ≃ R) (v : R) : Fin ℓ := (σ.symm v).1

/-- The base weight `w_e` (3), p. 9, of the edge `e` under the ring labeling `σ`, with
within-block weight `wint`. -/
noncomputable def ringBaseWeight (ℓ b : ℕ) (wint : ℝ) {R : Type*} (σ : Fin ℓ × Fin b ≃ R)
    (e : EdgeSlot R) : ℝ :=
  Sym2.lift ⟨slotWeight ℓ b wint, slotWeight_comm ℓ b wint⟩ (e.1.map σ.symm)

/-- The query edge `q = xy` (p. 9): `x` occupies the distinguished slot `(0, jx)` of block `0` and
`y` the distinguished slot `(ℓ/2, jy)` of block `ℓ/2`. -/
def ringQuery {ℓ b : ℕ} [NeZero ℓ] {R : Type*} (σ : Fin ℓ × Fin b ≃ R) (jx jy : Fin b) : Sym2 R :=
  s(σ (0, jx), σ (halfBlock ℓ, jy))

/-- The perturbed input weights of the unanchored hard distributions (§4.1, p. 10) on the vertex
set `R` with `|R| = ℓ b`: `w̃_e = w_e z_e` (No, `yes = false`) or `w̃_e = w_e z_e + 1{e = q}`
(Yes, `yes = true`), with `w_int = (ℓ b)²` and noise values `z`. -/
noncomputable def ringInput (ℓ b : ℕ) [NeZero ℓ] {R : Type*} (jx jy : Fin b)
    (σ : Fin ℓ × Fin b ≃ R) (yes : Bool) (z : EdgeSlot R → ℝ) : EdgeSlot R → ℝ :=
  open Classical in fun e =>
    ringBaseWeight ℓ b (((ℓ * b : ℕ) : ℝ) ^ 2) σ e * z e +
      if yes = true ∧ e.1 = ringQuery σ jx jy then 1 else 0

/-- The support of the union of the unanchored Yes and No distributions: all inputs
`ringInput σ yes z` with any labeling `σ`, either case, and every noise value `z_e ∈ [½, 3/2]`
(the support of the density (4)). -/
def ringSupport (ℓ b : ℕ) [NeZero ℓ] (R : Type*) [Fintype R] [DecidableEq R] (jx jy : Fin b) :
    Set (EdgeSlot R → ℝ) :=
  {w | ∃ (σ : Fin ℓ × Fin b ≃ R) (yes : Bool) (z : EdgeSlot R → ℝ),
    (∀ e, z e ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) ∧ w = ringInput ℓ b jx jy σ yes z}

/-- The success probability, under the Yes (`yes = true`) or No (`yes = false`) unanchored
distribution, of the test `T` that sees the labeling `σ` and the recovery output `D ω (A ω w̃)`
and answers Yes (`true`) or No (`false`). The labeling is uniform, the noise has law
`noiseProd`, and the seed has law `P`, all independent. -/
noncomputable def ringTestSuccess (ℓ b : ℕ) [NeZero ℓ] {R : Type*} [Fintype R] [DecidableEq R]
    (jx jy : Fin b) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : LinearSketch R N Ω) (T : (Fin ℓ × Fin b ≃ R) → (R → R → ℝ) → Bool) (yes : Bool) :
    ℝ≥0∞ :=
  (Fintype.card (Fin ℓ × Fin b ≃ R) : ℝ≥0∞)⁻¹ *
    ∑ σ : Fin ℓ × Fin b ≃ R, ∫⁻ z, P {ω | T σ (S.D ω (Matrix.of (S.A ω) *ᵥ
      ringInput ℓ b jx jy σ yes z)) = yes} ∂(noiseProd (EdgeSlot R))

end WeightedSpectralSketch.LowerBound


