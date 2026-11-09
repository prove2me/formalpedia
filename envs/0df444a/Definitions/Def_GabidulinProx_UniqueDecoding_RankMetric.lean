-- Prove2me | Definitions.Def_GabidulinProx_UniqueDecoding_RankMetric
-- name    : GabidulinProx_UniqueDecoding_RankMetric
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:12.69845+00:00
-- url     : https://prove2.me/theorems/61670060-ab07-4f45-acfd-9ebaf0226242
-- title:
--   Base-field rank, joint interleaving distance and proximity gaps
-- statement:
--   Let $L/K$ be a finite extension of finite fields. The rank of $y\in L^n$ is
--
--   $$\operatorname{rk}_q(y)=\dim_K\operatorname{span}_K\{y_r:r<n\}.$$
--
--   For a stacked pair, the columns are $(u_{0,r},u_{1,r})\in L\times L$ and the rank is their joint $K$-span dimension. A linear code is a submodule $C\le L^n$. Its distance from $v$ is the minimum of $\operatorname{rk}_q(v-c)$ over $c\in C$. The order-two interleaving contains all pairs of codewords, and its distance from $(u_0,u_1)$ is the minimum joint rank of the two residual rows over all such pairs. Each minimum is taken over an actual nonempty finite set.
--
--   Write $\ell(z)=u_0+zu_1$. Uniform probability means cardinality divided by $|L|$. A proximity gap is exactly the implication, for every $u_0,u_1$,
--
--   $$\Pr_{z\in L}[d(\ell(z),C)/n\le\delta]>\varepsilon
--   \quad\Longrightarrow\quad d([u_0,u_1],C^2)/n\le\delta.$$
--
--   Every theorem using relative distances has $n\ge1$. The definition is total at $n=0$, where real division returns zero, but no goal instance has that length. The representation makes rank independent of a chosen basis and keeps correlation between both rows.
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Definition 1.1 p.4; §2.2 pp.12–13; Definitions 2.3 and 2.5 p.13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf

import Mathlib

namespace GabidulinProx.UniqueDecoding

/-- Basis-free column rank over the BASE field (§2.2, p.12). -/
noncomputable def wordRank (K : Type*) {M : Type*} [Field K] [AddCommGroup M]
    [Module K M] {n : ℕ} (y : Fin n → M) : ℕ :=
  Module.finrank K (Submodule.span K (Set.range y))

/-- Column rank of the stacked pair, not the maximum or sum of its row ranks. -/
noncomputable def pairRank (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] {n : ℕ} (u₀ u₁ : Fin n → L) : ℕ :=
  wordRank K (fun r => (u₀ r, u₁ r))

/-- Definition 2.3, p.13. A finite linear code is nonempty since it contains zero. -/
noncomputable def codeDistance (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype L] {n : ℕ} (C : Submodule L (Fin n → L))
    (v : Fin n → L) : ℕ := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  exact (Finset.univ.image (fun c : C => wordRank K (v - c.val))).min'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- Definition 2.5, p.13: codewords of the order-two interleaving. -/
def interleavedCode {L : Type*} [Field L] {n : ℕ}
    (C : Submodule L (Fin n → L)) : Set ((Fin n → L) × (Fin n → L)) :=
  {c | c.1 ∈ C ∧ c.2 ∈ C}

/-- A joint minimum over both rows, using the 2m-by-n column rank. -/
noncomputable def pairDistance (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype L] {n : ℕ} (C : Submodule L (Fin n → L))
    (u₀ u₁ : Fin n → L) : ℕ := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  exact (Finset.univ.image (fun c : C × C =>
    pairRank K (u₀ - c.1.val) (u₁ - c.2.val))).min'
      (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- Affine line parameterization; permits zero or dependent directions. -/
def linePoint {L : Type*} [Field L] {n : ℕ} (u₀ u₁ : Fin n → L) (z : L) : Fin n → L :=
  fun r => u₀ r + z * u₁ r

/-- Uniform probability on every element of the finite extension field. -/
noncomputable def uniformFraction {L : Type*} [Fintype L] (p : L → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter p).card : ℝ) / (Fintype.card L : ℝ)

/-- Definition 1.1, p.4, with its strict probability threshold and joint conclusion.
All uses of relative distance assume n>0; the definition itself is total at n=0. -/
noncomputable def HasProximityGap (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype L] {n : ℕ} (C : Submodule L (Fin n → L)) (δ ε : ℝ) : Prop :=
  ∀ u₀ u₁ : Fin n → L,
    uniformFraction (fun z => (codeDistance K C (linePoint u₀ u₁ z) : ℝ) / (n : ℝ) ≤ δ) > ε →
    (pairDistance K C u₀ u₁ : ℝ) / (n : ℝ) ≤ δ

end GabidulinProx.UniqueDecoding


