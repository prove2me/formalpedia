-- Prove2me | Definitions.Def_ParallelDiffusionLB_NearIsotropic_Product
-- name    : ParallelDiffusionLB_NearIsotropic_Product
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:45.492665+00:00
-- url     : https://prove2.me/theorems/35fe9775-9af3-425b-9184-0508be7d67e7
-- title:
--   Product instance law, gated oracle and truncations
-- statement:
--   A layout has $B\ge1$ blocks of dimension $m\ge1$ and $d_{pad}\ge0$ remaining coordinates, so $d=Bm+d_{pad}$. In applications $m=\lfloor d/B\rfloor$. For codebooks $S_1,\ldots,S_B$, concatenate independent uniform codewords and independent uniform padding signs to obtain the center law $\mu^S$. Let $\pi_\tau^S=\mu^S*N(0,\tau^2I_d)$ and take the target $\pi^S=\pi_\gamma^S$. Codebooks of prescribed sizes $n_j$ have their independent uniform-subset laws.
--
--   The total-noise oracle is
--   $$\hat s_{j,\tau}^S(x)=s_\tau^0(x_j)+\left(\prod_{i<j}a_\tau^{S_i}(x_i)\right)\bigl(b_\tau^{S_j}(x_j)-s_\tau^0(x_j)\bigr),$$
--   with the exact public score on padding coordinates. The empty product is one. Additional noise $\sigma>0$ uses $\tau=\sqrt{\gamma^2+\sigma^2}$. The $r$-truncated oracle retains the first $r$ gated blocks and replaces later blocks by null scores, retaining exact padding.
--
--   The public choice $H=C_H\log(dP/(\varepsilon\rho))$ and the strict adjacent-rate separation predicate specify the arithmetic conventions used by the milestones. Concatenation and coordinate projection are actual maps, including when padding has dimension zero.
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, (10)–(13), p. 18; (30), p. 23; (37), p. 25

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Codebook
import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Algorithm

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

/-- A nonempty list of positive-dimensional blocks and possibly zero padding. -/
structure Layout where
  B : ℕ
  m : ℕ
  pad : ℕ
  B_pos : 0 < B
  m_pos : 0 < m

namespace Layout

def d (L : Layout) : ℕ := L.B * L.m + L.pad

def coord (L : Layout) (j : Fin L.B) (i : Fin L.m) : Fin L.d :=
  ⟨j.val * L.m + i.val, by
    have hj := j.isLt
    have hi := i.isLt
    dsimp [d]
    nlinarith⟩

def padCoord (L : Layout) (i : Fin L.pad) : Fin L.d :=
  ⟨L.B * L.m + i.val, by dsimp [d]; omega⟩

abbrev Books (L : Layout) := Fin L.B → Finset (Cube L.m)

def block (L : Layout) (x : E L.d) (j : Fin L.B) : E L.m :=
  WithLp.toLp 2 (fun i => x (L.coord j i))

def padding (L : Layout) (x : E L.d) : E L.pad :=
  WithLp.toLp 2 (fun i => x (L.padCoord i))

/-- Coordinate concatenation as a sum of coordinate vectors. Empty padding gives zero. -/
def join (L : Layout) (x : Fin L.B → E L.m) (z : E L.pad) : E L.d :=
  (∑ j, ∑ i, EuclideanSpace.single (L.coord j i) (x j i)) +
    ∑ i, EuclideanSpace.single (L.padCoord i) (z i)

/-- Finite product center law (10), including uniform sign padding. -/
def centerLaw (L : Layout) (S : L.Books) : Measure (E L.d) :=
  ((Measure.pi (fun j => uniformFinset (S j))).prod
    (uniformFinset (Finset.univ : Finset (Cube L.pad)))).map
      (fun yz => L.join (fun j => vertex (yz.1 j)) (vertex yz.2))

def targetLaw (L : Layout) (S : L.Books) (τ : ℝ) : Measure (E L.d) :=
  smoothLaw (L.centerLaw S) τ

def instanceLaw (L : Layout) (n : Fin L.B → ℕ) : Measure L.Books :=
  Measure.pi (fun j => codebookLaw L.m (n j))

def sizesValid (L : Layout) (n : Fin L.B → ℕ) : Prop :=
  ∀ j, 1 ≤ n j ∧ n j ≤ 2 ^ L.m

def booksValid (L : Layout) (S : L.Books) : Prop := ∀ j, (S j).Nonempty

/-- Block component in the product-gated score oracle (30), with zero-based block labels. -/
def oracleBlock (L : Layout) (ε ρ τ : ℝ) (S : L.Books) (x : E L.d) (j : Fin L.B) : E L.m :=
  nullScore L.m τ (L.block x j) +
    (∏ i ∈ Finset.univ.filter (fun i : Fin L.B => i < j),
      gate L.B ε ρ (S i) τ (L.block x i)) •
      (localAnswer L.B ε (S j) τ (L.block x j) - nullScore L.m τ (L.block x j))

def totalOracle (L : Layout) (ε ρ τ : ℝ) (S : L.Books) (x : E L.d) : E L.d :=
  L.join (L.oracleBlock ε ρ τ S x) (nullScore L.pad τ (L.padding x))

/-- Additional-noise oracle, fixed for the whole interaction. -/
def oracle (L : Layout) (γ ε ρ : ℝ) (S : L.Books) (q : Query L.d) : E L.d :=
  L.totalOracle ε ρ (Real.sqrt (γ ^ 2 + q.2.val ^ 2)) S q.1

/-- Keep the first r blocks; r is a count, so r=0 means all block answers are public. -/
def truncatedTotal (L : Layout) (ε ρ τ : ℝ) (S : L.Books) (r : ℕ) (x : E L.d) : E L.d :=
  L.join (fun j => if j.val < r then L.oracleBlock ε ρ τ S x j
    else nullScore L.m τ (L.block x j)) (nullScore L.pad τ (L.padding x))

def truncated (L : Layout) (γ ε ρ : ℝ) (S : L.Books) (r : ℕ) (q : Query L.d) : E L.d :=
  L.truncatedTotal ε ρ (Real.sqrt (γ ^ 2 + q.2.val ^ 2)) S r q.1

def separated (L : Layout) (n : Fin L.B → ℕ) (H C : ℝ) : Prop :=
  ∀ j k : Fin L.B, k.val = j.val + 1 →
    C * transitionScale L.m H < rate L.m (n k) - rate L.m (n j)

/-- The public H in (13), with its implicit constant made an argument. -/
def publicH (L : Layout) (P : ℕ) (ε ρ C_H : ℝ) : ℝ :=
  C_H * Real.log (L.d * P / (ε * ρ))

end Layout
end ParallelDiffusionLB.NearIsotropic


