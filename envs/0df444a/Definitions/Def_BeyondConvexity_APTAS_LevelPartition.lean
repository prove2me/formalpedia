-- Prove2me | Definitions.Def_BeyondConvexity_APTAS_LevelPartition
-- name    : BeyondConvexity_APTAS_LevelPartition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:13:35.840195+00:00
-- url     : https://prove2.me/theorems/d9a6a81d-f844-4ae8-897a-dfa856c3ff8d
-- title:
--   Level-separated partitions with real scales
-- statement:
--   A finite list of positive scales and one level index per labeled input occurrence describes a level partition. If its last index is $J$, the root scale is $s_0=1$ and every scale satisfies $0<s_j\le1$. For a dyadic $\alpha=2^{-K}$ with integer $K>0$ and $0<\beta,\gamma<1$, validity requires
--
--   $$
--   \beta s_j<D(P)\quad(P\in S_j),\qquad D(P)\le\alpha s_j\quad(P\in S_j,\ j\ge1),\qquad s_{j+1}=\gamma s_j\quad(1\le j<J).
--   $$
--
--   The root deliberately has no small-object upper bound, and its transition to the first lower level is unconstrained by this definition. Empty intermediate levels are retained. An empty instance can use a single root scale and no occurrence indices. Real scales express the full analytic definition; a separate fixed encoder is provided for rational scale lists. No rationality condition is imposed by the analytic validity predicate.
--
--   This is Definition 4's geometric partition object. It does not construct Section 3's separator partition or assume the stronger root-ratio or grid-resolution conclusions of Lemma 2.
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/890.pdf, Definition 4, printed p.6 / PDF p.7; Section 3, printed pp.9–10 / PDF pp.10–11.

import Definitions.Def_BeyondConvexity_APTAS_PolynomialOn

noncomputable section

namespace BeyondConvexity.APTAS

/-- Finite level data. List positions, rather than geometries, identify occurrences.
Real scales are permitted in the analytic definition; rational scales can be encoded. -/
structure LevelPartition (F : Type) where
  scales : List F
  levels : List ℕ

def LevelPartition.J {F : Type} (p : LevelPartition F) : ℕ := p.scales.length - 1

def LevelPartition.scale {F : Type} [Zero F] (p : LevelPartition F) (j : ℕ) : F :=
  p.scales.getD j 0

def LevelPartition.level {F : Type} (p : LevelPartition F) (i : ℕ) : ℕ :=
  p.levels.getD i 0

def LevelPartition.Realize (p : LevelPartition ℚ) : LevelPartition ℝ :=
  ⟨p.scales.map (fun s => (s : ℝ)), p.levels⟩

def PositiveDyadic (α : ℝ) : Prop :=
  ∃ K : ℕ, 0 < K ∧ α = (2 : ℝ) ^ (-(K : ℤ))

/-- Definition 4: the root has a lower diameter bound but no small-object upper
bound; geometric decay starts at level one, not at the root transition. -/
def LevelPartition.Valid (p : LevelPartition ℝ) (I : Instance) (α β γ : ℝ) : Prop :=
  PositiveDyadic α ∧ 0 < β ∧ β < 1 ∧ 0 < γ ∧ γ < 1 ∧
  p.scales ≠ [] ∧ p.levels.length = I.length ∧ p.scale 0 = 1 ∧
  (∀ j ≤ p.J, 0 < p.scale j ∧ p.scale j ≤ 1) ∧
  (∀ i : Fin I.length, p.level i ≤ p.J ∧
    β * p.scale (p.level i) < (I.get i).diameter ∧
    (1 ≤ p.level i → (I.get i).diameter ≤ α * p.scale (p.level i))) ∧
  ∀ j, 1 ≤ j → j < p.J → p.scale (j + 1) = γ * p.scale j

open RSListDecodingCapacity.AllRates (encNat encList)

def encLevelPartition (p : LevelPartition ℚ) : List Bool :=
  encList AbelianCayleyHDX.encRat p.scales ++ encList encNat p.levels

end BeyondConvexity.APTAS


