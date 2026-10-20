-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
-- name    : OAI_Analysis_LipschitzEquivalence_LocalLipschitz
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:11:31.270367+00:00
-- url     : https://prove2.me/theorems/cc7fe698-f61e-4fc3-bd71-4d60d16b7c1f
-- title:
--   Best Lipschitz constants on subsets and local orthogonality
-- statement:
--   Two notions for maps on metric spaces.
--
--   1. **Local Lipschitz constant.** For $f:M\to N$ and $S\subseteq M$, the quotients are $0$ and the ratios $d(f(x),f(y))/d(x,y)$ for $x,y\in S$, and the constant of $f$ on $S$ is their supremum. If $f$ is $L$-Lipschitz on $S$, the quotients are bounded by $L$ and the constant is nonnegative.
--   2. **Local orthogonality.** A map $D:M\to\mathcal H=\bigl(\bigoplus_n\mathbb R^{\iota_n}\bigr)_{\ell^2}$ is locally orthogonal if for any finitely many distinct points $z_i$ there are $r>0$, a cutoff $l$ and pairwise disjoint coordinate sets $S_i$ such that the tails beyond block $l$ are supported in $S_i$ near $z_i$:
--   $$
--   d(x,z_i)<r\ \Longrightarrow\ \mathrm{tail}_l(D(x))\in\mathcal H_{S_i}.
--   $$
--   3. **Bad sets.** For sets $O_j$ with numbers $a_j$ and $\eta$, the bad set is the set of $z$ such that $\eta\le a_j$ whenever $z\in O_j$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/LocalLipschitz.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/LocalLipschitz.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LipschitzEquivalence mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates

namespace OAI

universe uM uN uB uIndex

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} {N : Type uN} [MetricSpace M] [MetricSpace N]

def quotients (f : M → N) (S : Set M) : Set ℝ :=
  {0} ∪ {r | ∃ x ∈ S, ∃ y ∈ S, r = dist (f x) (f y) / dist x y}

def constant (f : M → N) (S : Set M) : ℝ := sSup (quotients f S)

theorem quotient_le {f : M → N} {S : Set M} {L : ℝ≥0}
    (hf : LipschitzOnWith L f S) {x y : M} (hx : x ∈ S) (hy : y ∈ S) :
    dist (f x) (f y) / dist x y ≤ L := by
  by_cases hxy : x = y
  · simp [hxy]
  · exact (div_le_iff₀ (dist_pos.mpr hxy)).mpr (hf.dist_le_mul x hx y hy)

theorem quotients_bounded {f : M → N} {S : Set M} {L : ℝ≥0}
    (hf : LipschitzOnWith L f S) : BddAbove (quotients f S) := by
  refine ⟨L,?_⟩
  rintro r (rfl | ⟨x,hx,y,hy,rfl⟩)
  · exact L.coe_nonneg
  · exact quotient_le hf hx hy

theorem constant_nonneg {f : M → N} {S : Set M} {L : ℝ≥0}
    (hf : LipschitzOnWith L f S) : 0 ≤ constant f S :=
  le_csSup (quotients_bounded hf) (Or.inl rfl)

end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} [MetricSpace M]

end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalGeometry
open CoordinateSpaces LocalLipschitz
variable {M : Type uM} [MetricSpace M] {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

def LocalOrthogonality (D : M → Hilbert (ι := ι)) : Prop :=
  ∀ {I : Type} [Fintype I], ∀ z : I → M, Function.Injective z →
    ∃ r : ℝ, 0 < r ∧ ∃ l : ℕ, ∃ S : I → Set (Σ n, ι n),
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      ∀ i x, x ∈ Metric.ball (z i) r → tail l (D x) ∈ space (S i)

end LipschitzCounterexample.LocalGeometry
namespace LipschitzCounterexample.LocalGeometry
open CoordinateSpaces LocalLipschitz
variable {M : Type uM} [MetricSpace M] {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

def badSet {B : Type uB} (O : B → Set M) (a : B → ℝ) (η : ℝ) : Set M :=
  {z | ∀ j, z ∈ O j → η ≤ a j}

end LipschitzCounterexample.LocalGeometry

end

end OAI


