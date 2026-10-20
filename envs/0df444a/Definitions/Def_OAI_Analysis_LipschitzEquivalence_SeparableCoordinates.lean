-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
-- name    : OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:09:57.163198+00:00
-- url     : https://prove2.me/theorems/f95c52c9-8c71-4bd4-993c-d2f73f55d7b8
-- title:
--   Coordinate subspaces of Hilbert sums and compact reduction in free spaces
-- statement:
--   Coordinate tools for Hilbert sums $\mathcal H=\bigl(\bigoplus_n\mathbb R^{\iota_n}\bigr)_{\ell^2}$ of finite-dimensional Euclidean spaces, and a compactness property of Lipschitz-free spaces.
--
--   1. **Coordinate subspaces.** For a set $S$ of coordinates $(n,a)$, the subspace $\mathcal H_S$ consists of vectors vanishing off $S$. It is closed and contains the basis vectors $e_{(n,a)}$ for $(n,a)\in S$. Its orthogonal projection $P_S$ keeps exactly the coordinates in $S$:
--   $$
--   (P_Sx)_{n,a}=[(n,a)\in S]\,x_{n,a}.
--   $$
--   The head and tail projections keep the blocks $n<l$ and $n\ge l$ respectively.
--   2. **Supported elements.** For $K\subseteq M$ in a pointed metric space, $\mathcal F_K(M)$ is the closed span of $\delta_x$, $x\in K$. The free space has compact reduction if for every weakly null sequence $\mu_i$ and $\tau>0$ there is a compact $K\ni0$ such that every $\mu_i$ is within $\tau$ of $\mathcal F_K(M)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/SeparableCoordinates.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SeparableCoordinates.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uIndex uI uE uM

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]
abbrev Hilbert := lp (fun n => EuclideanSpace ℝ (ι n)) 2

def coord (a : Σ n, ι n) : Hilbert (ι := ι) →L[ℝ] ℝ :=
  (PiLp.proj 2 (fun _ : ι a.1 => ℝ) a.2).comp
    (lp.evalCLM ℝ (fun n => EuclideanSpace ℝ (ι n)) 2 a.1)

@[simp] theorem coord_apply (a : Σ n, ι n) (x : Hilbert (ι := ι)) : coord a x = x a.1 a.2 := rfl

def space (S : Set (Σ n, ι n)) : Submodule ℝ (Hilbert (ι := ι)) :=
  ⨅ a : {a // a ∉ S}, (coord a.val).ker

@[simp] theorem mem_space (S : Set (Σ n, ι n)) (x : Hilbert (ι := ι)) :
    x ∈ space S ↔ ∀ a, a ∉ S → x a.1 a.2 = 0 := by
  simp [space]

theorem space_isClosed (S : Set (Σ n, ι n)) : IsClosed (space S : Set (Hilbert (ι := ι))) := by
  simp only [space, Submodule.coe_iInf]
  exact isClosed_iInter (fun a => (coord a.val).isClosed_ker)

def basisVector (a : Σ n, ι n) : Hilbert (ι := ι) :=
  lp.single 2 a.1 (PiLp.single 2 a.2 (1 : ℝ))

@[simp] theorem basisVector_coord (a b : Σ n, ι n) :
    basisVector a b.1 b.2 = if a = b then 1 else 0 := by
  classical
  rcases a with ⟨n,a⟩
  rcases b with ⟨m,b⟩
  by_cases h : n = m
  · subst m
    simp [basisVector, lp.single_apply, eq_comm]
  · simp [basisVector, lp.single_apply, h, Ne.symm h]

theorem basisVector_mem {S : Set (Σ n, ι n)} {a : Σ n, ι n} (ha : a ∈ S) :
    basisVector a ∈ space S := by
  rw [mem_space]
  intro b hb
  rw [basisVector_coord, ite_eq_right]
  exact fun he => hb (he ▸ ha)

end LipschitzCounterexample.CoordinateSpaces

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

instance (S : Set (Σ n, ι n)) : CompleteSpace (space S) := (space_isClosed S).completeSpace_coe

def projection (S : Set (Σ n, ι n)) : Hilbert (ι := ι) →L[ℝ] Hilbert (ι := ι) :=
  (space S).starProjection

theorem projection_mem (S : Set (Σ n, ι n)) (x : Hilbert (ι := ι)) : projection S x ∈ space S :=
  (space S).starProjection_apply_mem x

theorem inner_projection (S : Set (Σ n, ι n)) {x : Hilbert (ι := ι)} (hx : x ∈ space S)
    (y : Hilbert (ι := ι)) : ⟪x,projection S y⟫_ℝ = ⟪x,y⟫_ℝ := by
  rw [projection, ← Submodule.inner_starProjection_left_eq_right,
    (space S).starProjection_eq_self_iff.mpr hx]

end LipschitzCounterexample.CoordinateSpaces

namespace LipschitzCounterexample.HilbertSlots
open scoped ENNReal NNReal InnerProductSpace Topology
variable {E : ℕ → Type uE} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]

@[simp] theorem cutHead_apply (l n : ℕ) (x : HilbertSum E) :
    cutHead l x n = if n < l then x n else 0 := by
  classical
  change lp.evalCLM ℝ E 2 n (∑ i ∈ Finset.range l, lp.single 2 i (x i)) = _
  rw [map_sum]
  change (∑ i ∈ Finset.range l, (lp.single 2 i (x i)) n) = _
  simp [lp.single_apply]

@[simp] theorem tailCLM_coord (l n : ℕ) (x : HilbertSum E) :
    tailCLM l x n = if l ≤ n then x n else 0 := by
  rw [tailCLM_apply]
  change x n - cutHead l x n = _
  rw [cutHead_apply]
  split_ifs <;> simp_all
  omega
end LipschitzCounterexample.HilbertSlots

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set CoordinateSpaces

end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.FreeSpace
open scoped Topology NNReal
open Filter Set
variable {M : Type uM} [MetricSpace M] [Zero M]

def supported (K : Set M) : Submodule ℝ (Space M) :=
  (Submodule.span ℝ (point '' K)).topologicalClosure

def HasCompactReduction : Prop :=
  ∀ μ : ℕ → Space M, WeakSequences.WeakNull μ → ∀ τ : ℝ, 0 < τ →
    ∃ K : Set M, IsCompact K ∧ (0 : M) ∈ K ∧
      ∀ i, ∃ ν : Space M, ν ∈ supported K ∧ ‖μ i-ν‖ < τ

end LipschitzCounterexample.FreeSpace

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

@[simp] theorem inner_basisVector_left (a : Σ n, ι n) (x : Hilbert (ι := ι)) :
    ⟪basisVector a,x⟫_ℝ = x a.1 a.2 := by
  rw [basisVector, lp.inner_single_left]
  simp [PiLp.inner_apply]

@[simp] theorem projection_coord (S : Set (Σ n, ι n)) (x : Hilbert (ι := ι)) (a : Σ n, ι n) :
    projection S x a.1 a.2 = if a ∈ S then x a.1 a.2 else 0 := by
  by_cases ha : a ∈ S
  · rw [ite_eq_left ha]
    simpa only [inner_basisVector_left] using inner_projection S (basisVector_mem ha) x
  · rw [ite_eq_right ha]
    exact (mem_space S _).mp (projection_mem S x) a ha

def headSet (l : ℕ) : Set (Σ n, ι n) := {a | a.1 < l}
def tailSet (l : ℕ) : Set (Σ n, ι n) := {a | l ≤ a.1}
def head (l : ℕ) : Hilbert (ι := ι) →L[ℝ] Hilbert (ι := ι) := projection (headSet l)
def tail (l : ℕ) : Hilbert (ι := ι) →L[ℝ] Hilbert (ι := ι) := projection (tailSet l)

@[simp] theorem head_coord (l n : ℕ) (a : ι n) (x : Hilbert (ι := ι)) :
    head l x n a = if n < l then x n a else 0 := by
  by_cases hn : n < l <;> simpa [head,headSet,hn] using projection_coord (headSet l) x ⟨n,a⟩
@[simp] theorem tail_coord (l n : ℕ) (a : ι n) (x : Hilbert (ι := ι)) :
    tail l x n a = if l ≤ n then x n a else 0 := by
  by_cases hn : l ≤ n <;> simpa [tail,tailSet,hn] using projection_coord (tailSet l) x ⟨n,a⟩

end LipschitzCounterexample.CoordinateSpaces

end

end OAI


