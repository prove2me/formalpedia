-- Prove2me | Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_MatrixEntries
-- name    : OAI_Analysis_CStarAlgebra_PureInfiniteness_MatrixEntries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:01:20.856109+00:00
-- url     : https://prove2.me/theorems/1cfdc0c1-a6dd-4f55-94c8-fb8ad297a7f0
-- title:
--   Matrix entries and finite corner blocks of elements of the stabilization
-- statement:
--   Let $A$ be a possibly non-unital C$^*$-algebra. For $n\in\mathbb{N}$ let $M_n(A)$ be the C$^*$-algebra of $n\times n$ matrices over $A$, with rows and columns indexed by $0,\dots,n-1$. For $n\le m$ the corner embedding $M_n(A)\to M_m(A)$ places an $n\times n$ matrix in the upper-left corner and fills the remaining entries with $0$; it is an isometric $*$-homomorphism. The algebraic direct limit $M_\infty(A)$ of these embeddings is normed by the norms of representatives. Its completion $\mathcal{S}(A)$ is the stabilization of $A$, and $\iota_n:M_n(A)\to\mathcal{S}(A)$ denotes the canonical map. The file introduces four objects.
--
--   1. **Padded entries.** For $i,j\in\mathbb{N}$ and $x\in M_n(A)$, let $\hat x_{ij}=x_{ij}$ if $i<n$ and $j<n$, and $\hat x_{ij}=0$ otherwise. Padded entries are unchanged by the corner embeddings.
--
--   2. **Entry maps on the algebraic limit.** For $i,j\in\mathbb{N}$, the map $E_{ij}:M_\infty(A)\to A$ sending the class of $x\in M_n(A)$ to $\hat x_{ij}$. It is well defined, $\mathbb{C}$-linear, and satisfies $\|E_{ij}(y)\|\le\|y\|$, so it is a bounded linear map of norm at most $1$.
--
--   3. **Entry maps on the stabilization.** The unique continuous extension $E_{ij}:\mathcal{S}(A)\to A$ of the previous map to the completion. It satisfies
--   $$E_{ij}\bigl(\iota_n(x)\bigr)=\hat x_{ij}\qquad(x\in M_n(A)).$$
--
--   4. **Finite blocks.** For $m,n\in\mathbb{N}$ and $y\in\mathcal{S}(A)$, the $m\times n$ matrix
--   $$\operatorname{block}_{m,n}(y)=\bigl(E_{ij}(y)\bigr)_{0\le i<m,\ 0\le j<n},$$
--   which recovers corner matrices: $\operatorname{block}_{n,n}(\iota_n(x))=x$ for $x\in M_n(A)$.
--
--   Blocks are how statements about the stabilization are pulled back to finite matrices over $A$. An example is Cuntz comparison $r_j^*\,\iota_m(v)\,r_j\to\iota_n(d)$ with $r_j\in\mathcal{S}(A)$. The module shows that $\operatorname{block}_{n,n}(y^*\iota_m(v)\,y)=\operatorname{block}_{m,n}(y)^*\,v\,\operatorname{block}_{m,n}(y)$, so comparison in $\mathcal{S}(A)$ becomes comparison of finite matrices.
--
--   **Formalization Note** The objects are `paddedEntry`, `entryAlgLinear`, `entryAlg` (made continuous by `mkContinuous` with bound $1$), `entry` (defined by `UniformSpace.Completion.extension`) and `block`. The lemmas `paddedEntry_pad`, `entryAlgLinear_corner`, `norm_entryAlgLinear_le`, `entry_coe`, `entry_corner`, `block_apply` and `block_corner_self` record the stated identities. The file also contains local spectral-order instances, local topology instances on the algebraic limit, and a private compatibility lemma `dite_eq_left`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/MatrixEntries.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/MatrixEntries.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the IndividualStrongInfiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Ultrafilter
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Avoidance
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Graph
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Nonvanishing
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Compression
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Shrinking
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Products
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Separation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealDetection
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealComparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Signal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Diagonalization

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap.Stable
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance matrixEntryOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance matrixEntryStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance algebraicTopology' : TopologicalSpace (Algebraic A) :=
  (inferInstance : PseudoMetricSpace (Algebraic A)).toUniformSpace.toTopologicalSpace

def paddedEntry (i j n : ℕ) (x : Mat A n) : A :=
  if hi : i < n then if hj : j < n then x ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0

lemma paddedEntry_pad (i j : ℕ) {n m : ℕ} (h : n ≤ m) (x : Mat A n) :
    paddedEntry i j m (pad h x) = paddedEntry i j n x := by
  by_cases hi : i < n <;> by_cases hj : j < n
  · have hi' := lt_of_lt_of_le hi h
    have hj' := lt_of_lt_of_le hj h
    simp [paddedEntry, hi, hj, hi', hj', pad_entry]
  · by_cases hi' : i < m <;> by_cases hj' : j < m <;>
      simp [paddedEntry, hi, hj, hi', hj', pad_entry]
  · by_cases hi' : i < m <;> by_cases hj' : j < m <;>
      simp [paddedEntry, hi, hi', hj', pad_entry]
  · by_cases hi' : i < m <;> by_cases hj' : j < m <;>
      simp [paddedEntry, hi, hi', hj', pad_entry]

def entryAlgLinear (i j : ℕ) : Algebraic A →ₗ[ℂ] A where
  toFun := DirectLimit.lift _ (paddedEntry i j) (fun _ _ h x => (paddedEntry_pad i j h x).symm)
  map_add' := DirectLimit.induction₂ _ fun n x y => by
    rw [DirectLimit.add_def]
    change paddedEntry i j n (x+y) = paddedEntry i j n x + paddedEntry i j n y
    by_cases hi : i < n <;> by_cases hj : j < n <;> simp [paddedEntry, hi, hj]
  map_smul' c := DirectLimit.induction _ fun n x => by
    rw [DirectLimit.smul_def]
    change paddedEntry i j n (c • x) = c • paddedEntry i j n x
    by_cases hi : i < n <;> by_cases hj : j < n <;> simp [paddedEntry, hi, hj]

@[simp] lemma entryAlgLinear_corner (i j n : ℕ) (x : Mat A n) :
    entryAlgLinear i j (cornerAlg n x) = paddedEntry i j n x := rfl

lemma norm_entryAlgLinear_le (i j : ℕ) (x : Algebraic A) :
    ‖entryAlgLinear i j x‖ ≤ ‖x‖ := by
  induction x using DirectLimit.induction with
  | ih n x =>
    change ‖paddedEntry i j n x‖ ≤ ‖x‖
    by_cases hi : i < n <;> by_cases hj : j < n
    · simpa [paddedEntry, hi, hj] using
        (CStarMatrix.norm_entry_le_norm (M := x) (i := ⟨i,hi⟩) (j := ⟨j,hj⟩))
    all_goals simp [paddedEntry, hi, hj]

def entryAlg (i j : ℕ) : Algebraic A →L[ℂ] A :=
  (entryAlgLinear i j).mkContinuous 1 (fun x => by simpa using norm_entryAlgLinear_le i j x)

def entry (i j : ℕ) : Stabilization A → A :=
  UniformSpace.Completion.extension (entryAlg (A := A) i j)

@[simp] lemma entry_coe (i j : ℕ) (x : Algebraic A) :
    entry i j (x : Stabilization A) = entryAlg (A := A) i j x := by
  unfold entry
  exact UniformSpace.Completion.extension_coe (f := (entryAlg (A := A) i j))
    (ContinuousLinearMap.uniformContinuous (entryAlg (A := A) i j)) x

@[simp] lemma entry_corner (i j n : ℕ) (x : Mat A n) :
    entry i j (corner n x) = paddedEntry i j n x := by
  rw [corner_apply, entry_coe]
  rfl

def block (m n : ℕ) (x : Stabilization A) : CStarMatrix (Fin m) (Fin n) A :=
  CStarMatrix.ofMatrix fun i j => entry i.val j.val x

@[simp] lemma block_apply (m n : ℕ) (x : Stabilization A) (i : Fin m) (j : Fin n) :
    block m n x i j = entry i.val j.val x := rfl

@[simp] lemma block_corner_self (n : ℕ) (x : Mat A n) : block n n (corner n x) = x := by
  ext i j
  simp only [block_apply, entry_corner, paddedEntry, dite_eq_left i.isLt, dite_eq_left j.isLt]

end MainGap.Stable

namespace MainGap.Stable
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance blockConjugateOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance blockConjugateStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance algebraicTopology'' : TopologicalSpace (Algebraic A) :=
  (inferInstance : PseudoMetricSpace (Algebraic A)).toUniformSpace.toTopologicalSpace

end MainGap.Stable

end

end OAI


