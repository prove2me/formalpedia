-- Prove2me | Definitions.Def_RandOnlineSetCover_InfoLB_Inner
-- name    : RandOnlineSetCover_InfoLB_Inner
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:40.343635+00:00
-- url     : https://prove2.me/theorems/41346617-4be8-4515-afed-6af0296bd285
-- title:
--   Inner request sequence and minimum subtree color ratio
-- statement:
--   Fix a positive integer $k$, a complete binary tree with $2k$ levels and a coloring $\chi:V\to[m]$. A root-to-leaf path $\pi=(v_1,\ldots,v_{2k})$ is specified by $2k-1$ bits. For each vertex $v$, fix an enumeration of every rooted subtree $H(v)$ with $|H(v)|<k$, including the empty subtree, without repetition. The enumeration is fixed before the path is chosen.
--
--   The requests along $\pi$ concatenate these enumerations in path order. The request indexed by $H(v)$ reveals only the incidence set
--
--   $$
--   E_{H(v)}=\{\chi(u):u\in\partial H(v)\}.
--   $$
--
--   The shared observation horizon is the maximum of the request counts over all paths. The count actually depends only on the depths, hence is constant across paths. Expected algorithm cost is the arithmetic mean over all $2^{2k-1}$ paths. Define
--
--   $$
--   \alpha(\chi)=\min_{\substack{H\text{ rooted at }v_1\\1\le |H|\le k^2}}
--   \frac{|\chi(H)|}{|H|}.
--   $$
--
--   These objects isolate exactly the random input experiment used in Observation 3.2 and Lemma 3.3. Algorithms receive the incidence sequence only; indices naming tree vertices and subtrees are discarded before observations are supplied.
--
--   **Formalization Note** The minimum is a real infimum of a finite nonempty set, containing the ratio for the singleton root; every denominator is positive. The batch-order parameter permits every fixed enumeration rather than selecting a particular lexicographic order. It cannot depend on the hidden selected leaf. Every generated request has nonempty incidence because every rooted subtree has nonempty boundary in the finite tree.
-- source:
--   Roie Levin, STOC 2027 submission #400 (October 2026), §3.1 and §3.2, pp. 3–4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/400.pdf

import Mathlib
import Definitions.Def_RandOnlineSetCover_InfoLB_Model
import Definitions.Def_RandOnlineSetCover_InfoLB_BinaryTree

namespace RandOnlineSetCover.InfoLB

/-- Root-to-leaf paths in a tree with 2k levels have 2k-1 independent bits. -/
abbrev InnerPath (k : ℕ) := Fin (2 * k - 1) → Bool

def pathVertex {k : ℕ} (π : InnerPath k) (t : Fin (2 * k)) : BinaryVertex (2 * k) :=
  ⟨t, fun i => π ⟨i.val, by omega⟩⟩

/-- One fixed enumeration per vertex, independent of the selected leaf. Every eligible
subtree appears exactly once, including the empty subtree when k is positive. -/
abbrev BatchOrder (k : ℕ) := (v : BinaryVertex (2 * k)) →
  {l : List (Finset (BinaryVertex (2 * k))) //
    l.Nodup ∧ ∀ H, H ∈ l ↔ IsRootedSubtree v H ∧ H.card < k}

def innerIndices {k : ℕ} (O : BatchOrder k) (π : InnerPath k) :
    List (BinaryVertex (2 * k) × Finset (BinaryVertex (2 * k))) :=
  (List.ofFn (pathVertex π)).flatMap fun v => (O v).val.map fun H => (v, H)

/-- Set incidences of the actual requests, in batch order. Names of vertices/subtrees
are discarded before the observations reach the online algorithm. -/
noncomputable def innerRequests {k m : ℕ} (O : BatchOrder k)
    (χ : BinaryVertex (2 * k) → Fin m) (π : InnerPath k) : List (Finset (Fin m)) :=
  (innerIndices O π).map fun e => (boundary e.1 e.2).image χ

/-- A finite common observation horizon. In fact all paths have the same request count:
subtree counts depend only on depth. Taking the maximum does not assume that fact. -/
noncomputable def innerHorizon {k : ℕ} (O : BatchOrder k) : ℕ :=
  Finset.univ.sup fun π : InnerPath k => (innerIndices O π).length

/-- Uniform leaf expectation; denominator is always a positive power of two. -/
noncomputable def innerExpectedCost {k m : ℕ} (O : BatchOrder k)
    (χ : BinaryVertex (2 * k) → Fin m) (A : DetAlg m (innerHorizon O)) : ℝ :=
  (∑ π : InnerPath k, (listCost A (innerRequests O χ π) : ℝ)) /
    (Fintype.card (InnerPath k) : ℝ)

/-- Literal minimum of the colors-per-vertex ratios of root subtrees of sizes 1..k².
For k>0 this is a finite nonempty set (it contains the singleton root). -/
noncomputable def minimumColorRatio {k m : ℕ} (hk : 0 < k)
    (χ : BinaryVertex (2 * k) → Fin m) : ℝ :=
  sInf {r : ℝ | ∃ H : Finset (BinaryVertex (2 * k)),
    IsRootedSubtree (treeRoot (2 * k) (by omega)) H ∧
    1 ≤ H.card ∧ H.card ≤ k ^ 2 ∧ r = (subtreeColors χ H).card / (H.card : ℝ)}

end RandOnlineSetCover.InfoLB


