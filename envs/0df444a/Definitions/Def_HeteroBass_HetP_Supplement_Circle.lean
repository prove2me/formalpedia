-- Prove2me | Definitions.Def_HeteroBass_HetP_Supplement_Circle
-- name    : HeteroBass_HetP_Supplement_Circle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:27:39.929815+00:00
-- url     : https://prove2.me/theorems/fa1f52fe-f4e9-4070-89b8-b8d191d106ce
-- title:
--   §6.2 — cyclic neighbors, two-sided support and interval observations
-- statement:
--   Node labels are cyclic. Let $j+k$ denote the label obtained by adding the integer $k$ modulo $M$. A **two-sided circle** has $Q_{i,j}=0$ whenever $i\ne j$ is neither $j-1$ nor $j+1$. The two directed neighbor weights may differ and may depend on the target node; mild heterogeneity is not imposed. Diagonal matrix values do not affect the adoption process and are left unrestricted.
--
--   For natural numbers $m,n$ with $m+n+1\le M$, let $U^j_{m,n}=\{j-m,\ldots,j+n\}$. Its interval observation is
--
--   $$[S^j_{m,n}](t)=s_{U^j_{m,n}}(t).$$
--
--   These observations use the published generator-defined process. For $M=2$, the left and right neighbor are the same peer and represent one directed edge, as explicitly stipulated on p. 19. For larger circles they are distinct. The interval set removes duplicate node labels; it is only interpreted as an interval of the indicated length when that length is at most $M$.
--
--   **Formalization Note** Labels in `Fin M` are zero-based; integer remainder implements cyclic shifts without natural-number subtraction. The same support predicate covers zero individual edge weights, subject to positive total incoming influence when a theorem invokes (7).
-- source:
--   Fibich & Golan, Diffusion of new products with heterogeneous consumers, arXiv:2102.05926v3, (45), p. 18; modulo-index Remark, p. 9; coincident-neighbor convention, p. 19

import Mathlib
import Definitions.Def_HeteroBass_HetP_Supplement_Subset

namespace HeteroBass.HetP.Supplement

/-- Integer cyclic shift; the existence of j supplies M > 0. -/
def cyclicShift {M : ℕ} (j : Fin M) (k : ℤ) : Fin M :=
  ⟨(((j.val : ℤ) + k) % (M : ℤ)).toNat, by
    have hM : (0 : ℤ) < M := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
    have h0 := Int.emod_nonneg ((j.val : ℤ) + k) (ne_of_gt hM)
    have h1 := Int.emod_lt_of_pos ((j.val : ℤ) + k) hM
    omega⟩

/-- Directed weights vanish away from the cyclic neighbors; diagonal values are irrelevant. -/
def IsTwoSidedCircle {M : ℕ} (Q : Fin M → Fin M → ℝ) : Prop :=
  ∀ i j, i ≠ j → i ≠ cyclicShift j (-1) → i ≠ cyclicShift j 1 → Q i j = 0

/-- The distinct nodes in the anchored interval j-m,...,j+n. Used only at length ≤ M. -/
def intervalSet {M : ℕ} (j : Fin M) (m n : ℕ) : Finset (Fin M) :=
  (Finset.range (m + n + 1)).image (fun k : ℕ => cyclicShift j ((k : ℤ) - (m : ℤ)))

/-- Nonadoption probability of the cyclic interval, observed in the published chain. -/
noncomputable def intervalNonadoption {M : ℕ} (p : Fin M → ℝ)
    (Q : Fin M → Fin M → ℝ) (j : Fin M) (m n : ℕ) (t : ℝ) : ℝ :=
  subsetNonadoption p Q (intervalSet j m n) t

end HeteroBass.HetP.Supplement


