-- Prove2me | Definitions.Def_GroupLabeledMatroid_Proximity_ContractionFiltration
-- name    : GroupLabeledMatroid_Proximity_ContractionFiltration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:14.273755+00:00
-- url     : https://prove2.me/theorems/7e8500ba-56a2-42d8-bc79-9b3fe7ce0ff5
-- title:
--   Ordered-base contraction and cost-filtered color sets
-- statement:
--   Enumerate a base $B$ in nondecreasing cost order. Lean uses indices $0,\ldots,r-1$ for the paper's $b_1,\ldots,b_r$. At stage $k$ let $P_k$ contain the first $k$ elements and $T_k=B\setminus P_k$. The associated objects are
--
--   $$M_k=M/P_k,\quad E_h^k=E_h\setminus P_k,\quad R_h^k=\{e\in E_h^k:c(e)\le c(b_k)\},$$
--   $$S_k=\{\ell(D):D\text{ base of }M_k,\ c(D)\le c(T_k)\},\quad H_k=\{h:b_k\in\operatorname{cl}_{M_k}(R_h^k)\}.$$
--
--   For the terminal stage $k=r$, define $R_h^r=E_h^r$ and $S_r=\{0\}$; no pivot or $H_r$ is defined. A cost order is injective, has image exactly $B$, and permits equal costs. These are the source's computed contractions and filtered sets, rather than free parameters satisfying desired conclusions.
--
--   **Formalization Note** Stage $k$ corresponds to the paper's stage $k+1$. The finite representation of $H_k$ filters the labels occurring on the ground. Under the standing base hypotheses each pivot is a nonloop after contracting its predecessors, so an empty color class cannot span it; the finite filter therefore gives exactly the source's set. The natural stage argument also has harmless total values beyond $r$, but every theorem uses only stages $0$ through $r$.
-- source:
--   Siyue Liu, Taihei Oki, Chao Xu, Proximity Theorem and FPT Algorithm for Minimum Group-labeled Matroid Bases, STOC 2027 submission #554 (October 2026), pp. 6–7, §3 and §3.1

import Definitions.Def_GroupLabeledMatroid_Proximity_LabelModel

namespace GroupLabeledMatroid.Proximity

variable {E G : Type*} [Fintype E] [DecidableEq E] [AddCommGroup G] [DecidableEq G]

/-- A bijective enumeration of B in nondecreasing cost order. -/
def IsCostOrder {r : ℕ} (c : E → ℝ) (B : Finset E) (b : Fin r → E) : Prop :=
  Function.Injective b ∧ Finset.univ.image b = B ∧ Monotone (fun i => c (b i))

def basePrefix {r : ℕ} (b : Fin r → E) (k : ℕ) : Finset E :=
  (Finset.univ.filter (fun j => j.val < k)).image b

def suffix {r : ℕ} (B : Finset E) (b : Fin r → E) (k : ℕ) : Finset E :=
  B \ basePrefix b k

noncomputable def stageMinor {r : ℕ} (M : Matroid E) (b : Fin r → E)
    (k : ℕ) : Matroid E := M.contract (basePrefix b k : Set E)

noncomputable def stageColor {r : ℕ} (M : Matroid E) (ℓ : E → G)
    (b : Fin r → E) (k : ℕ) (h : G) : Finset E :=
  colorClass M ℓ h \ basePrefix b k

/-- Stage r (source r+1) has no pivot and uses the whole remaining color class. -/
noncomputable def stageR {r : ℕ} (M : Matroid E) (ℓ : E → G) (c : E → ℝ)
    (b : Fin r → E) (k : ℕ) (h : G) : Finset E := by
  classical
  exact if hk : k < r then (stageColor M ℓ b k h).filter (fun e => c e ≤ c (b ⟨k, hk⟩))
    else stageColor M ℓ b k h

/-- Stage r is the specified singleton {0}, including for r=0. -/
noncomputable def stageS {r : ℕ} (M : Matroid E) (ℓ : E → G) (c : E → ℝ)
    (B : Finset E) (b : Fin r → E) (k : ℕ) : Finset G := by
  classical
  exact if k = r then {0}
    else labelsUnder (stageMinor M b k) ℓ c (costSum c (suffix B b k))

/-- In the ordered-base setting the pivot is a nonloop, so every closure color
occurs in the ground; this finite filter is exactly the source's H_i. -/
noncomputable def stageH {r : ℕ} (M : Matroid E) (ℓ : E → G) (c : E → ℝ)
    (b : Fin r → E) (i : Fin r) : Finset G := by
  classical
  exact ((ground M).image ℓ).filter
    (fun h => b i ∈ (stageMinor M b i.val).closure (stageR M ℓ c b i.val h : Set E))

end GroupLabeledMatroid.Proximity


