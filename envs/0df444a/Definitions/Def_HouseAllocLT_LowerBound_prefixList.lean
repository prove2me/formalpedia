-- Prove2me | Definitions.Def_HouseAllocLT_LowerBound_prefixList
-- name    : HouseAllocLT_LowerBound_prefixList
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:01:49.693079+00:00
-- url     : https://prove2.me/theorems/0094f99c-c064-4106-8395-371a393ed3d8
-- title:
--   Common-prefix instances and the independent uniform average
-- statement:
--   For $\ell\in\{1,\ldots,n\}$, $P^\ell$ ranks $a_1\succ\cdots\succ a_\ell$ strictly and declares every other object unacceptable. The domain is $D_n=\{P^1,\ldots,P^n\}$. For lengths $\boldsymbol\ell=(\ell_i)_{i=1}^n$, the associated profile is $(P^{\ell_i})_i$. Define
--
--   $$Z_h(\boldsymbol\ell)=|\{i:\ell_i\le h\}|,\qquad \Delta_n(\boldsymbol\ell)=\max_{0\le h\le n}(Z_h(\boldsymbol\ell)-h).$$
--
--   Expectation over independent uniform lengths is the exact average $n^{-n}\sum_{\boldsymbol\ell\in[n]^n} f(\boldsymbol\ell)$. These objects describe only the supporting lower-bound family.
--
--   **Formalization Note** A finite index $q$ denotes the positive length $q+1$. Truncated natural subtraction is used inside the maximum defining the nonnegative deficiency; this agrees with the integer maximum because $h=0$ supplies zero. The average is used only when $n\ge1$.
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), §3.1–3.2, prefix family and deficiency, PDF pp. 7–8 (printed pp. 5–6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_Mechanism
import Definitions.Def_HouseAllocLT_LowerBound_B

open scoped BigOperators
open Classical

namespace HouseAllocLT.LowerBound
noncomputable section

/-- §3.1: q : Fin n denotes the positive length q+1; rank j denotes j+1. -/
def prefixList {n : ℕ} (q : Fin n) : Preference n where
  length := q.val + 1
  classes := fun j => Finset.univ.filter (fun a => a.val = j ∧ j ≤ q.val)
  nonempty_iff := by
    intro j
    constructor
    · rintro ⟨a, ha⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      omega
    · intro hj
      refine ⟨⟨j, by omega⟩, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
  disjoint := by
    intro j k hjk
    apply Finset.disjoint_left.mpr
    intro a ha hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact hjk (ha.1.symm.trans hb.1)

def prefixDomain (n : ℕ) : Set (Preference n) := Set.range (@prefixList n)

def prefixProfile {n : ℕ} (ℓ : Fin n → Fin n) : Profile n n :=
  fun i => prefixList (ℓ i)

/-- Independent uniform positive lengths, encoded by their exact finite average. -/
def profileAverage {n : ℕ} (f : (Fin n → Fin n) → ℝ) : ℝ :=
  (∑ ℓ : Fin n → Fin n, f ℓ) / (n : ℝ) ^ n

def Z {n : ℕ} (ℓ : Fin n → Fin n) (h : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => (ℓ i).val + 1 ≤ h)).card

/-- max_h (Z_h - h); truncated terms give the same maximum since h=0 supplies zero. -/
def deficiency {n : ℕ} (ℓ : Fin n → Fin n) : ℕ :=
  (Finset.range (n + 1)).sup (fun h => Z ℓ h - h)

end
end HouseAllocLT.LowerBound


