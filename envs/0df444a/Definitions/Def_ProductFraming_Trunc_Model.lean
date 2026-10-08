-- Prove2me | Definitions.Def_ProductFraming_Trunc_Model
-- name    : ProductFraming_Trunc_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:15:32.781197+00:00
-- url     : https://prove2.me/theorems/56a4269c-4362-4091-8765-98d4cd9effc3
-- title:
--   Type-dependent framing: $R_x(S)$ (8), $U(x)$ (9), $V^{OPT}$, Assumptions B1–B2, TRUNC(y) runs
-- statement:
--   In the type-dependent framing model, a consumer who views $x$ pages (a consumer **of type $x$**) chooses according to her own choice model $P_x(i,S)$. Product $i$ has revenue $r_i$.
--
--   1. The expected revenue from presenting assortment $S$ to a consumer of type $x$ is (eq. (8))
--   $$R_x(S)=\sum_{i\in S}r_iP_x(i,S).$$
--   2. The optimal revenue of the capacitated assortment problem for type $x$ is (eq. (9))
--   $$U(x)=\max_{S\subseteq[n],\ |S|\le x\cdot p}R_x(S).$$
--   3. The expected revenue of a framing $f$ is $V(f)=\sum_{x\in[m]}\lambda(x)\,R_x(C_f(x))$, where $C_f(x)$ is the consideration set of a consumer who views $x$ pages, and $V^{OPT}$ is the maximum of $V(f)$ over all feasible framings (problem (1) with $P$ replaced by $P_x$).
--   4. **Assumption B1**: $R_x(S)\le R_y(S)$ for all $1\le x\le y\le m$ and all $S$ with $|S|\le x\cdot p$.
--   5. **Assumption B2**: $U(x)/x$ is decreasing (nonincreasing) in $x\in[m]$.
--   6. A **run of TRUNC($y$)**, $y\in[m]$, is a pair $(S,f)$ where $S$ is an optimal solution of (9) for $x=y$ (so $|S|\le y\cdot p$ and $R_y(S)=U(y)$), and $f$ is a feasible framing that places exactly the products of $S$ on pages $1,\dots,y$, in any arrangement, and leaves pages $y+1,\dots,m$ blank.
--
--   These objects describe the setting of Theorem 4 of the paper and of the TRUNC algorithm.
--
--   **Formalization Note** The type-dependent choice model is `Pt : ℕ → Fin n → Finset (Fin n) → ℝ` with `Pt x i S` $=P_x(i,S)$. Both maxima are taken over finite nonempty families (the empty assortment and the empty framing are feasible), so they exist. Assumption B3 (= A2, an approximate oracle for (9)) is used in the paper with $\epsilon=0$; a TRUNC run therefore uses an exact optimum of (9). TRUNC's arbitrary choices (which optimal $S$, which arrangement) are encoded as a predicate on the output rather than as a function.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, §6, (8), (9), Assumptions B1–B3, p. 13; §6.1, TRUNC(y), p. 14; (1), p. 6

import Mathlib
import Definitions.Def_ProductFraming_Trunc_Framing
open Finset

namespace ProductFraming.Trunc

/-! Product framing with type-dependent choice models (§6, pp. 13–14) and the TRUNC(y)
algorithm (§6.1, p. 14). A consumer of type `x` views `x` pages and chooses according to
`Pt x`, i.e. `Pt x i S = P_x(i,S)`. -/

/-- `R_x(S) = ∑_{i ∈ S} r_i P_x(i,S)`, eq. (8), p. 13. -/
def Rt {n : ℕ} (r : Fin n → ℝ) (Pt : ℕ → Fin n → Finset (Fin n) → ℝ) (x : ℕ)
    (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, r i * Pt x i S

/-- `U(x) = max_{S ⊆ [n], |S| ≤ x·p} R_x(S)`, eq. (9), p. 13. The feasible family is finite and
contains `∅`, so the maximum exists. -/
noncomputable def Ut {n : ℕ} (p : ℕ) (r : Fin n → ℝ) (Pt : ℕ → Fin n → Finset (Fin n) → ℝ)
    (x : ℕ) : ℝ :=
  (univ.filter (fun S : Finset (Fin n) => S.card ≤ x * p)).sup' ⟨∅, by simp⟩ (Rt r Pt x)

/-- Expected revenue of the framing `f` when a consumer viewing `x` pages chooses by `P_x`:
`∑_{x ∈ [m]} λ(x) R_x({k : k is on pages 1, …, x})`, the objective of (1) with `P` replaced by
`P_x` (§6, p. 13). -/
def Vt {n : ℕ} (m : ℕ) (lam : ℕ → ℝ) (r : Fin n → ℝ) (Pt : ℕ → Fin n → Finset (Fin n) → ℝ)
    (f : Fin n → ℕ) : ℝ :=
  ∑ x ∈ Icc 1 m, lam x * Rt r Pt x (ProductFraming.Nest.consideration f x)

open Classical in
/-- `V^OPT`, the optimal value of (1) with type-dependent choice: the maximum of `Vt` over all
feasible framings. A framing is enumerated as `g : Fin n → Fin (m+1)` (page `0` = not
displayed); the empty framing is feasible, so the maximum is over a finite nonempty set. -/
noncomputable def VoptT {n : ℕ} (m p : ℕ) (lam : ℕ → ℝ) (r : Fin n → ℝ)
    (Pt : ℕ → Fin n → Finset (Fin n) → ℝ) : ℝ :=
  (univ.filter (fun g : Fin n → Fin (m + 1) => Feasible m p (fun i => (g i : ℕ)))).sup'
    ⟨fun _ => 0, by
      refine mem_filter.mpr ⟨mem_univ _, fun _ => by simp, fun x hx => ?_⟩
      simp only [mem_Icc] at hx
      exact (card_eq_zero.mpr (filter_eq_empty_iff.mpr (fun i _ => by simp; omega))).le.trans
        (Nat.zero_le p)⟩
    (fun g => Vt m lam r Pt (fun i => (g i : ℕ)))

/-- Assumption B1 (p. 13): `R_x(S) ≤ R_y(S)` for all `x ≤ y` in `[m]` and `S ⊆ [n]` with
`|S| ≤ x·p`. -/
def AssumptionB1 {n : ℕ} (m p : ℕ) (r : Fin n → ℝ) (Pt : ℕ → Fin n → Finset (Fin n) → ℝ) :
    Prop :=
  ∀ x y : ℕ, ∀ S : Finset (Fin n), 1 ≤ x → x ≤ y → y ≤ m → S.card ≤ x * p →
    Rt r Pt x S ≤ Rt r Pt y S

/-- Assumption B2 (p. 13): `U(x)/x` is decreasing (nonincreasing) in `x ∈ [m]`. -/
def AssumptionB2 {n : ℕ} (m p : ℕ) (r : Fin n → ℝ) (Pt : ℕ → Fin n → Finset (Fin n) → ℝ) :
    Prop :=
  ∀ x ∈ Icc 1 m, ∀ x' ∈ Icc 1 m, x ≤ x' → Ut p r Pt x' / (x' : ℝ) ≤ Ut p r Pt x / (x : ℝ)

/-- An output of TRUNC(y) (§6.1, p. 14), with Assumption B3 = A2 taken with `ε = 0` (p. 8):
1. `S` is an optimal solution of (9) for `x = y`: `|S| ≤ y·p` and `R_y(S) = U(y)`;
2. `f` is a feasible framing whose first `y` pages hold exactly the products of `S`
   (any arrangement, "any heuristic");
3. pages `y+1, …, m` are blank (every product is on a page `≤ y` or not displayed). -/
def IsTruncRun {n : ℕ} (m p : ℕ) (r : Fin n → ℝ) (Pt : ℕ → Fin n → Finset (Fin n) → ℝ)
    (y : ℕ) (S : Finset (Fin n)) (f : Fin n → ℕ) : Prop :=
  S.card ≤ y * p ∧ Rt r Pt y S = Ut p r Pt y ∧
  Feasible m p f ∧ ProductFraming.Nest.consideration f y = S ∧ ∀ i, f i ≤ y

end ProductFraming.Trunc


