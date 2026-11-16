-- Prove2me | Definitions.Def_HSOSetCover_FullCover_Supplement_WSC
-- name    : HSOSetCover_FullCover_Supplement_WSC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:10:58.706076+00:00
-- url     : https://prove2.me/theorems/5f0df5bc-7a97-4fc7-9ad0-2f98cd4a0c46
-- title:
--   Weighted set cover: LP value $L$, $\mathrm{OPT}$, dual feasibility, local dual certification and certified $\rho$-covers
-- statement:
--   A **weighted set cover (WSC) instance** consists of a nonempty finite universe $U$ with $n=|U|$ elements, candidate sets $S_1,\dots,S_m\subseteq U$ whose union is $U$, and positive weights $w_1,\dots,w_m$.
--
--   Write $w(C)=\sum_{j\in C}w_j$ for $C\subseteq[m]$. $\mathrm{OPT}$ is the minimum weight of an integral cover, and $L$ is the optimum of the LP relaxation:
--   $$L=\inf\Big\{\sum_j w_jx_j:\ x\ge0,\ \sum_{S_j\ni e}x_j\ge1\ \ \forall e\in U\Big\}.$$
--   A vector $y=(y_e)_{e\in U}$ is **dual feasible** if $y\ge0$ and $\sum_{e\in S_j}y_e\le w_j$ for every $j$.
--
--   For a retained index set $C$, the residual is $R=U\setminus\bigcup_{j\in C}S_j$. A returned subfamily $P$ newly covers $N(P,R)=R\cap\bigcup_{j\in P}S_j$. It satisfies the **local dual-certification condition** for $R$ (with target $\rho$ and dual $y$) if
--   $$N(P,R)\neq\emptyset\quad\text{and}\quad w(P)\le\rho\sum_{e\in N(P,R)}y_e .$$
--   A **certified $\rho$-cover** is a cover $C$ with $w(C)\le\rho L$.
--
--   The retention rule processes returned subfamilies in order and retains each one exactly when it satisfies the local dual-certification condition for the current residual. These objects are shared by Lemma 1 and Theorems 4–6.
--
--   **Formalization Note** Candidate sets are indexed by an arbitrary finite type, in place of $[m]$. $L$ and $\mathrm{OPT}$ are real infima of nonempty sets bounded below by $0$.
-- source:
--   Jie Wang, Computing Weighted Set Covers with Heterogeneous Stochastic Oracles: Deadline-Constrained Token Complexity, STOC 2027 submission #191 (October 2026), SHA-256 d7c07e91dc65c2dd29234b0edf05fe6bcfcbee569eb1a14c07b3e0f337ca7a48, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/191.pdf, §2, PDF p. 3 / printed p. 2 (WSC instance, OPT); §3, PDF p. 4 / printed p. 3 (LP relaxation, certified ρ-cover); §5, PDF p. 9 / printed p. 8 (dual, N(P,R), local dual certification)

import Mathlib

namespace HSOSetCover.FullCover.Supplement

/-- A **weighted set cover (WSC) instance** (PDF pp. 3–4): a nonempty finite universe `U`,
candidate sets `S j ⊆ U` indexed by a finite type `ι` (the paper's `[m]`) whose union covers `U`,
and positive weights `w j`. -/
structure WSCInstance (U ι : Type*) [Fintype U] [DecidableEq U] [Fintype ι] where
  /-- The candidate set `S_j`. -/
  S : ι → Finset U
  /-- The weight `w_j`. -/
  w : ι → ℝ
  w_pos : ∀ j, 0 < w j
  univ_nonempty : (Finset.univ : Finset U).Nonempty
  covers : ∀ e, ∃ j, e ∈ S j

variable {U ι : Type*} [Fintype U] [DecidableEq U] [Fintype ι] [DecidableEq ι]
variable (W : WSCInstance U ι)

/-- The union `⋃_{h < H} P_h` of the first `H` members of a sequence of partial covers. -/
def prefixUnion (Ps : ℕ → Finset ι) (H : ℕ) : Finset ι := (Finset.range H).biUnion Ps

namespace WSCInstance

/-- `w(C) = ∑_{j ∈ C} w_j`. -/
noncomputable def weight (C : Finset ι) : ℝ := ∑ j ∈ C, W.w j

/-- The elements covered by the sets indexed by `C`. -/
def covered (C : Finset ι) : Finset U := C.biUnion W.S

/-- `C` indexes an integral cover: every element of `U` lies in some `S_j`, `j ∈ C`. -/
def IsCover (C : Finset ι) : Prop := ∀ e, ∃ j ∈ C, e ∈ W.S j

/-- The standard LP relaxation's optimum `L` (PDF p. 4): the infimum of `∑_j w_j x_j` over
`x ≥ 0` with `∑_{S_j ∋ e} x_j ≥ 1` for every `e ∈ U`. The feasible set is nonempty (`x ≡ 1`) and
the objective is bounded below by `0`. -/
noncomputable def lpValue : ℝ :=
  sInf {v | ∃ x : ι → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ e, 1 ≤ ∑ j ∈ Finset.univ.filter (fun j => e ∈ W.S j), x j) ∧
    v = ∑ j, W.w j * x j}

/-- `OPT`, the minimum weight of an integral cover (PDF p. 3). The set is nonempty (all sets) and
finite. -/
noncomputable def opt : ℝ := sInf {v | ∃ C : Finset ι, W.IsCover C ∧ v = W.weight C}

/-- A feasible solution of the dual of the LP relaxation (PDF p. 9): `y_e ≥ 0` and
`∑_{e ∈ S_j} y_e ≤ w_j` for every `j`. -/
def DualFeasible (y : U → ℝ) : Prop := (∀ e, 0 ≤ y e) ∧ ∀ j, ∑ e ∈ W.S j, y e ≤ W.w j

/-- The residual set `R = U ∖ ⋃_{j ∈ C} S_j` of the retained sets `C` (PDF p. 9). -/
def residual (C : Finset ι) : Finset U := Finset.univ \ W.covered C

/-- `N(P, R) = R ∩ ⋃_{j ∈ P} S_j`, the elements of `R` newly covered by `P` (PDF p. 9). -/
def newlyCovered (P : Finset ι) (R : Finset U) : Finset U := R ∩ W.covered P

/-- The **local dual-certification condition** (PDF p. 9): `P` satisfies it for `R` (with the
fixed target `ρ` and dual vector `y`) if `N(P, R) ≠ ∅` and `w(P) ≤ ρ ∑_{e ∈ N(P,R)} y_e`. -/
def LocalDualCert (ρ : ℝ) (y : U → ℝ) (P : Finset ι) (R : Finset U) : Prop :=
  (W.newlyCovered P R).Nonempty ∧ W.weight P ≤ ρ * ∑ e ∈ W.newlyCovered P R, y e

/-- A **certified `ρ`-cover** (PDF p. 4): a cover `C` with `w(C) ≤ ρ L`. -/
def CertifiedCover (ρ : ℝ) (C : Finset ι) : Prop := W.IsCover C ∧ W.weight C ≤ ρ * W.lpValue

open Classical in
/-- One retention step (PDF p. 9): the partial cover `P` is retained, i.e. added to the retained
sets `C`, exactly when it satisfies the local dual-certification condition for the current
residual. -/
noncomputable def retainStep (ρ : ℝ) (y : U → ℝ) (C P : Finset ι) : Finset ι :=
  if W.LocalDualCert ρ y P (W.residual C) then C ∪ P else C

/-- The sets retained after processing the responses `l` in order, starting from nothing. -/
noncomputable def retained (ρ : ℝ) (y : U → ℝ) (l : List (Finset ι)) : Finset ι :=
  l.foldl (W.retainStep ρ y) ∅

end WSCInstance

end HSOSetCover.FullCover.Supplement


