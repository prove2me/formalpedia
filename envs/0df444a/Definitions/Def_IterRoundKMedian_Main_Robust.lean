-- Prove2me | Definitions.Def_IterRoundKMedian_Main_Robust
-- name    : IterRoundKMedian_Main_Robust
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:27:09.880256+00:00
-- url     : https://prove2.me/theorems/c51680a4-57a0-47ec-8544-23b3240faec8
-- title:
--   The robust algorithm of §7: complete fractional solutions, threshold radii, filtering, bundles, greedy matching and the dependent-rounding properties (85)–(89)
-- statement:
--   A **complete fractional solution** is a finite point set with a pseudometric $d$ (colocated copies allowed), clients $C$ and facilities $F$, openings $y_i\in[0,1]$ with $y(F)\ge1$, and an assignment $x_{ij}\in\{0,y_i\}$ with $\sum_{i\in F}x_{ij}=1$ for every client; $F_j=\{i\in F:x_{ij}>0\}$ and $V_j=\sum_{i\in F}x_{ij}d(i,j)$.
--
--   **Threshold radii.** $R_j$ is an admissible radius minimizing $R+5e\,T_j(R)$ (as in `ClientProfile`), and $A_j=R_j+5e\,T_j(R_j)$.
--
--   **Filtering.** Starting from all clients, repeatedly select a remaining client $r$ with minimum $A_r$ as a representative and remove every remaining client $j$ with $d(j,r)\le 2\max\{R_j,R_r\}$; $\mathcal R$ is the list of representatives.
--
--   **Bundles.** For $r\in\mathcal R$, $B_r=\tfrac12 d(r,\mathcal R\setminus\{r\})$ ($B_r=\infty$ if $\mathcal R=\{r\}$) and $U_r=\{i\in F_r: d(i,r)<B_r\}$.
--
--   **Greedy matching.** Repeatedly match two closest distinct unmatched representatives, until at most one is unmatched.
--
--   **Dependent rounding.** A law of $Y\in\{0,1\}^{P}$ with, in every outcome, $Y(F)\in\{\lfloor y(F)\rfloor,\lceil y(F)\rceil\}$ (85), $Y(U_r)\in\{\lfloor y(U_r)\rfloor,\lceil y(U_r)\rceil\}$ for $r\in\mathcal R$ (87) and $Y(U_r\cup U_s)\ge1$ for matched $\{r,s\}$ (88); with $\mathbb E[Y_i]=y_i$ for $i\in F$ (86); and with $\Pr(F_{\rm open}\cap S=\emptyset)\le\prod_{i\in S}(1-y_i)$ for every $S\subseteq F$ (89), where $F_{\rm open}=\{i\in F:Y_i=1\}$.
--
--   **Formalization Note.** Namespace `Robust`: `Solution`, `wt`, `Vj`, `Fsupp`, `IsThreshold`, `assurance`, `FilterRun` and `GreedyMatching` (inductive runs; ties arbitrary), `bundle`, `Fopen`, `distOpen` ($d(j,F_{\rm open})$, $0$ if nothing is open, an outcome of probability $0$ by (85)), `IsRobustRounding`. “In every outcome” means every outcome of positive probability.
-- source:
--   Byrka, Guo, Hu, Li, Shin, Vajanopath, Wan, Wang, Iterative Randomized Rounding for k-Median in General and Euclidean Metrics, STOC 2027 submission (manuscript sha256 02f6267b…), pp. 64–68, §7.1–7.2, (84)–(89)

import Mathlib
import Definitions.Def_IterRoundKMedian_Main_PipageLaw
import Definitions.Def_IterRoundKMedian_Main_ClientProfile

namespace IterRoundKMedian.Main
namespace Robust

/-- A complete fractional solution (§7): a finite point set `P` with a pseudometric `d`
(distinct points may be at distance `0`: colocated copies created by facility splitting),
clients `C` and facilities `F` (subsets of `P`, possibly overlapping), openings `y_i ∈ [0,1]`
for `i ∈ F` with `y(F) ≥ 1`, and an assignment `x i j` (amount of client `j` served by `i`)
that is complete, `x_{ij} ∈ {0, y_i}`, and serves every client fully, `Σ_{i∈F} x_{ij} = 1`. -/
structure Solution (P : Type*) [Fintype P] where
  d : P → P → ℝ
  d_nonneg : ∀ a b, 0 ≤ d a b
  d_self : ∀ a, d a a = 0
  d_symm : ∀ a b, d a b = d b a
  d_triangle : ∀ a b c, d a c ≤ d a b + d b c
  C : Finset P
  F : Finset P
  y : P → ℝ
  x : P → P → ℝ
  y_nonneg : ∀ i ∈ F, 0 ≤ y i
  y_le_one : ∀ i ∈ F, y i ≤ 1
  x_complete : ∀ j ∈ C, ∀ i ∈ F, x i j = 0 ∨ x i j = y i
  x_sum : ∀ j ∈ C, ∑ i ∈ F, x i j = 1
  yF_ge_one : 1 ≤ ∑ i ∈ F, y i

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The support weights of client `j`: `x_{ij}` on `F`, `0` elsewhere (so `F_j` is the
support and the weight of `i ∈ F_j` is `y_i`). -/
def wt (S : Solution P) (j : P) (i : P) : ℝ := if i ∈ S.F then S.x i j else 0

/-- The distances `d(i, j)` of client `j`. -/
def distFrom (S : Solution P) (j : P) (i : P) : ℝ := S.d i j

/-- `V_j`. -/
def Vj (S : Solution P) (j : P) : ℝ := ClientProfile.V (wt S j) (distFrom S j)

/-- `F_j = {i ∈ F : x_{ij} > 0}`. -/
noncomputable def Fsupp (S : Solution P) (j : P) : Finset P := by
  classical
  exact S.F.filter (fun i => 0 < S.x i j)

/-- `R` is a threshold radius for `j`: admissible (84) and minimizing `R + 5e·T_j(R)` over
the admissible radii. -/
def IsThreshold (S : Solution P) (j : P) (R : ℝ) : Prop :=
  ClientProfile.Admissible (wt S j) (distFrom S j) R ∧
    ∀ R', ClientProfile.Admissible (wt S j) (distFrom S j) R' →
      R + 5 * Real.exp 1 * ClientProfile.T (wt S j) (distFrom S j) R ≤
        R' + 5 * Real.exp 1 * ClientProfile.T (wt S j) (distFrom S j) R'

/-- The assurance radius `A_j = R_j + 5e·T_j(R_j)` for a chosen threshold radius `R_j`. -/
noncomputable def assurance (S : Solution P) (Rad : P → ℝ) (j : P) : ℝ :=
  Rad j + 5 * Real.exp 1 * ClientProfile.T (wt S j) (distFrom S j) (Rad j)

/-- A run of the filtering procedure (§7.2) from the set `rem` of remaining clients,
selecting the representatives `reps` in order: while clients remain, pick a remaining `r`
with minimum `A_r` (ties arbitrary) and remove every remaining `j` with
`d(j, r) ≤ 2 max{R_j, R_r}`. -/
inductive FilterRun (S : Solution P) (Rad : P → ℝ) : Finset P → List P → Prop
  | done : FilterRun S Rad ∅ []
  | step (rem : Finset P) (r : P) (reps : List P) (hr : r ∈ rem)
      (hmin : ∀ j ∈ rem, assurance S Rad r ≤ assurance S Rad j)
      (hrest : FilterRun S Rad
        (by classical exact rem.filter (fun j => ¬ S.d j r ≤ 2 * max (Rad j) (Rad r))) reps) :
      FilterRun S Rad rem (r :: reps)

/-- The bundle `U_r = {i ∈ F_r : d(i, r) < B_r}` with `B_r = d(r, R ∖ {r})/2`
(`B_r = ∞` when `R = {r}`), written as `2 d(i,r) < d(r,s)` for every other
representative `s`. -/
noncomputable def bundle (S : Solution P) (reps : List P) (r : P) : Finset P := by
  classical
  exact (Fsupp S r).filter (fun i => ∀ s ∈ reps, s ≠ r → 2 * S.d i r < S.d r s)

/-- A run of the greedy matching (§7.2) on the set `unm` of unmatched representatives:
repeatedly match two closest distinct unmatched representatives (ties arbitrary) until at
most one is left. -/
inductive GreedyMatching (S : Solution P) : Finset P → List (P × P) → Prop
  | done (unm : Finset P) (h : unm.card ≤ 1) : GreedyMatching S unm []
  | step (unm : Finset P) (r s : P) (M : List (P × P)) (hr : r ∈ unm) (hs : s ∈ unm)
      (hrs : r ≠ s)
      (hclosest : ∀ a ∈ unm, ∀ b ∈ unm, a ≠ b → S.d r s ≤ S.d a b)
      (hrest : GreedyMatching S (by classical exact unm \ {r, s}) M) :
      GreedyMatching S unm ((r, s) :: M)

/-- The opened set `F_open = {i ∈ F : Y_i = 1}`. -/
noncomputable def Fopen (S : Solution P) (Y : P → Bool) : Finset P := by
  classical
  exact S.F.filter (fun i => Y i = true)

/-- `Y(A) = Σ_{i∈A} Y_i`. -/
def Ysum (Y : P → Bool) (A : Finset P) : ℝ := ∑ i ∈ A, bitVal (Y i)

/-- `d(j, F_open)` (value `0` if nothing is open, which has probability `0` under (85)). -/
noncomputable def distOpen (S : Solution P) (Y : P → Bool) (j : P) : ℝ :=
  if h : (Fopen S Y).Nonempty then ((Fopen S Y).image (fun i => S.d j i)).min' (h.image _)
  else 0

/-- The dependent rounding of §7.2 on the laminar family
`{F} ∪ {U_r ∪ U_s : {r,s} ∈ M} ∪ {U_r : r ∈ R}`: a law `μ` of `Y ∈ {0,1}^P` with,
in every outcome of positive probability, (85) `Y(F) ∈ {⌊y(F)⌋, ⌈y(F)⌉}`,
(87) `Y(U_r) ∈ {⌊y(U_r)⌋, ⌈y(U_r)⌉}` for `r ∈ R`, (88) `Y(U_r ∪ U_s) ≥ 1` for
`{r,s} ∈ M`; the marginals (86) `E[Y_i] = y_i` for `i ∈ F`; and the negative correlation
(89) `Pr(F_open ∩ S = ∅) ≤ ∏_{i∈S}(1 − y_i)` for every `S ⊆ F`. -/
structure IsRobustRounding (S : Solution P) (reps : List P) (M : List (P × P))
    (μ : FinLaw (P → Bool)) : Prop where
  total : ∀ Y, μ.prob Y ≠ 0 →
    Ysum Y S.F = (⌊∑ i ∈ S.F, S.y i⌋ : ℝ) ∨ Ysum Y S.F = (⌈∑ i ∈ S.F, S.y i⌉ : ℝ)
  marginal : ∀ i ∈ S.F, μ.expect (fun Y => bitVal (Y i)) = S.y i
  bundle_total : ∀ r ∈ reps, ∀ Y, μ.prob Y ≠ 0 →
    Ysum Y (bundle S reps r) = (⌊∑ i ∈ bundle S reps r, S.y i⌋ : ℝ) ∨
      Ysum Y (bundle S reps r) = (⌈∑ i ∈ bundle S reps r, S.y i⌉ : ℝ)
  pair_open : ∀ p ∈ M, ∀ Y, μ.prob Y ≠ 0 →
    1 ≤ Ysum Y (by classical exact bundle S reps p.1 ∪ bundle S reps p.2)
  neg_corr : ∀ T ⊆ S.F,
    μ.pr (fun Y => Disjoint (Fopen S Y) T) ≤ ∏ i ∈ T, (1 - S.y i)

end Robust
end IterRoundKMedian.Main


