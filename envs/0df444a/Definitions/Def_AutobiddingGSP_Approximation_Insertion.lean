-- Prove2me | Definitions.Def_AutobiddingGSP_Approximation_Insertion
-- name    : AutobiddingGSP_Approximation_Insertion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:26:42.667619+00:00
-- url     : https://prove2.me/theorems/eb6d6041-d458-4465-923a-336776fd0dce
-- title:
--   Heaviside correspondence, legal insertion positions, insertion probabilities, insertion encodings and the quantile coupling
-- statement:
--   $H(x)=\{0\}$ for $x<0$, $[0,1]$ at $x=0$, $\{1\}$ for $x>0$ (p. 13).
--
--   At an insertion step with earlier group bids `prev` ($p=t-1$ of them) and new bid $\beta$: $L_t=|\{s:b_s>\beta\}|$, $U_t=|\{s:b_s\ge\beta\}|$, legal positions $R_t=\{L_t,\dots,U_t\}$ (p. 12). $d$ is the nonincreasing rearrangement of `prev`. From Heaviside outputs $y_{t,j}$: $R_{t,0}=1$, $\rho_{t,j-1}=\min\{R_{t,j-1},y_{t,j}\}$, $R_{t,j}=R_{t,j-1}-\rho_{t,j-1}$, $\rho_{t,t-1}=R_{t,t-1}$ (p. 13).
--
--   An insertion encoding $\sigma$ gives each group $t$ (0-based) a position $\sigma(t)\in\{0,\dots,t\}$; `execute` inserts the groups one at a time and returns the group order. The marginal of a distribution $\pi$ over encodings at step $t$, position $r$, is $\sum_{\sigma(t)=r}\pi(\sigma)$ (p. 14).
--
--   Quantile coupling (p. 15): $F_{t,-1}=0$, $F_{t,r}=\sum_{r'\le r}\rho_{t,r'}$; all entries of $F_2,\dots,F_T$ sorted as $E_0\le\dots\le E_Q$, $Q=\sum_{t=2}^T(t+1)-1$; $w_h=E_h-E_{h-1}$, $u_h=(E_{h-1}+E_h)/2$, $\sigma_h(t)=\min\{r:F_{t,r}\ge u_h\}$; the coupling assigns weight $w_h$ to $\sigma_h$ for $h\in[Q]$.
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], §4.1, pp. 11–16 (PDF 11–16)

import Mathlib

namespace AutobiddingGSP.Approximation

open scoped BigOperators

/-- **The Heaviside correspondence** `H` (§4.1, p. 13): `H(x) = {0}` for `x < 0`, `[0, 1]` at
`x = 0`, and `{1}` for `x > 0`. A Heaviside (pseudo)gate with input `x` may output any element of
`H(x)` at a fixed point of the circuit. -/
def Hset (x : ℝ) : Set ℝ :=
  if x < 0 then {0} else if x = 0 then Set.Icc 0 1 else {1}

/-- `L_t(α) = |{s < t : b_s(α) > b_t(α)}|` (§4.1, p. 12), for the bids `prev` of the `p = t − 1`
previously inserted groups and the bid `β = b_t(α)` of the new group. -/
noncomputable def lowPos {p : ℕ} (prev : Fin p → ℝ) (β : ℝ) : ℕ :=
  (Finset.univ.filter (fun s => β < prev s)).card

/-- `U_t(α) = |{s < t : b_s(α) ≥ b_t(α)}|` (§4.1, p. 12). -/
noncomputable def highPos {p : ℕ} (prev : Fin p → ℝ) (β : ℝ) : ℕ :=
  (Finset.univ.filter (fun s => β ≤ prev s)).card

/-- Position `r` is a **legal insertion position**, `r ∈ R_t(α) = {L_t(α), …, U_t(α)}` (§4.1,
p. 12). -/
def IsLegal {p : ℕ} (prev : Fin p → ℝ) (β : ℝ) (r : ℕ) : Prop :=
  lowPos prev β ≤ r ∧ r ≤ highPos prev β

/-- `d` is the nonincreasing rearrangement `d_{t,1} ≥ ⋯ ≥ d_{t,t−1}` of the earlier bids `prev`, as
output by the sorting network (§4.1, p. 12). Index `j` (0-based) is the paper's `d_{t,j+1}`. -/
def IsDescRearrangement {p : ℕ} (prev d : Fin p → ℝ) : Prop :=
  Antitone d ∧ ∃ σ : Equiv.Perm (Fin p), ∀ j, d j = prev (σ j)

/-- The residual probability mass `R_{t,j}` (§4.1, p. 13): `R_{t,0} = 1` and
`R_{t,j} = R_{t,j−1} − min{R_{t,j−1}, y_{t,j}}`. The Heaviside outputs are `y j = y_{t,j+1}`
(0-based). -/
def residual {p : ℕ} (y : Fin p → ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => residual y j - min (residual y j) (if h : j < p then y ⟨j, h⟩ else 0)

/-- The insertion probabilities `ρ_{t,r}`, `r = 0, …, t − 1` (§4.1, p. 13):
`ρ_{t,r} = min{R_{t,r}, y_{t,r+1}}` for `r < t − 1`, and `ρ_{t,t−1} = R_{t,t−1}`
(`p = t − 1` earlier groups). -/
def insertProb {p : ℕ} (y : Fin p → ℝ) (r : Fin (p + 1)) : ℝ :=
  if h : r.val < p then min (residual y r.val) (y ⟨r.val, h⟩) else residual y p

/-- **Insertion encodings of deterministic group allocations** (§4.1, p. 14): for the groups
`g_1, …, g_T` (Lean `0, …, T − 1`), `σ t ∈ {0, …, t}` is the number of earlier groups that precede
group `t` when it is inserted (the paper's position `σ(t + 1)` in step `t + 1`; group `0` is
inserted alone). -/
abbrev InsSeq (T : ℕ) : Type := (t : Fin T) → Fin (t.val + 1)

/-- The group order produced by executing an insertion encoding: insert the groups `0, …, T − 1`
one at a time, group `t` at position `σ t` (0-based) of the current order (§4.1, p. 14). -/
def execute {T : ℕ} (σ : InsSeq T) : List (Fin T) :=
  (List.finRange T).foldl (fun L t => L.insertIdx (σ t).val t) []

/-- The insertion marginal `p_t = ∑_σ π(σ) e_{t,σ(t)}` of a distribution `π` over insertion
encodings, at step `t` and position `r` (§4.1, p. 14). -/
def marginal {T : ℕ} (π : InsSeq T → ℝ) (t : Fin T) (r : Fin (t.val + 1)) : ℝ :=
  ∑ σ ∈ Finset.univ.filter (fun σ : InsSeq T => σ t = r), π σ

/-- The bids of the groups inserted before group `t`. -/
def prevBids {T : ℕ} (b : Fin T → ℝ) (t : Fin T) : Fin t.val → ℝ :=
  fun s => b ⟨s.val, lt_trans s.isLt t.isLt⟩

/-- The cumulative probabilities (§4.1, p. 15): `cumF ρ t j = ∑_{r < j} ρ_{t,r}`, so that
`cumF ρ t 0 = F_{t,−1} = 0` and `cumF ρ t (r + 1) = F_{t,r}`. -/
def cumF {T : ℕ} (ρ : (t : Fin T) → Fin (t.val + 1) → ℝ) (t : Fin T) (j : ℕ) : ℝ :=
  ∑ r : Fin (t.val + 1), if r.val < j then ρ t r else 0

/-- `Q = ∑_{t=2}^{T} (t + 1) − 1` (§4.1, p. 15). -/
def couplingQ (T : ℕ) : ℕ := (∑ t ∈ Finset.Icc 2 T, (t + 1)) - 1

/-- All entries of `F_2, …, F_T` (each including both endpoints `F_{t,−1}` and `F_{t,t−1}`), with
repetitions, in nondecreasing order: the sorting network's output `E_0 ≤ E_1 ≤ ⋯ ≤ E_Q` (§4.1,
p. 15). In Lean the steps are `t = 1, …, T − 1` and step `t` has the `t + 2` entries
`cumF ρ t 0, …, cumF ρ t (t + 1)`. -/
noncomputable def sortedEntries {T : ℕ} (ρ : (t : Fin T) → Fin (t.val + 1) → ℝ) : List ℝ :=
  (((List.finRange T).filter (fun t => 1 ≤ t.val)).flatMap
    (fun t => (List.range (t.val + 2)).map (cumF ρ t))).mergeSort (fun x y => decide (x ≤ y))

/-- `E_h` (§4.1, p. 15). -/
noncomputable def entryE {T : ℕ} (ρ : (t : Fin T) → Fin (t.val + 1) → ℝ) (h : ℕ) : ℝ :=
  (sortedEntries ρ).getD h 0

/-- The interval length `w_h = E_h − E_{h−1}`, `h ∈ [Q]` (§4.1, p. 15). -/
noncomputable def weightW {T : ℕ} (ρ : (t : Fin T) → Fin (t.val + 1) → ℝ) (h : ℕ) : ℝ :=
  entryE ρ h - entryE ρ (h - 1)

/-- The midpoint `u_h = (E_{h−1} + E_h) / 2`, `h ∈ [Q]` (§4.1, p. 15). -/
noncomputable def midU {T : ℕ} (ρ : (t : Fin T) → Fin (t.val + 1) → ℝ) (h : ℕ) : ℝ :=
  (entryE ρ (h - 1) + entryE ρ h) / 2

/-- **The quantile selector** of Lemma 4.3 (p. 15): `σ_h(t) = min{r ∈ {0, …, t − 1} : F_{t,r} ≥ u_h}`
(Lean step `t ≥ 1`, positions `0, …, t`; the step-`0` group has the single position `0`). If no
such `r` existed the value would be the last position; this never happens because `F_{t,t−1} = 1`
and `u_h ≤ 1`. -/
noncomputable def quantileSeq {T : ℕ} (ρ : (t : Fin T) → Fin (t.val + 1) → ℝ) (h : ℕ) : InsSeq T :=
  fun t => ⟨min (((List.range (t.val + 1)).find? (fun r => decide (midU ρ h ≤ cumF ρ t (r + 1)))).getD t.val)
    t.val, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- **The quantile coupling** (Lemma 4.3, p. 15): the probability mixture assigning weight `w_h` to
the deterministic group allocation `σ_h`, for every `h ∈ [Q]`. -/
noncomputable def quantileCoupling {T : ℕ} (ρ : (t : Fin T) → Fin (t.val + 1) → ℝ) :
    InsSeq T → ℝ :=
  fun σ => ∑ h ∈ Finset.Icc 1 (couplingQ T), if quantileSeq ρ h = σ then weightW ρ h else 0

end AutobiddingGSP.Approximation


