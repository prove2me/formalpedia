-- Prove2me | Definitions.Def_DisplayMNL_Rounding_Model
-- name    : DisplayMNL_Rounding_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:18.156804+00:00
-- url     : https://prove2.me/theorems/e8160620-9f16-4805-9ddd-076dc582aa98
-- title:
--   §1.1, §2, §4.2–§4.4, §5.2 — MNL display model, DP action sequences with constraints (8)–(14), the rounded assignment Ã
-- statement:
--   This file sets up the display optimization model of Aouad and Segev under multinomial logit (MNL) preferences, the sequences of dynamic-programming actions of their approximation scheme, and the assignment rounded from such a sequence.
--
--   **Instance.** There are $n$ items $i\in[n]$, item $i$ having a price $r_i$ and an MNL preference weight $w_i$, and $n$ positions $k\in[n]$ with weights $\lambda_k$. Write $\rho_i=r_iw_i$, and for an assortment $S\subseteq[n]$
--   $$\rho(S)=\sum_{i\in S}\rho_i,\qquad w(S)=\sum_{i\in S}w_i,\qquad R(S)=\frac{\rho(S)}{1+w(S)} .$$
--   An assignment $\mathcal A:[n]\to[n]$ is a bijection from positions to items; $\mathcal A[k]$ is the set of items in positions $1,\dots,k$ (with $\mathcal A[0]=\emptyset$), $R_k(\mathcal A)=R(\mathcal A[k])$, and the objective is
--   $$\mathcal R(\mathcal A)=\sum_{k=1}^n\lambda_k\,R_k(\mathcal A).$$
--   For a set $J$ of positions, $\lambda(J)=\sum_{k\in J}\lambda_k$.
--
--   **Standing assumptions.** $n\ge 2$; $r_i>0$ and $w_i>0$ for every item; $\lambda_k>0$ for every position (Assumption 2.3); and the accuracy parameter satisfies $\epsilon\in(0,1/5)$ (§5).
--
--   **Unimodality.** A function $k\mapsto f(k)$ is unimodal over the integer interval $[a,b]$ if there is $m\in[a,b]$ such that $f$ is non-decreasing on $[a,m]$ and non-increasing on $[m,b]$.
--
--   **Dynamic-programming actions.** A sequence of actions consists of a length $T$, events $e_1,\dots,e_T$ and pairs $\vec S_j=(S^-_j,S^+_j)$ of item sets, with the conventions $e_{T+1}=e_T$, $\vec S_{T+1}=\vec S_T$ and $S^+_0=\emptyset$. Write
--   $$\alpha_j=\frac{\rho(S^-_j)}{1+w(S^+_j)} .$$
--   Given a guess $k_{\mathrm{mid}}$, the sequence is **feasible** if $T\ge1$, every event lies in $[n]$, the boundary case holds ($e_1=1$ and $S^-_1=S^+_1=\{i_1\}$ for some item $i_1$), the root holds ($e_T=n$ and $\vec S_T=([n],[n])$), and for every $j\in[2,T]$ the transition $(e_{j-1},\vec S_{j-1})\in\mathcal T(e_j,e_{j+1},\vec S_j,\vec S_{j+1})$ satisfies constraints (8)–(14):
--
--   1. (8) $S^-_{j-1}\subseteq S^+_{j-1}\subseteq S^+_j$;
--   2. (9) $\rho(S^+_{j-1}\setminus S^-_{j-1})\le 4\epsilon^2\rho(S^-_{j-1})$;
--   3. (10) $w(S^+_{j-1}\setminus S^-_{j-1})\le 4\epsilon^2 w(S^-_{j-1})$;
--   4. (11) $e_{j-1}\le\min\{|S^+_{j-1}|,\ e_j-|S^-_j\setminus S^+_{j-1}|\}$;
--   5. (12) $\alpha_j\ge(1+\epsilon/2)\,\alpha_{j-1}$ if $k_{\mathrm{mid}}\ge e_j$;
--   6. (13) $\alpha_{j+1}\le\min\{(1-\epsilon/2)\,\alpha_{j-1},\ (1+\epsilon/2)\,\alpha_j\}$ if $e_j\ge e_{j-1}\ge k_{\mathrm{mid}}$;
--   7. (14) $\alpha_j\ge(1-3\epsilon/2)\,\alpha_{j-1}$ if $e_j\ge k_{\mathrm{mid}}\ge e_{j-1}$.
--
--   **Rounding to an assignment (§4.4).** Let $j_{\mathrm{mid}}=\max\{j\in[T]:e_j\le k_{\mathrm{mid}}\}$. Step 1 defines
--   $$\Delta_j=S^-_j\setminus\Big(S^+_{j-1}\cup\bigcup_{t<j}\Delta_t\Big)\ \ (j\le j_{\mathrm{mid}}),\qquad \Delta_j=S^+_j\setminus\bigcup_{t<j}\Delta_t\ \ (j>j_{\mathrm{mid}}),$$
--   and $\tilde e_j=|\Delta_1\cup\dots\cup\Delta_j|$, $\tilde e_0=0$. Step 2: an assignment $\tilde{\mathcal A}$ is **rounded** from the sequence if, for every $j\in[1,T]$, $\tilde{\mathcal A}[\tilde e_j]=\Delta_1\cup\dots\cup\Delta_j$ (so $\Delta_j$ occupies positions $\tilde e_{j-1}+1,\dots,\tilde e_j$) and the prices along these positions are non-increasing.
--
--   **Intervals (proof of Lemma 5.4).** $\tilde I_j=[\tilde e_j,\tilde e_{j+1}-1]\cap[1,k_{\mathrm{mid}}]$ if $j\le j_{\mathrm{mid}}$, and $\tilde I_j=[\tilde e_{j-1}+1,\tilde e_j]\cap[k_{\mathrm{mid}}+1,n]$ if $j\ge j_{\mathrm{mid}}+1$.
--
--   These objects are the vocabulary of every statement in the mission: the revenue lower bound for $\tilde{\mathcal A}$ and the lemmas it rests on.
--
--   **Formalization Note** Items are `Fin n`; positions and DP indices are 1-based natural numbers as in the paper, and the assignment is an equivalence `Fin n ≃ Fin n` from the 0-based position $k-1$ to the item at position $k$. The DP sequence stores its data as functions on ℕ, read through accessors that clamp indices above $T$ to $T$ (the root convention) and return $S^+_0=\emptyset$. Constraint (11) is written without natural-number truncation, as $e_{j-1}\le|S^+_{j-1}|$ and $e_{j-1}+|S^-_j\setminus S^+_{j-1}|\le e_j$. The approximate assortments range over all subsets of $[n]$ rather than the families $\mathcal S^\pm(\epsilon^2)$ of Lemma 2.5, and Assumptions 2.1–2.2 enter only as positivity of prices and weights; both make every statement about feasible sequences stronger. "Rounded" allows any order among items of equal price within a block, which the paper leaves open. $j_{\mathrm{mid}}$ is `Nat.findGreatest`, equal to $0$ only when no index qualifies, which feasibility excludes.
-- source:
--   Aouad & Segev, Display Optimization for Vertically Differentiated Locations Under Multinomial Logit Preferences, SSRN 2709652 (version of 31/07/2019), pp. 3–4, 9–10, 13, 17–20, 22, §1.1 (1), §2, Assumption 2.3, Lemma 3.1 (unimodality), §4.2–§4.4 (8)–(14), §5, proof of Lemma 5.4

import Mathlib

namespace DisplayMNL.Rounding

open Finset

/-- An instance of the display optimization problem (§1.1, pp. 3–4; §2, p. 9): `n` items, item `i`
having price `r i` and MNL preference weight `w i`, and position weights `lam k` for the 1-based
positions `k ∈ [1, n]` (values of `lam` outside `[1, n]` are never used). -/
structure Instance (n : ℕ) where
  r : Fin n → ℝ
  w : Fin n → ℝ
  lam : ℕ → ℝ

variable {n : ℕ}

/-- `ρ_i = r_i · w_i` (§2, p. 9). -/
def rho (I : Instance n) (i : Fin n) : ℝ := I.r i * I.w i

/-- `ρ(S) = Σ_{i ∈ S} ρ_i`. -/
def rhoSet (I : Instance n) (S : Finset (Fin n)) : ℝ := ∑ i ∈ S, rho I i

/-- `w(S) = Σ_{i ∈ S} w_i`. -/
def wt (I : Instance n) (S : Finset (Fin n)) : ℝ := ∑ i ∈ S, I.w i

/-- MNL expected revenue of the assortment `S`: `R(S) = ρ(S) / (1 + w(S))`. -/
noncomputable def rev (I : Instance n) (S : Finset (Fin n)) : ℝ := rhoSet I S / (1 + wt I S)

/-- `A[k]`: the items displayed at the 1-based positions `1, …, k` by the assignment `A`, which maps
0-based positions to items (so 1-based position `p` holds the item `A ⟨p - 1, _⟩`). `A[0] = ∅`. -/
def pre (A : Fin n ≃ Fin n) (k : ℕ) : Finset (Fin n) :=
  (univ.filter (fun p : Fin n => p.val < k)).image A

/-- `R_k(A) = R(A[k])`. -/
noncomputable def revAt (I : Instance n) (A : Fin n ≃ Fin n) (k : ℕ) : ℝ := rev I (pre A k)

/-- The objective (1): `R(A) = Σ_{k=1}^n λ_k · R_k(A)`. -/
noncomputable def totalRev (I : Instance n) (A : Fin n ≃ Fin n) : ℝ :=
  ∑ k ∈ Icc 1 n, I.lam k * revAt I A k

/-- `λ(J) = Σ_{k ∈ J} λ_k` for a set `J` of 1-based positions. -/
def lamSum (I : Instance n) (J : Finset ℕ) : ℝ := ∑ k ∈ J, I.lam k

/-- Standing assumptions: at least two items (needed for `1 ≤ k_mid ≤ n - 1`), positive prices and
weights (§1.1, p. 3; what Assumptions 2.1–2.2 are used for), positive position weights
(Assumption 2.3, p. 10), and the accuracy `ε ∈ (0, 1/5)` (§5, p. 20). -/
def Standing (I : Instance n) (ε : ℝ) : Prop :=
  2 ≤ n ∧ (∀ i, 0 < I.r i) ∧ (∀ i, 0 < I.w i) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ n → 0 < I.lam k) ∧ 0 < ε ∧ ε < 1 / 5

/-- `f` is unimodal over the integer interval `[a, b]` (as in Lemma 3.1, p. 13): for some
`m ∈ [a, b]`, `f` is non-decreasing on `[a, m]` and non-increasing on `[m, b]`. -/
def IsUnimodalOn (f : ℕ → ℝ) (a b : ℕ) : Prop :=
  ∃ m, a ≤ m ∧ m ≤ b ∧
    (∀ k l, a ≤ k → k ≤ l → l ≤ m → f k ≤ f l) ∧
    (∀ k l, m ≤ k → k ≤ l → l ≤ b → f l ≤ f k)

/-- A sequence of dynamic-programming actions (§4.2, p. 17; §4.4, p. 19): a length `T`, events
`e j` and pairs `(S⁻_j, S⁺_j) = (Sm j, Sp j)` for the 1-based indices `j ∈ [1, T]`. Values at other
indices are read only through the accessors `ev`, `sm`, `sp`. -/
structure DPSeq (n : ℕ) where
  T : ℕ
  e : ℕ → ℕ
  Sm : ℕ → Finset (Fin n)
  Sp : ℕ → Finset (Fin n)

namespace DPSeq

/-- `e_j`, with the root convention `e_{T+1} = e_T` (p. 18): indices above `T` read `e_T`. -/
def ev (s : DPSeq n) (j : ℕ) : ℕ := s.e (min j s.T)

/-- `S⁻_j`, with the root convention `S⁻_{T+1} = S⁻_T` (p. 18). -/
def sm (s : DPSeq n) (j : ℕ) : Finset (Fin n) := s.Sm (min j s.T)

/-- `S⁺_j`, with `S⁺_0 = ∅` (§4.4, p. 19; App. C.5, p. 48) and the root convention
`S⁺_{T+1} = S⁺_T` (p. 18). -/
def sp (s : DPSeq n) (j : ℕ) : Finset (Fin n) := if j = 0 then ∅ else s.Sp (min j s.T)

end DPSeq

open DPSeq

/-- `α_j = ρ(S⁻_j) / (1 + w(S⁺_j))` (App. C.8, p. 49 notation; the immediate reward of (7)). -/
noncomputable def alpha (I : Instance n) (s : DPSeq n) (j : ℕ) : ℝ :=
  rhoSet I (s.sm j) / (1 + wt I (s.sp j))

/-- The pair `(e_{j-1}, S⃗_{j-1})` is a feasible transition into the state
`(e_j, e_{j+1}, S⃗_j, S⃗_{j+1})`, i.e. constraints (8)–(14), pp. 18–19. Constraint (11),
`e_{j-1} ≤ min{|S⁺_{j-1}|, e_j − |S⁻_j \ S⁺_{j-1}|}`, is written in integer (additive) form. -/
def FeasibleTransition (I : Instance n) (ε : ℝ) (kmid : ℕ) (s : DPSeq n) (j : ℕ) : Prop :=
  -- (8)
  (s.sm (j - 1) ⊆ s.sp (j - 1) ∧ s.sp (j - 1) ⊆ s.sp j) ∧
  -- (9)
  rhoSet I (s.sp (j - 1) \ s.sm (j - 1)) ≤ 4 * ε ^ 2 * rhoSet I (s.sm (j - 1)) ∧
  -- (10)
  wt I (s.sp (j - 1) \ s.sm (j - 1)) ≤ 4 * ε ^ 2 * wt I (s.sm (j - 1)) ∧
  -- (11)
  (s.ev (j - 1) ≤ (s.sp (j - 1)).card ∧ s.ev (j - 1) + (s.sm j \ s.sp (j - 1)).card ≤ s.ev j) ∧
  -- (12)
  (s.ev j ≤ kmid → (1 + ε / 2) * alpha I s (j - 1) ≤ alpha I s j) ∧
  -- (13)
  (s.ev j ≥ s.ev (j - 1) → s.ev (j - 1) ≥ kmid →
    alpha I s (j + 1) ≤ min ((1 - ε / 2) * alpha I s (j - 1)) ((1 + ε / 2) * alpha I s j)) ∧
  -- (14), as printed on p. 19
  (s.ev j ≥ kmid → kmid ≥ s.ev (j - 1) → (1 - 3 * ε / 2) * alpha I s (j - 1) ≤ alpha I s j)

/-- A feasible sequence of dynamic-programming actions (§4.2–§4.3, pp. 17–19): `T ≥ 1`, events in
`[n]`, the boundary case `e_1 = 1`, `S⁻_1 = S⁺_1 = {i₁}` (p. 17), the root `e_T = n`,
`S⃗_T = ([n], [n])` (p. 18), and every transition `j ∈ [2, T]` satisfies (8)–(14). -/
def IsFeasible (I : Instance n) (ε : ℝ) (kmid : ℕ) (s : DPSeq n) : Prop :=
  1 ≤ s.T ∧
  (∀ j, 1 ≤ j → j ≤ s.T → 1 ≤ s.e j ∧ s.e j ≤ n) ∧
  (s.e 1 = 1 ∧ ∃ i₁ : Fin n, s.Sm 1 = {i₁} ∧ s.Sp 1 = {i₁}) ∧
  (s.e s.T = n ∧ s.Sm s.T = univ ∧ s.Sp s.T = univ) ∧
  (∀ j, 2 ≤ j → j ≤ s.T → FeasibleTransition I ε kmid s j)

/-- `j_mid = max{j ∈ [T] : e_j ≤ k_mid}` (§4.4, p. 19); `0` if no such `j`. -/
def jmid (s : DPSeq n) (kmid : ℕ) : ℕ :=
  Nat.findGreatest (fun j => 1 ≤ j ∧ s.e j ≤ kmid) s.T

/-- `Δ_j` given `prev = Δ_1 ∪ ⋯ ∪ Δ_{j-1}` (§4.4 Step 1, p. 19):
`Δ_j = S⁻_j \ (S⁺_{j-1} ∪ prev)` for `j ≤ j_mid` (with `S⁺_0 = ∅`), and
`Δ_j = S⁺_j \ prev` for `j > j_mid`. -/
def deltaStep (s : DPSeq n) (kmid : ℕ) (j : ℕ) (prev : Finset (Fin n)) : Finset (Fin n) :=
  if j ≤ jmid s kmid then s.sm j \ (s.sp (j - 1) ∪ prev) else s.sp j \ prev

/-- `U_j = Δ_1 ∪ ⋯ ∪ Δ_j`, with `U_0 = ∅`. -/
def U (s : DPSeq n) (kmid : ℕ) : ℕ → Finset (Fin n)
  | 0 => ∅
  | j + 1 => U s kmid j ∪ deltaStep s kmid (j + 1) (U s kmid j)

/-- `Δ_j` for `j ≥ 1`. -/
def Delta (s : DPSeq n) (kmid : ℕ) (j : ℕ) : Finset (Fin n) :=
  deltaStep s kmid j (U s kmid (j - 1))

/-- `ẽ_j = |Δ_1 ∪ ⋯ ∪ Δ_j|`, with `ẽ_0 = 0` (§4.4 Step 2, p. 19). -/
def etil (s : DPSeq n) (kmid : ℕ) (j : ℕ) : ℕ := (U s kmid j).card

/-- `Ã` is an assignment rounded from `s` (§4.4 Step 2, p. 19): for every `j ∈ [1, T]` the items in
the first `ẽ_j` positions are exactly `Δ_1 ∪ ⋯ ∪ Δ_j` (so `Δ_j` fills the 1-based positions
`ẽ_{j-1}+1, …, ẽ_j`), and within that block prices are non-increasing (ties in any order). In 0-based
positions `p < q` of the block `[ẽ_{j-1}, ẽ_j)`, `r_{Ã(q)} ≤ r_{Ã(p)}`. -/
def IsRounded (I : Instance n) (s : DPSeq n) (kmid : ℕ) (A : Fin n ≃ Fin n) : Prop :=
  ∀ j, 1 ≤ j → j ≤ s.T →
    pre A (etil s kmid j) = U s kmid j ∧
    ∀ p q : Fin n, etil s kmid (j - 1) ≤ p.val → p.val < q.val → q.val < etil s kmid j →
      I.r (A q) ≤ I.r (A p)

/-- The intervals of positions in the proof of Lemma 5.4 (p. 22):
`Ĩ_j = [ẽ_j, ẽ_{j+1} − 1] ∩ [1, k_mid]` if `j ≤ j_mid`, and
`Ĩ_j = [ẽ_{j-1} + 1, ẽ_j] ∩ [k_mid + 1, n]` if `j ≥ j_mid + 1`. -/
def Itil (s : DPSeq n) (kmid : ℕ) (j : ℕ) : Finset ℕ :=
  if j ≤ jmid s kmid then
    (Ico (etil s kmid j) (etil s kmid (j + 1))).filter (fun k => 1 ≤ k ∧ k ≤ kmid)
  else
    (Ioc (etil s kmid (j - 1)) (etil s kmid j)).filter (fun k => kmid + 1 ≤ k ∧ k ≤ n)

end DisplayMNL.Rounding


