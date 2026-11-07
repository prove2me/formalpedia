-- Prove2me | Definitions.Def_TIEMaximin_Reservation
-- name    : TIEMaximin_Reservation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:43:52.604863+00:00
-- url     : https://prove2.me/theorems/79b7f68d-c585-4176-ba63-7e69a1b692c5
-- title:
--   The reservation polytope (12) and the compensation suballocation $b$
-- statement:
--   The 0–1 points of the **reservation polytope** consist of $y_{ig}$ ("$g$ is reserved for $i$"), only on edges with $h_{ig}>0$, and $z_i$ ("$i$ receives her dummy item"), only for deficient $i$. With $D=\{i_1,\dots,i_{|D|}\}$ ordered by decreasing $1/k_i$, they satisfy
--
--   1. (A) $\sum_{g}y_{ig}+z_i=1$ for every agent $i$;
--   2. (B) $\sum_{i}y_{ig}\le1$ for every good $g$;
--   3. (C) $\sum_{g\in M\setminus P_t}\sum_i y_{ig}\le\lceil\rho(P_t)\rceil$ for $t\in\{0,\dots,m\}$;
--   4. (D) $\lfloor\sum_{j\le\ell}p_{i_j}\rfloor\le\sum_{j\le\ell}z_{i_j}\le\lceil\sum_{j\le\ell}p_{i_j}\rceil$ for $\ell\in\{1,\dots,|D|\}$.
--
--   Given such a point with reserved goods $R$, the fractional suballocation $b$ gives every reserved good fully to its agent and gives every dummy agent $i$ the fraction $1/k_i$ of each good in $L_i\setminus(Q_i\cup R)$.
--
--   **Formalization Note** The page leaves ties among equal $k_i$ unspecified, so the order is a parameter `ord` and `IsDOrder` admits every such order. Variables are Booleans and sums of them are counts. The real polytope itself is not needed: Lemma 4.1 speaks only of its 0–1 points and their mean.
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §4.1, eq. (12), p.19; §4.2, p.21

import Mathlib
import Definitions.Def_TIEMaximin_Comparison

namespace TIEMaximin

open Finset

/-- **The 0–1 points of the reservation polytope** (12), p.19: `y_ig` ("`g` is reserved for `i`") and
`z_i` ("`i` receives her dummy item"), as Booleans (arXiv:2609.35670, version of 2026-11-03, sha256
4e68de70…). -/
abbrev ResPt (n m : ℕ) : Type := (Fin n → Fin m → Bool) × (Fin n → Bool)

/-- **An order of `D` by decreasing `1/k_i`** (§4.1, p.19): a duplicate-free list of exactly the
deficient agents with `k` nondecreasing along it.

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §4.1, p.19: "Order D = {i_1, . . . , i_|D|}
by decreasing 1/k_i."

**Formalization Note.** The page leaves ties unspecified, so every such order is allowed. Statements
about the polytope quantify over all of them; the mechanism picks one existentially. -/
def IsDOrder {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (ord : List (Fin n)) : Prop :=
  ord.Nodup ∧ ord.toFinset = defSet α v ∧ ord.Pairwise fun i j => kDef α v i ≤ kDef α v j

/-- **A 0–1 point of the reservation polytope** (12), p.19.

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §4.1, (12), p.19: variables `y_ig` only on
edges with `h_ig > 0`, `z_i` only for `i ∈ D` (`z_i = 0` outside `D`), and
(A) `Σ_g y_ig + z_i = 1` for every `i`; (B) `Σ_i y_ig ≤ 1` for every `g`;
(C) `Σ_{g ∈ M∖P_t} Σ_i y_ig ≤ ⌈ρ(P_t)⌉` for `t ∈ {0, …, m}`;
(D) `⌊Σ_{j≤ℓ} p_{i_j}⌋ ≤ Σ_{j≤ℓ} z_{i_j} ≤ ⌈Σ_{j≤ℓ} p_{i_j}⌉` for `ℓ ∈ {1, …, |D|}`.

**Formalization Note.** The sums of Booleans are counts. In (D), `i_1, …, i_ℓ` is `ord.take ℓ`. -/
structure IsResPoint {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (ord : List (Fin n))
    (pt : ResPt n m) : Prop where
  /-- `y_ig` exists only for edges with `h_ig > 0`. -/
  edge : ∀ i g, pt.1 i g = true → 0 < hRet α v i g
  /-- `z_i` exists only for `i ∈ D`. -/
  dummy : ∀ i, pt.2 i = true → IsDeficient α v i
  /-- Constraint (A). -/
  consA : ∀ i, #{g | pt.1 i g = true} + (if pt.2 i = true then 1 else 0) = 1
  /-- Constraint (B). -/
  consB : ∀ g, #{i | pt.1 i g = true} ≤ 1
  /-- Constraint (C). -/
  consC : ∀ t, t ≤ m →
    ((∑ g ∈ univ \ prefixP v t, #{i | pt.1 i g = true} : ℕ) : ℤ) ≤ ⌈rho α v (prefixP v t)⌉
  /-- Constraint (D). -/
  consD : ∀ l, 1 ≤ l → l ≤ ord.length →
    ⌊((ord.take l).map (pDef α v)).sum⌋ ≤ (((ord.take l).countP fun i => pt.2 i) : ℤ) ∧
    (((ord.take l).countP fun i => pt.2 i) : ℤ) ≤ ⌈((ord.take l).map (pDef α v)).sum⌉

/-- **The set `R` of reserved goods** of an outcome of the first step (§3.3, p.18; Lemma 4.1, p.20 of
arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…). -/
def reserved {n m : ℕ} (pt : ResPt n m) : Finset (Fin m) :=
  {g | ∃ i, pt.1 i g = true}

/-- **The fractional suballocation `b`** of the second step (§4.2, p.21): a reserved good goes with
fraction `1` to the agent it is reserved for; a dummy agent `i` receives the fraction `1/k_i` of every
good in `L_i ∖ (Q_i ∪ R)`; every other entry is `0`.

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §4.2, p.21: "each agent i previously
receiving a dummy item receives a fraction 1/k_i of every good in L_i ∖ (Q_i ∪ R), and she receives
nothing in (Q_i ∪ R). Each agent receiving a high good in R continues to receive it (with fraction 1),
and she receives nothing else."

**Formalization Note.** `Q_i`, `k_i` are deterministic functions of `v`; `R` is the outcome. -/
noncomputable def bComp {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (pt : ResPt n m)
    (i : Fin n) (g : Fin m) : ℝ :=
  if pt.1 i g = true then 1
  else if pt.2 i = true ∧ g ∈ low α v i \ (compSet α v i ∪ reserved pt) then 1 / (kDef α v i : ℝ)
  else 0

end TIEMaximin


