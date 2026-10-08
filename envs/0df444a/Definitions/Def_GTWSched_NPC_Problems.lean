-- Prove2me | Definitions.Def_GTWSched_NPC_Problems
-- name    : GTWSched_NPC_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:24:56.470525+00:00
-- url     : https://prove2.me/theorems/c8d19a43-53d9-4032-aba8-bb0f3b356e82
-- title:
--   §2.1, pp. 332–336 — total discrepancy and even-odd partition as languages, and the instances EO and D of the reductions
-- statement:
--   This file states the decision problems of §2.1 of Garey, Tarjan and Wilfong (1988) as languages, and the instances built in the proofs of LEMMA 1 and THEOREM 1. Instances are written as strings over the four-letter alphabet $\{0,1,-,\#\}$, every number in binary followed by a separator.
--
--   **Even-odd partition (p. 332).** An instance is a set $X=\{x_1,\dots,x_{2n}\}$ of positive integers, $n\ge 1$, with $x_i<x_{i+1}$ for $1\le i<2n$, written as the list $x_1,\dots,x_{2n}$. It is a yes-instance if $X$ splits into $X_1$ and $X_2$ with
--   $$\sum_{x\in X_1}x=\sum_{x\in X_2}x$$
--   such that for each $i$, $1\le i\le n$, $X_1$ (and hence $X_2$) contains exactly one of $x_{2i-1},x_{2i}$. The **even-odd partition language** is the set of codes of yes-instances.
--
--   **Total discrepancy (p. 332).** An instance consists of $N,k\in\mathbb Z^+$ and $M_i,l_i\in\mathbb Z^+$ ($1\le i\le N$), coded as the numbers $N,k,M_1,\dots,M_N,l_1,\dots,l_N$. It is a yes-instance if some schedule $S$ (real starting times $s_i\ge0$, nonoverlapping execution intervals) has $\mathrm{cost}(S)=\sum_{i=1}^N|m_i(S)-M_i|\le k$, where $m_i(S)=s_i+l_i/2$. The **total discrepancy language** is the set of codes of yes-instances.
--
--   **The instance EO of LEMMA 1 (p. 333).** From $Y=\{y_1,\dots,y_n\}$:
--   $$x_1=1,\qquad x_{2i}=x_{2i-1}+y_i\ (1\le i\le n),\qquad x_{2i+1}=x_{2i}+1\ (1\le i<n).$$
--
--   **The instance D of THEOREM 1 (p. 336).** From $X=\{x_1,\dots,x_{2n}\}$: $2n+2$ tasks $T_0,\dots,T_{2n+1}$ with $l_0=x_1-1$, $l_i=x_i$ for $1\le i\le 2n$, $l_{2n+1}=2$; preferred midtimes $M_j=M=\sum_{i=0}^{2n}l_i/2$ for $0\le j\le 2n$ and $M_{2n+1}=2M+l_{2n+1}/2$; threshold $k=\sum_{i=1}^n(l_{2i}+l_{2i-1})(n-i+\tfrac12)+l_0 n$.
--
--   **Formalization Note** The alphabet `BSym` and the binary list code `encNats` are the published `ProjSchedTW.Complexity.Encoding`; the class `NP` and `NPComplete` used with these languages are the published `CookPvsNP_defs`. Positions are 0-based: "exactly one of $x_{2i-1},x_{2i}$" is stated as "of two distinct positions with the same quotient by 2, exactly one is in $X_1$", which for a list of even length is the same condition. $X_1$ is a set of positions, not of values (the $x_i$ are distinct). Only codes of well-formed instances (positive entries; for EO, even positive length and strictly increasing) belong to the languages. The total discrepancy schedules have real starting times; the data $M_i,l_i,k$ are integers cast to $\mathbb R$. The instance D is real-valued (`dLen`, `dMid`, `dK`, indexed by `Fin (2n+2)` with $n=|X|/2$) because $M$ and $k$ can be half-integers; the paper's decision problem asks for integer data, so a polynomial-time reduction has to rescale (double every time), which preserves yes-instances. $l_0=x_1-1$ is computed in $\mathbb R$.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 332 §2.1 (Total discrepancy, Even-odd partition); p. 333 (proof of LEMMA 1, instance EO); p. 336 (proof of THEOREM 1, instance D)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules

namespace GTWSched.NPC

open CookPvsNP ProjSchedTW.Complexity

/-! # The decision problems of §2.1, their languages, and the instances built in the proofs of
LEMMA 1 and THEOREM 1 (Garey, Tarjan & Wilfong 1988, pp. 332–336)

Instances are written over the published four-letter alphabet `BSym`, every number in binary
(`encNats`). -/

noncomputable section

/-! ## Even-odd partition (p. 332) -/

/-- The paper's PARTITION source problem (p. 333): a nonempty list of positive integers has
an equal-sum partition. The imported `partitionLang` also accepts zero entries and the empty
list, so the source language is restricted here to the instances printed in the paper. -/
def positivePartitionLang : Lang BSym :=
  { w | ∃ y : List ℕ, y ≠ [] ∧ (∀ v ∈ y, 0 < v) ∧ PartitionYes y ∧ w = encNats y }

/-- An instance `X = {x₁, …, x₂ₙ}` of even-odd partition (p. 332), given as the list
`[x₁, …, x₂ₙ]`: its length is even and positive (`n ∈ Z⁺`), its entries are positive integers,
and it is strictly increasing (`xᵢ < xᵢ₊₁`). -/
def EOInstance (x : List ℕ) : Prop :=
  Even x.length ∧ 0 < x.length ∧ (∀ v ∈ x, 0 < v) ∧ x.Pairwise (· < ·)

/-- The question of even-odd partition (p. 332): there is a set `X₁` of positions (its complement
is `X₂`) containing exactly one of the positions of `x₂ᵢ₋₁, x₂ᵢ` for every `i` (0-based positions
`2i − 2, 2i − 1`, i.e. two distinct positions with the same quotient by `2`), with
`∑_{X₁} x = ∑_{X₂} x`. -/
def EOYes (x : List ℕ) : Prop :=
  ∃ X₁ : Finset (Fin x.length),
    (∀ p q : Fin x.length, p ≠ q → p.val / 2 = q.val / 2 → (p ∈ X₁ ↔ q ∉ X₁)) ∧
    ∑ p ∈ X₁, x.get p = ∑ p ∈ X₁ᶜ, x.get p

/-- The even-odd partition language: binary codes `x₁ x₂ … x₂ₙ` of the yes-instances. -/
def evenOddLang : Lang BSym :=
  { w | ∃ x : List ℕ, EOInstance x ∧ EOYes x ∧ w = encNats x }

/-! ## Total discrepancy (p. 332) -/

/-- The binary code of a total discrepancy instance: the numbers `N, k, M₁, …, M_N, l₁, …, l_N`.
The first number `N` fixes how many follow, so the code determines the instance. -/
def tdCode (N k : ℕ) (M l : Fin N → ℕ) : List BSym :=
  encNats (N :: k :: (List.ofFn M ++ List.ofFn l))

/-- The total discrepancy language (p. 332): codes of the instances `N, k ∈ Z⁺`, `Mᵢ, lᵢ ∈ Z⁺`
(`1 ≤ i ≤ N`) for which some schedule `S` (real starting times) has
`cost(S) = ∑ᵢ |mᵢ(S) − Mᵢ| ≤ k`. -/
def tdLang : Lang BSym :=
  { w | ∃ (N k : ℕ) (M l : Fin N → ℕ), 0 < N ∧ 0 < k ∧ (∀ i, 0 < M i) ∧ (∀ i, 0 < l i) ∧
      TDYesReal (fun i => (l i : ℝ)) (fun i => (M i : ℝ)) (k : ℝ) ∧ w = tdCode N k M l }

/-! ## The instance EO of the proof of LEMMA 1 (p. 333) -/

/-- `eoAux a [yᵢ, yᵢ₊₁, …]` lists `x₂ᵢ₋₁ = a, x₂ᵢ = x₂ᵢ₋₁ + yᵢ`, then continues with
`x₂ᵢ₊₁ = x₂ᵢ + 1`. -/
def eoAux : ℕ → List ℕ → List ℕ
  | _, [] => []
  | a, y :: ys => a :: (a + y) :: eoAux (a + y + 1) ys

/-- The instance `X` of even-odd partition built from a partition instance `Y = [y₁, …, yₙ]`
(p. 333): `x₁ = 1`, `x₂ᵢ = x₂ᵢ₋₁ + yᵢ` (`1 ≤ i ≤ n`), `x₂ᵢ₊₁ = x₂ᵢ + 1` (`1 ≤ i < n`). -/
def eoOfPartition (y : List ℕ) : List ℕ := eoAux 1 y

/-! ## The instance D of the proof of THEOREM 1 (p. 336) -/

/-- The lengths of the `2n + 2` tasks `T₀, …, T₂ₙ₊₁` of the instance D built from an even-odd
instance `x = [x₁, …, x₂ₙ]` (`n = |x|/2`; position `i` of `Fin (2n+2)` is `Tᵢ`):
`l₀ = x₁ − 1`, `lᵢ = xᵢ` for `1 ≤ i ≤ 2n`, `l₂ₙ₊₁ = 2`. -/
def dLen (x : List ℕ) (i : Fin (2 * (x.length / 2) + 2)) : ℝ :=
  if i.val = 0 then (x.getD 0 0 : ℝ) - 1
  else if i.val ≤ 2 * (x.length / 2) then (x.getD (i.val - 1) 0 : ℝ)
  else 2

/-- `M = ∑ᵢ₌₀²ⁿ lᵢ/2`, the common preferred midtime of `T₀, …, T₂ₙ` in D (p. 336). -/
def dM (x : List ℕ) : ℝ :=
  ∑ i : Fin (2 * (x.length / 2) + 1), dLen x i.castSucc / 2

/-- The preferred midtimes of D (p. 336): `Mⱼ = M` for `0 ≤ j ≤ 2n` and
`M₂ₙ₊₁ = 2M + l₂ₙ₊₁/2`. -/
def dMid (x : List ℕ) (j : Fin (2 * (x.length / 2) + 2)) : ℝ :=
  if j.val ≤ 2 * (x.length / 2) then dM x
  else 2 * dM x + dLen x (Fin.last _) / 2

/-- The threshold of D (p. 336): `k = ∑ᵢ₌₁ⁿ (l₂ᵢ + l₂ᵢ₋₁)(n − i + 1/2) + (l₀)n`, computed from the
lengths of `T₀, …, T₂ₙ`. -/
def dK (x : List ℕ) : ℝ :=
  kStar (fun i : Fin (2 * (x.length / 2) + 1) => dLen x i.castSucc)

end

end GTWSched.NPC


