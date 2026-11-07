-- Prove2me | Definitions.Def_OnlineBinCover_ConfigLP
-- name    : OnlineBinCover_ConfigLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:48:54.952207+00:00
-- url     : https://prove2.me/theorems/f05c7c4f-20b9-4522-b797-1a1c81a8ee90
-- title:
--   Classification, linear grouping, configurations and the configuration LP (3)
-- statement:
--   Fix a set $J$ of items (the instance, a sample or an epoch), ranks inside $J$, and $\varepsilon>0$ with $K=\lceil\varepsilon^{-2}\rceil$.
--
--   1. **Classes.** If $|J|\ge\lceil\mathrm{vol}(J)/\varepsilon\rceil+\lceil\mathrm{vol}(J)\rceil$ (the three-class case), the large items $L$ are the $\lceil\mathrm{vol}(J)/\varepsilon\rceil$ items of smallest rank, the medium items $M$ the next $\lceil\mathrm{vol}(J)\rceil$, and the small items $S$ the rest; otherwise $L=J$ and $M=S=\emptyset$.
--   2. **Linear grouping.** The large items in rank order are cut into $K$ consecutive groups $G_1,\dots,G_K$: the first $|L|-K\lfloor|L|/K\rfloor$ have $\lfloor|L|/K\rfloor+1$ items, the others $\lfloor|L|/K\rfloor$. Each large item is rounded down to the smallest size $r_j$ in its group.
--   3. **Configurations.** A configuration $C$ is a multiset of rounded large items, recorded by its counts $n(j,C)$, with $\mathrm{vol}(C)=\sum_j n(j,C)r_j<2$; its S-slot demand is $d(C)=(1-\mathrm{vol}(C))^+$.
--   4. **LP (3).**
--   $$\max\sum_C x_C\quad\text{s.t.}\quad\sum_C n(j,C)x_C\le|G_j|\ \ (j\in[K]),\qquad \sum_C d(C)x_C\le\mathrm{vol}(S),\qquad x\ge0.$$
--   5. **The guarantee of Lemma 2.2.** $x$ is a basic feasible solution with at most $K+1$ positive variables and $\sum_C\lfloor x_C\rfloor\ge(1-4\varepsilon)\mathrm{OPT}(J)-(K+5)$.
--
--   The milestones quantify over every $x$ with the guarantee of item 5, so no statement depends on which LP algorithm is used.
--
--   **Formalization Note** Groups are indexed from $0$ and may be empty when $|L|<K$; configurations use only nonempty groups, so there are finitely many. "Basic" is the standard notion for the LP in equality form: the columns of the positive variables and the unit columns of the positive slacks are linearly independent in $\mathbb R^{K+1}$.
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), §2.1, pp.7–8 (PDF pp.8–9), LP (3) and Lemma 2.2; §3, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_OnlineBinCover_Basic

namespace OnlineBinCover

/-!
# Classification, linear grouping, configurations and the configuration LP (3)

Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…), §2.1 pp.7–8 ("Classifying the items",
"Linear grouping", "Fractional small items and configurations", LP (3), Lemma 2.2) and §3 p.8
(the sample classification into `Lp`, `Mp`, `Sp` and the groups `G^p_1, …, G^p_K`).

All objects are defined for the items of a set `J` of item labels (the whole instance, a sample or
an epoch), with ranks taken inside `J` (decreasing size, ties by label).

**Formalization Note.**
* `K = ⌈ε^{-2}⌉` is `Kof ε`. Groups are indexed `0, …, K − 1` (the paper's `1, …, K`).
* *Classes.* If `|J| ≥ ⌈vol(J)/ε⌉ + ⌈vol(J)⌉` (`ThreeClass`), the large items are the
  `⌈vol(J)/ε⌉` items of smallest rank, the medium items the next `⌈vol(J)⌉`, the small items the
  rest; otherwise all items are large and there are no medium or small items.
* *Linear grouping.* The large items in rank order are cut into `K` consecutive groups, the first
  `|L| − K⌊|L|/K⌋` of size `⌊|L|/K⌋ + 1` and the others of size `⌊|L|/K⌋` (`groupOf`). Groups may be
  empty when `|L| < K`. Each item is rounded *down* to the smallest size in its group (`rsize`; the
  value `0` is never used for an empty group).
* *Configurations.* A configuration is a count vector `C : Fin K → ℕ` (`C j` rounded items of group
  `j`) using only nonempty groups and with rounded volume `vol(C) = ∑ C j · r_j < 2`. Its S-slot
  demand is `d(C) = max(0, 1 − vol(C))`. Since every nonempty group has positive rounded size, there
  are finitely many configurations.
* *LP (3).* A solution is a finitely supported `x : (Fin K → ℕ) →₀ ℝ` supported on configurations;
  feasibility is `x ≥ 0`, `∑_C C j · x_C ≤ |G_j|` for every `j` and `∑_C d(C) x_C ≤ vol(S)`.
  *Basic* is the standard notion for the LP in equality form with one slack per row: the constraint
  columns of the positive configuration variables together with the unit columns of the positive
  slacks are linearly independent in `ℝ^{K+1}` (rows indexed by `Option (Fin K)`, `none` the
  small-volume row).
* `LPSpec s J ε x` collects the guarantee of Lemma 2.2 for the LP built from `J` and `ε`: basic
  feasible, at most `K + 1` positive variables, and `∑_C ⌊x_C⌋ ≥ (1 − 4ε) OPT(J) − (K + 5)`. Later
  statements quantify over every `x` meeting it, so none depends on which LP algorithm is used.
-/

open Finset

/-- `K = ⌈ε^{-2}⌉` (§2.1, p.7). -/
noncomputable def Kof (ε : ℝ) : ℕ := ⌈(ε⁻¹) ^ 2⌉₊

/-- The three-class case `|J| ≥ ⌈vol(J)/ε⌉ + ⌈vol(J)⌉` (§2.1, p.7; §3, p.8). -/
def ThreeClass {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ) : Prop :=
  ⌈volOn s J / ε⌉₊ + ⌈volOn s J⌉₊ ≤ J.card

/-- `|L|`: `⌈vol(J)/ε⌉` in the three-class case, `|J|` otherwise. -/
noncomputable def nLarge {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ) : ℕ :=
  by classical exact if ThreeClass s J ε then ⌈volOn s J / ε⌉₊ else J.card

/-- `|M|`: `⌈vol(J)⌉` in the three-class case, `0` otherwise. -/
noncomputable def nMed {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ) : ℕ :=
  by classical exact if ThreeClass s J ε then ⌈volOn s J⌉₊ else 0

/-- The large items of `J`. -/
noncomputable def largeOf {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ) :
    Finset (Fin n) :=
  J.filter (fun i => rankIn s J i ≤ nLarge s J ε)

/-- The medium items of `J`. -/
noncomputable def medOf {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ) :
    Finset (Fin n) :=
  J.filter (fun i => nLarge s J ε < rankIn s J i ∧ rankIn s J i ≤ nLarge s J ε + nMed s J ε)

/-- The small items of `J`. -/
noncomputable def smallOf {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ) :
    Finset (Fin n) :=
  J.filter (fun i => nLarge s J ε + nMed s J ε < rankIn s J i)

/-- Linear grouping of `ℓ` ranked items into `K` groups: the group (`0`-based) of the item at
`0`-based position `r`; the first `ℓ % K` groups have `ℓ / K + 1` items, the others `ℓ / K`. -/
def groupOf (K ℓ r : ℕ) : ℕ :=
  if r < (ℓ % K) * (ℓ / K + 1) then r / (ℓ / K + 1)
  else ℓ % K + (r - (ℓ % K) * (ℓ / K + 1)) / (ℓ / K)

/-- The group (`0`-based) of a large item of `J`. -/
noncomputable def groupIdx {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ) (i : Fin n) :
    ℕ :=
  groupOf (Kof ε) (nLarge s J ε) (rankIn s J i - 1)

/-- The group `G_j` of large items of `J` (the paper's `G^p_{j+1}` for a sample). -/
noncomputable def Gp {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ) (j : Fin (Kof ε)) :
    Finset (Fin n) :=
  (largeOf s J ε).filter (fun i => groupIdx s J ε i = j.val)

/-- The rounded size of group `j`: the smallest size in the group (`0` for an empty group). -/
noncomputable def rsize {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ) (j : Fin (Kof ε)) :
    ℝ :=
  by classical exact if h : (Gp s J ε j).Nonempty then (Gp s J ε j).inf' h s else 0

/-- The rounded volume `vol(C) = ∑_j C j · r_j` of a configuration. -/
noncomputable def cvol {K : ℕ} (size : Fin K → ℝ) (C : Fin K → ℕ) : ℝ :=
  ∑ j, (C j : ℝ) * size j

/-- The S-slot demand `d(C) = (1 − vol(C))⁺`. -/
noncomputable def demand {K : ℕ} (size : Fin K → ℝ) (C : Fin K → ℕ) : ℝ :=
  max 0 (1 - cvol size C)

/-- `C` is a configuration: it uses only nonempty groups and `vol(C) < 2`. -/
def IsConfig {K : ℕ} (cnt : Fin K → ℕ) (size : Fin K → ℝ) (C : Fin K → ℕ) : Prop :=
  (∀ j, cnt j = 0 → C j = 0) ∧ cvol size C < 2

/-- Feasibility for LP (3) with group sizes `cnt`, rounded sizes `size` and small volume `volS`. -/
def LPFeasible {K : ℕ} (cnt : Fin K → ℕ) (size : Fin K → ℝ) (volS : ℝ)
    (x : (Fin K → ℕ) →₀ ℝ) : Prop :=
  (∀ C ∈ x.support, IsConfig cnt size C) ∧ (∀ C, 0 ≤ x C) ∧
    (∀ j, ∑ C ∈ x.support, (C j : ℝ) * x C ≤ (cnt j : ℝ)) ∧
    ∑ C ∈ x.support, demand size C * x C ≤ volS

/-- The constraint column of configuration `C` in `ℝ^{K+1}`. -/
noncomputable def lpCol {K : ℕ} (size : Fin K → ℝ) (C : Fin K → ℕ) : Option (Fin K) → ℝ
  | none => demand size C
  | some j => (C j : ℝ)

/-- The slack of each row of LP (3) at `x`. -/
noncomputable def lpSlack {K : ℕ} (cnt : Fin K → ℕ) (size : Fin K → ℝ) (volS : ℝ)
    (x : (Fin K → ℕ) →₀ ℝ) : Option (Fin K) → ℝ
  | none => volS - ∑ C ∈ x.support, demand size C * x C
  | some j => (cnt j : ℝ) - ∑ C ∈ x.support, (C j : ℝ) * x C

/-- `x` is basic: the columns of its positive variables and the unit columns of its positive
slacks are linearly independent. -/
def LPBasic {K : ℕ} (cnt : Fin K → ℕ) (size : Fin K → ℝ) (volS : ℝ)
    (x : (Fin K → ℕ) →₀ ℝ) : Prop :=
  LinearIndependent ℝ (Sum.elim (fun C : x.support => lpCol size C.1)
    (fun k : {k : Option (Fin K) // 0 < lpSlack cnt size volS x k} =>
      (Pi.single k.1 (1 : ℝ) : Option (Fin K) → ℝ)))

/-- The group sizes `|G_j|` of `J`. -/
noncomputable def lpCnt {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ) :
    Fin (Kof ε) → ℕ :=
  fun j => (Gp s J ε j).card

/-- The small-item volume `vol(S)` of `J`. -/
noncomputable def lpVolS {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ) : ℝ :=
  volOn s (smallOf s J ε)

/-- The guarantee of Lemma 2.2 for the LP (3) built from `J` and `ε`. -/
def LPSpec {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ)
    (x : (Fin (Kof ε) → ℕ) →₀ ℝ) : Prop :=
  LPFeasible (lpCnt s J ε) (rsize s J ε) (lpVolS s J ε) x ∧
    LPBasic (lpCnt s J ε) (rsize s J ε) (lpVolS s J ε) x ∧
    x.support.card ≤ Kof ε + 1 ∧
    (1 - 4 * ε) * (OPTon s J : ℝ) - ((Kof ε : ℝ) + 5) ≤ ∑ C ∈ x.support, (⌊x C⌋₊ : ℝ)

end OnlineBinCover


