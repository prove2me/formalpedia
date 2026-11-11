-- Prove2me | Definitions.Def_IIDMultiItem_TwoPoint_Auction
-- name    : IIDMultiItem_TwoPoint_Auction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:57:39.161242+00:00
-- url     : https://prove2.me/theorems/662b780e-7a2b-462e-a322-8abdaf85c8d7
-- title:
--   The exclusive-count auction with integer reserves (§3.2, (3.4)) and the one-buyer view H, D, C_ℓ, Θ(Q)
-- statement:
--   Fix the priority order $1<2<\dots<n$. At a profile $S$ the buyers are **ranked** by decreasing exclusive count, ties broken by priority: $\ell$ is ranked before $i$ iff $e_\ell>e_i$, or $e_\ell=e_i$ and $\ell<i$. Let $i^*$ be the first buyer. Given integer reserves $\theta_0,\theta_1,\dots$, the **auction** is:
--
--   * **Allocation.** Each item that some buyer reports high goes to the first buyer in the ranking who reports it high. If $e_{i^*}\ge\theta_{c+e_{i^*}}$, every item of $L$ goes to $i^*$; otherwise the items of $L$ are kept. $A_i$ is the set allocated to buyer $i$, and $x_{ij}=\mathbf 1\{j\in A_i\}$.
--   * **Payments.** For buyer $i$, with $d=c+e_i$,
--   $$\Theta_i=\max\big(\{\theta_d\}\cup\{e_\ell+\mathbf 1\{\ell<i\}:\ell\ne i\}\big),\tag{3.4}$$
--   and buyer $i$ pays $s_i=\sum_{j\in A_i}t_j(S_i)-\Delta\,[e_i-\Theta_i]_+$.
--
--   **One-buyer view.** Fix buyer $i$ and the others' reports. $H$ is the set of items some opponent reports high, $D=[m]\setminus H$, $d=|D|$; $C_\ell$ is the set of items that, among the buyers other than $i$, only $\ell$ reports high. When $i$ reports $Q\cup T$ with $Q\subseteq H$, $T\subseteq D$, opponent $\ell$ has exclusive count $|C_\ell\setminus Q|$, and the threshold (3.4) is
--   $$\Theta(Q)=\max\big(\{\theta_{d}\}\cup\{|C_\ell\setminus Q|+\mathbf 1\{\ell<i\}:\ell\ne i\}\big).$$
--
--   **Formalization Note.** Priority is the order of `Fin n` (smaller index first). The auction is defined for an arbitrary reserve sequence `θ : ℕ → ℤ` (the paper: Lemma 3.2 holds "for any integer reserves θ_0, …, θ_m"); the optimal auction uses `reserveStar a b p`. `RankedBefore S ℓ i`, `IsFirst S i` ($i=i^*$), `GetsLow θ S i` ($i=i^*$ and $e_{i^*}\ge\theta_{c+e_{i^*}}$), `unclaimed S i` (items no buyer ranked before $i$ reports high), `alloc θ S i` $=A_i$, `Theta θ S i` $=\Theta_i$, `payment a b θ S i` $=s_i$ and `auction a b θ` the mechanism. For the one-buyer view the others' reports are the coordinates $\ell\ne i$ of `S`: `oppHigh S i` $=H$, `oppLow S i` $=D$, `onlyOpp S i ℓ` $=C_\ell$, `ThetaQ θ S i Q` $=\Theta(Q)$.
-- source:
--   Liu, Liu, Wang, Optimal Multi-Item Auctions with I.I.D. Values, arXiv:2610.11051 (held version, PDF of 2026-11-03, sha256 983080a4…), p. 14 (PDF 16), §3.2, (3.4); p. 38 (PDF 40), §B.3

import Mathlib
import Definitions.Def_IIDMultiItem_TwoPoint_Model
import Definitions.Def_IIDMultiItem_TwoPoint_Counts

open scoped BigOperators

/-!
# The exclusive-count auction with integer reserves, and the one-buyer view

Liu, Liu, Wang, *Optimal Multi-Item Auctions with I.I.D. Values*, arXiv:2610.11051 (held version,
PDF of 2026-11-03, sha256 983080a4…), §3.2, p. 14, (3.4); §B.3, p. 38.

Priority order `1 < 2 < ⋯ < n` is the order of `Fin n` (smaller index = higher priority). The
buyers are ranked by decreasing exclusive count, ties broken by priority. The auction is defined
for an arbitrary sequence of integer reserves `θ : ℕ → ℤ` (the paper: "they hold for any integer
reserves θ_0, …, θ_m"); the reserves (3.2) are `reserveStar a b p`.
-/

namespace IIDMultiItem.TwoPoint

open Classical

variable {n m : ℕ}

/-- Buyer `ℓ` is ranked before buyer `i` at the profile `S`: a larger exclusive count, or an equal
one and a smaller index. -/
def RankedBefore (S : Fin n → Finset (Fin m)) (ℓ i : Fin n) : Prop :=
  exclCount S i < exclCount S ℓ ∨ (exclCount S ℓ = exclCount S i ∧ ℓ < i)

/-- Buyer `i` is the first buyer `i*` of the ranking. -/
def IsFirst (S : Fin n → Finset (Fin m)) (i : Fin n) : Prop :=
  ∀ ℓ, ¬ RankedBefore S ℓ i

/-- Buyer `i` receives the all-low items: `i = i*` and `e_{i*} ≥ θ_{c + e_{i*}}`. -/
def GetsLow (θ : ℕ → ℤ) (S : Fin n → Finset (Fin m)) (i : Fin n) : Prop :=
  IsFirst S i ∧ θ (numLow S + exclCount S i) ≤ (exclCount S i : ℤ)

/-- The items that no buyer ranked before buyer `i` reports high. -/
noncomputable def unclaimed (S : Fin n → Finset (Fin m)) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun j => ∀ ℓ, RankedBefore S ℓ i → j ∉ S ℓ)

/-- The set `A_i` allocated to buyer `i`: each item she reports high and that no buyer ranked
before her reports high (each item reported high goes to the first buyer in the ranking who
reports it high), and the items of `L` if she receives the all-low items. -/
noncomputable def alloc (θ : ℕ → ℤ) (S : Fin n → Finset (Fin m)) (i : Fin n) : Finset (Fin m) :=
  (S i ∩ unclaimed S i) ∪ (if GetsLow θ S i then allLow S else ∅)

/-- The threshold (3.4): with `d = c + e_i`,
`Θ_i = max({θ_d} ∪ {e_ℓ + 1{ℓ < i} : ℓ ≠ i})`. -/
noncomputable def Theta (θ : ℕ → ℤ) (S : Fin n → Finset (Fin m)) (i : Fin n) : ℤ :=
  (insert (θ (numLow S + exclCount S i))
    ((Finset.univ.erase i).image
      (fun ℓ => (exclCount S ℓ : ℤ) + if ℓ < i then 1 else 0))).max'
    (Finset.insert_nonempty _ _)

/-- The payment `s_i = ∑_{j ∈ A_i} t_j(S_i) − ∆ [e_i − Θ_i]_+`, `∆ = b − a`. -/
noncomputable def payment (a b : ℝ) (θ : ℕ → ℤ) (S : Fin n → Finset (Fin m)) (i : Fin n) : ℝ :=
  (∑ j ∈ alloc θ S i, setVal a b (S i) j) -
    (b - a) * (max ((exclCount S i : ℤ) - Theta θ S i) 0 : ℤ)

/-- The auction of §3.2 with reserves `θ`, as a mechanism on the two-point type space:
`x_ij(S) = 1{j ∈ A_i}`, `s_i(S) = payment`. -/
noncomputable def auction (a b : ℝ) (θ : ℕ → ℤ) : Mechanism (Finset (Fin m)) n m where
  x S i j := if j ∈ alloc θ S i then 1 else 0
  s S i := payment a b θ S i

/-! ## The view of one buyer (§3.2): the others' reports are the coordinates `ℓ ≠ i` of `S`. -/

/-- `H`: the items that some opponent of buyer `i` reports high. -/
def oppHigh (S : Fin n → Finset (Fin m)) (i : Fin n) : Finset (Fin m) :=
  (Finset.univ.erase i).biUnion S

/-- `D = [m] \ H`: the items that no opponent of buyer `i` reports high. -/
def oppLow (S : Fin n → Finset (Fin m)) (i : Fin n) : Finset (Fin m) :=
  Finset.univ \ oppHigh S i

/-- `C_ℓ`: the items that, among the buyers other than `i`, only `ℓ` reports high. -/
def onlyOpp (S : Fin n → Finset (Fin m)) (i ℓ : Fin n) : Finset (Fin m) :=
  S ℓ \ ((Finset.univ.erase i).erase ℓ).biUnion S

/-- `Θ(Q)`: the threshold (3.4) of buyer `i` when she reports `Q ∪ T` (`Q ⊆ H`, `T ⊆ D`), with
`d = |D|` and the opponents' exclusive counts `e_ℓ(Q) = |C_ℓ \ Q|`. -/
noncomputable def ThetaQ (θ : ℕ → ℤ) (S : Fin n → Finset (Fin m)) (i : Fin n)
    (Q : Finset (Fin m)) : ℤ :=
  (insert (θ (oppLow S i).card)
    ((Finset.univ.erase i).image
      (fun ℓ => ((onlyOpp S i ℓ \ Q).card : ℤ) + if ℓ < i then 1 else 0))).max'
    (Finset.insert_nonempty _ _)

end IIDMultiItem.TwoPoint


