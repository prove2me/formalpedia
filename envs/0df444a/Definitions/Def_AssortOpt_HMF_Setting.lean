-- Prove2me | Definitions.Def_AssortOpt_HMF_Setting
-- name    : AssortOpt_HMF_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:38.930558+00:00
-- url     : https://prove2.me/theorems/b2902a49-1686-450f-8018-f86c21096cd0
-- title:
--   §2, §4.1–4.2, pp. 8–20 — list distributions, assortments, IC mechanisms, set functions, monotone stopping policies, history-monotone futures, S-adjusted prices, tiers
-- statement:
--   The model of Will Ma, *When Is Assortment Optimization Optimal?* (§2 and §4), and every object its main theorem is about.
--
--   1. **List distribution** (p. 8). A seller has items $N = \{1, \dots, n\}$ with prices $r_j \ge 0$. A buyer's private type is a **list** $\ell$, a strictly ordered subset of $N$ (most preferred first; the empty list is allowed). Types are drawn from a finite support $\mathcal L$ with probabilities $p(\ell) > 0$ and $\sum_{\ell \in \mathcal L} p(\ell) = 1$. For a list $\ell$, $\ell_k$ is its $k$'th item and $\ell_{1:k}$ its first $k$ items; set operations on a list refer to its set of items.
--
--   2. **Assortments** (Definition 2, p. 8). Offering $S \subseteq N$, the buyer buys $j \in S$ iff $j$ is the earliest item of $S$ on their list; $\Pr[j \succeq S_0]$ is the probability of this event and
--   $$\mathsf{REV}[S] = \sum_{j \in S} r_j \Pr[j \succeq S_0]. \qquad (2)$$
--
--   3. **IC mechanisms** (Definition 3, p. 9). A mechanism gives, for each $\ell \in \mathcal L$ and $j \in \ell$, a probability $x_j(\ell)$ of assigning $j$ on report $\ell$. It is **IC** if
--   $$\sum_{j \in \ell_{1:k}} x_j(\ell) \ge \sum_{j \in \ell_{1:k} \cap \ell'} x_j(\ell') \ \ \forall \ell \in \mathcal L, k \le |\ell|, \ell' \in \mathcal L, \qquad \sum_{j \in \ell} x_j(\ell) \le 1, \qquad x_j(\ell) \ge 0,$$
--   constraints (3)–(5). Its revenue is $\mathsf{REV}[x] = \sum_{\ell \in \mathcal L} p(\ell) \sum_{j \in \ell} r_j x_j(\ell)$. The mechanism (6) of an assortment $S$ sets $x_j(\ell) = 1$ if $j$ is the first item of $S$ on $\ell$ and $0$ otherwise.
--
--   4. **Increasing set functions** (Definition 4, p. 11). $f : 2^N \to [0,1]$ with $f(S) \le f(S')$ for $S \subseteq S'$, and
--   $$\mathsf{REV}[f] = \sum_{\ell \in \mathcal L} p(\ell) \sum_{k=1}^{|\ell|} r_{\ell_k} \big(f(\ell_{1:k}) - f(\ell_{1:k-1})\big).$$
--
--   5. **Prefixes** (Definition 5, p. 12). A prefix $\rho$ is an ordered subset of $N$; $\Pr[\rho] = \sum_{\ell \in \mathcal L : \ell_{1:|\rho|} = \rho} p(\ell)$, and $\rho$ is **realizable** if $\Pr[\rho] > 0$. For nonempty $\rho$, $\rho_{\mathrm{end}}$ is its last item and $\rho_{\mathrm{pre}}$ the items before it. $\Pr[j \succeq S_0 \mid \rho]$ is the probability that $j$ is the first item of $S$ on the random list, conditional on the list starting with $\rho$.
--
--   6. **Monotone stopping policies** (Definition 8, p. 13). Boolean functions $\phi_j : 2^{N \setminus \{j\}} \to \{0,1\}$, each increasing in the history, with
--   $$\mathsf{REV}[\phi] = \sum_{\rho} r_{\rho_{\mathrm{end}}} \Pr[\rho] \Big(\phi_{\rho_{\mathrm{end}}}(\rho_{\mathrm{pre}}) \prod_{k=1}^{|\rho|-1} \big(1 - \phi_{\rho_k}(\rho_{1:k-1})\big)\Big), \qquad (10)$$
--   the sum over nonempty prefixes. An assortment $S$ is the policy with $\phi_j \equiv 1$ for $j \in S$ and $\phi_j \equiv 0$ otherwise.
--
--   7. **Domination and history-monotone futures** (Definitions 10–11, p. 17). For realizable $\rho, \rho'$, the future from $\rho$ **dominates** the future from $\rho'$ if $\Pr[j \succeq S_0 \mid \rho] \ge \Pr[j \succeq S_0 \mid \rho']$ for all $S \subseteq N \setminus (\rho \cup \rho')$ and $j \in S$ (12). The distribution has **history-monotone futures** if for all realizable $\rho, \rho'$ with $\rho_{\mathrm{end}} = \rho'_{\mathrm{end}}$ and $\rho_{\mathrm{pre}} \not\subseteq \rho'_{\mathrm{pre}}$, the future from $\rho$ dominates the future from $\rho'$.
--
--   8. **S-adjusted price** (Definition 12, p. 19). For realizable $\rho$ disjoint from $S$,
--   $$r^S(\rho) = r_{\rho_{\mathrm{end}}} - \sum_{j' \in S} r_{j'} \Pr[j' \succeq S_0 \mid \rho]. \qquad (13)$$
--
--   9. **Tier partitions** (Lemma 2, p. 20). For $S$ and $j \notin S$, a partition of the realizable prefixes $\rho$ with $\rho_{\mathrm{end}} = j$, $\rho \cap S = \emptyset$ into nonempty tiers $\mathcal T(1), \dots, \mathcal T(T)$ such that (1) for $t > t'$, $\rho \in \mathcal T(t)$, $\rho' \in \mathcal T(t')$: $\rho \supsetneq \rho'$ as sets and $\Pr[j' \succeq S_0 \mid \rho] \ge \Pr[j' \succeq S_0 \mid \rho']$ for all $j' \in S$; (2) within each tier, either (a) distinct prefixes are $\subseteq$-incomparable as sets with equal conditional choice probabilities for every $j' \in S$, or (b) all prefixes are equal as sets.
--
--   These objects carry the paper's chain of relaxations $\mathsf{OPT}^S \le \mathsf{OPT}^x \le \mathsf{OPT}^f \le \mathsf{OPT}^\phi$ and the sufficient condition under which the chain collapses.
--
--   **Formalization Note** Items are `Fin n`, 0-based (Lean item `i` is the paper's item `i + 1`). Lists are `List (Fin n)`; the support is a `Finset` of `Nodup` lists. `ℓ_{1:|ρ|} = ρ` is `ρ <+: ℓ`, `ℓ_{1:k}` is `ℓ.take k`, $\rho_{\mathrm{end}}$ is `getLast?`, $\rho_{\mathrm{pre}}$ is `dropLast`. "$j$ first in $S$ on $\ell$" is `ℓ.find? (· ∈ S) = some j`. A mechanism is a function on all lists and items, but only the values $x_j(\ell)$ with $\ell \in \mathcal L$, $j \in \ell$ are read. The realizable nonempty prefixes are `prefixes D`, the nonempty prefixes of support lists (equal to the realizable ones because $p > 0$ on the support); domination, history-monotone futures, $r^S$ and tiers only ever quantify over them, so the conditional probability (a quotient by $\Pr[\rho]$) is never taken at $\Pr[\rho] = 0$. Policies are `Bool`-valued on all pairs $(j, H)$; values at $H \ni j$ are never read. Tiers are a labelling `τ` onto $\{1, \dots, T\}$ with every tier nonempty.
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, pp. 8–20, Definitions 1–5, 8, 10–12, (2)–(6), (10), (12), (13), Lemma 2 (tier properties 1–2)

import Mathlib

namespace AssortOpt.HMF
open Finset

/-- A list distribution (Ma, arXiv:2105.10433v5, §2, p. 8): a finite support `supp` of lists, each a
strictly ordered subset of the items `Fin n` (items are 0-based: Lean item `i` is the paper's item
`i + 1`), with positive probabilities `p ℓ` summing to one. Values of `p` off the support are never
read. -/
structure ListDist (n : ℕ) where
  supp : Finset (List (Fin n))
  p : List (Fin n) → ℝ
  nodup : ∀ ℓ ∈ supp, ℓ.Nodup
  pos : ∀ ℓ ∈ supp, 0 < p ℓ
  sum_one : ∑ ℓ ∈ supp, p ℓ = 1

variable {n : ℕ}

/-- "`j ⪰_S 0` on `ℓ`" (Definition 2, p. 8): `j` is the earliest item of the list `ℓ` lying in `S`.
In particular `j ∈ S` and `j ∈ ℓ`. -/
def Chooses (S : Finset (Fin n)) (ℓ : List (Fin n)) (j : Fin n) : Prop :=
  ℓ.find? (fun i => decide (i ∈ S)) = some j

instance (S : Finset (Fin n)) (ℓ : List (Fin n)) (j : Fin n) : Decidable (Chooses S ℓ j) :=
  inferInstanceAs (Decidable (_ = _))

/-- `Pr[j ⪰_S 0]` (Definition 2, p. 8): the probability that `j` is the first item of `S` on the
random list. -/
noncomputable def choiceProb (D : ListDist n) (S : Finset (Fin n)) (j : Fin n) : ℝ :=
  ∑ ℓ ∈ D.supp with Chooses S ℓ j, D.p ℓ

/-- `REV[S] = ∑_{j ∈ S} r_j Pr[j ⪰_S 0]`, display (2), p. 8. -/
noncomputable def revAssort (D : ListDist n) (r : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, r j * choiceProb D S j

/-- IC mechanisms (Definition 3, p. 9): `x ℓ j` is the probability of assigning item `j` on report
`ℓ`; `x` is IC if it satisfies (3), (4) and (5). Only the values `x ℓ j` with `ℓ ∈ supp`, `j ∈ ℓ` are
read. In (3), `ℓ.take k` is `ℓ_{1:k}` for every `k ≤ |ℓ|` (the case `k = 0` is the trivial `0 ≤ 0`). -/
def IsIC (D : ListDist n) (x : List (Fin n) → Fin n → ℝ) : Prop :=
  (∀ ℓ ∈ D.supp, ∀ k ≤ ℓ.length, ∀ ℓ' ∈ D.supp,
      ∑ j ∈ (ℓ.take k).toFinset ∩ ℓ'.toFinset, x ℓ' j ≤ ∑ j ∈ (ℓ.take k).toFinset, x ℓ j) ∧
  (∀ ℓ ∈ D.supp, ∑ j ∈ ℓ.toFinset, x ℓ j ≤ 1) ∧
  (∀ ℓ ∈ D.supp, ∀ j ∈ ℓ, 0 ≤ x ℓ j)

/-- `REV[x] = ∑_{ℓ ∈ ℒ} p(ℓ) ∑_{j ∈ ℓ} r_j x_j(ℓ)`, the objective of the LP of Definition 3, p. 9. -/
noncomputable def revMech (D : ListDist n) (r : Fin n → ℝ) (x : List (Fin n) → Fin n → ℝ) : ℝ :=
  ∑ ℓ ∈ D.supp, D.p ℓ * ∑ j ∈ ℓ.toFinset, r j * x ℓ j

/-- The mechanism (6) of Proposition 1, p. 9, induced by an assortment `S`: assign `j` with
probability one iff `j` is the first item of `S` on `ℓ`. -/
noncomputable def assortMech (S : Finset (Fin n)) : List (Fin n) → Fin n → ℝ :=
  fun ℓ j => if Chooses S ℓ j then 1 else 0

/-- An increasing set function `f : 2^N → [0, 1]` (Definition 4, p. 11). -/
def IsIncreasingSetFn (f : Finset (Fin n) → ℝ) : Prop :=
  Monotone f ∧ ∀ S, f S ∈ Set.Icc (0 : ℝ) 1

/-- `REV[f] = ∑_{ℓ ∈ ℒ} p(ℓ) ∑_{k=1}^{|ℓ|} r_{ℓ_k} (f(ℓ_{1:k}) − f(ℓ_{1:k−1}))` (Definition 4,
p. 11), written 0-based: the paper's position `k + 1` is `ℓ.get k`, `ℓ_{1:k+1}` is `ℓ.take (k+1)`. -/
noncomputable def revSetFn (D : ListDist n) (r : Fin n → ℝ) (f : Finset (Fin n) → ℝ) : ℝ :=
  ∑ ℓ ∈ D.supp, D.p ℓ * ∑ k : Fin ℓ.length,
    r (ℓ.get k) * (f (ℓ.take (k + 1)).toFinset - f (ℓ.take k).toFinset)

/-- `Pr[ρ] = ∑_{ℓ ∈ ℒ : ℓ_{1:|ρ|} = ρ} p(ℓ)` (Definition 5, p. 12); `ρ <+: ℓ` is `ℓ_{1:|ρ|} = ρ`. -/
noncomputable def prefProb (D : ListDist n) (ρ : List (Fin n)) : ℝ :=
  ∑ ℓ ∈ D.supp with ρ <+: ℓ, D.p ℓ

/-- The nonempty prefixes of lists in the support. Since `p > 0` on the support, these are exactly
the nonempty realizable prefixes (`Pr[ρ] > 0`, Definition 5, p. 12). -/
def prefixes (D : ListDist n) : Finset (List (Fin n)) :=
  (D.supp.biUnion fun ℓ => ℓ.inits.toFinset).filter (· ≠ [])

/-- `Pr[j ⪰_S 0 | ρ]`: the probability that `j` is the first item of `S` on the random list,
conditional on the list starting with `ρ` (p. 15, Definitions 10 and 12). Every use has `ρ` realizable
and disjoint from `S`. -/
noncomputable def condChoiceProb (D : ListDist n) (S : Finset (Fin n)) (j : Fin n)
    (ρ : List (Fin n)) : ℝ :=
  (∑ ℓ ∈ D.supp with ρ <+: ℓ ∧ Chooses S ℓ j, D.p ℓ) / prefProb D ρ

/-- The price of the endpoint `ρ_end` of a nonempty prefix (`0` for the empty list, never used). -/
def endPrice (r : Fin n → ℝ) (ρ : List (Fin n)) : ℝ :=
  (ρ.getLast?.map r).getD 0

/-- A stopping policy: `φ j H ∈ {0, 1}` for each item `j` and history `H` (Definition 8, p. 13).
The values at `H ∋ j` are never read. -/
abbrev Policy (n : ℕ) := Fin n → Finset (Fin n) → Bool

/-- Monotone stopping policy (Definition 8, p. 13): each `φ_j` is increasing on `2^{N \ {j}}`. -/
def IsMonotonePolicy (φ : Policy n) : Prop :=
  ∀ j H H', j ∉ H' → H ⊆ H' → φ j H ≤ φ j H'

/-- A boolean read as `0` or `1`. -/
def ind (b : Bool) : ℝ := if b then 1 else 0

/-- The bracket of (10), p. 13, for a nonempty prefix `ρ`:
`φ_{ρ_end}(ρ_pre) ∏_{k=1}^{|ρ|−1} (1 − φ_{ρ_k}(ρ_{1:k−1}))`. 0-based: the paper's `ρ_{k+1}` is
`ρ.dropLast.get k` and its history `ρ_{1:k}` is `ρ.take k`. Equals `0` for the empty list. -/
def stopInd (φ : Policy n) (ρ : List (Fin n)) : ℝ :=
  match ρ.getLast? with
  | none => 0
  | some e => ind (φ e ρ.dropLast.toFinset) *
      ∏ k : Fin ρ.dropLast.length, (1 - ind (φ (ρ.dropLast.get k) (ρ.take k).toFinset))

/-- `REV[φ] = ∑_ρ r_{ρ_end} Pr[ρ] (φ_{ρ_end}(ρ_pre) ∏_{k=1}^{|ρ|−1} (1 − φ_{ρ_k}(ρ_{1:k−1})))`,
display (10), p. 13. The sum runs over nonempty realizable prefixes; unrealizable ones have
`Pr[ρ] = 0` and contribute nothing on the page. -/
noncomputable def revPolicy (D : ListDist n) (r : Fin n → ℝ) (φ : Policy n) : ℝ :=
  ∑ ρ ∈ prefixes D, endPrice r ρ * prefProb D ρ * stopInd φ ρ

/-- The stopping policy of an assortment (p. 13): `φ_j` is the all-1 function if `j ∈ S` and the
all-0 function otherwise. -/
def assortPolicy (S : Finset (Fin n)) : Policy n :=
  fun j _ => decide (j ∈ S)

/-- Domination of futures, (12) of Definition 10, p. 17: for all `S ⊆ N \ (ρ ∪ ρ')` and `j ∈ S`,
`Pr[j ⪰_S 0 | ρ] ≥ Pr[j ⪰_S 0 | ρ']`. -/
def Dominates (D : ListDist n) (ρ ρ' : List (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), Disjoint S (ρ.toFinset ∪ ρ'.toFinset) →
    ∀ j ∈ S, condChoiceProb D S j ρ' ≤ condChoiceProb D S j ρ

/-- History-monotone futures (Definition 11, p. 17): for all realizable prefixes `ρ, ρ'` with
`ρ_end = ρ'_end` and `ρ_pre ⊈ ρ'_pre` as sets, the future from `ρ` dominates the future from `ρ'`. -/
def HasHistoryMonotoneFutures (D : ListDist n) : Prop :=
  ∀ ρ ∈ prefixes D, ∀ ρ' ∈ prefixes D, ρ.getLast? = ρ'.getLast? →
    ¬ ρ.dropLast.toFinset ⊆ ρ'.dropLast.toFinset → Dominates D ρ ρ'

/-- The `S`-adjusted price `r^S(ρ) = r_{ρ_end} − ∑_{j' ∈ S} r_{j'} Pr[j' ⪰_S 0 | ρ]`, (13) of
Definition 12, p. 19. Used only for realizable `ρ` disjoint from `S`. -/
noncomputable def adjPrice (D : ListDist n) (r : Fin n → ℝ) (S : Finset (Fin n))
    (ρ : List (Fin n)) : ℝ :=
  endPrice r ρ - ∑ j' ∈ S, r j' * condChoiceProb D S j' ρ

/-- The realizable prefixes `ρ` with `ρ_end = j` and `ρ ∩ S = ∅` (Lemma 2, p. 20). -/
def tierDomain (D : ListDist n) (S : Finset (Fin n)) (j : Fin n) : Finset (List (Fin n)) :=
  (prefixes D).filter (fun ρ => ρ.getLast? = some j ∧ Disjoint ρ.toFinset S)

/-- `τ` partitions `tierDomain D S j` into the tiers `𝒯(1), …, 𝒯(T)` (`𝒯(t) = {ρ : τ ρ = t}`, all
nonempty) with properties 1 and 2 of Lemma 2, p. 20. -/
def IsTierPartition (D : ListDist n) (S : Finset (Fin n)) (j : Fin n) (T : ℕ)
    (τ : List (Fin n) → ℕ) : Prop :=
  (∀ ρ ∈ tierDomain D S j, τ ρ ∈ Finset.Icc 1 T) ∧
  (∀ t ∈ Finset.Icc 1 T, ∃ ρ ∈ tierDomain D S j, τ ρ = t) ∧
  (∀ ρ ∈ tierDomain D S j, ∀ ρ' ∈ tierDomain D S j, τ ρ' < τ ρ →
      ρ'.toFinset ⊂ ρ.toFinset ∧ ∀ j' ∈ S, condChoiceProb D S j' ρ' ≤ condChoiceProb D S j' ρ) ∧
  (∀ t ∈ Finset.Icc 1 T,
      (∀ ρ ∈ tierDomain D S j, ∀ ρ' ∈ tierDomain D S j, τ ρ = t → τ ρ' = t → ρ ≠ ρ' →
          ¬ ρ.toFinset ⊆ ρ'.toFinset ∧ ¬ ρ'.toFinset ⊆ ρ.toFinset ∧
          ∀ j' ∈ S, condChoiceProb D S j' ρ = condChoiceProb D S j' ρ') ∨
      (∀ ρ ∈ tierDomain D S j, ∀ ρ' ∈ tierDomain D S j, τ ρ = t → τ ρ' = t →
          ρ.toFinset = ρ'.toFinset))

end AssortOpt.HMF


