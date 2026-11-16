-- Prove2me | Definitions.Def_CompPermOracle_Supplement_sparsity
-- name    : CompPermOracle_Supplement_sparsity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:47:37.60844+00:00
-- url     : https://prove2.me/theorems/0ac362dc-db18-4c06-8810-4357e4639797
-- title:
--   Increasing database properties, witnessing lists and the two-sided sparsity $s_t$
-- statement:
--   A **database property** is a set $\mathcal B$ of partial permutations of $[N]$. It is **increasing** if $f\in\mathcal B$ and $f\subseteq g$ imply $g\in\mathcal B$, where $f\subseteq g$ means that every pair $(x,y)$ with $f(x)=y$ also has $g(x)=y$. A list of input-output pairs **witnesses** $\mathcal B$ if its set of pairs is exactly the graph of some $f\in\mathcal B$; repeated pairs impose no additional condition. The list **agrees** with a permutation $\varphi$ if $\varphi(x)=y$ for every listed pair.
--
--   For an increasing $\mathcal B$ with $\emptyset\notin\mathcal B$, the **two-sided sparsity** is
--   $$
--   s_t=\max_{\substack{|h|\le t\\ h\notin\mathcal B}}\max\Big\{\max_{x\notin\mathrm{dom}(h)}\big|\{y\notin\mathrm{im}(h):h[x\mapsto y]\in\mathcal B\}\big|,\ \max_{y\notin\mathrm{im}(h)}\big|\{x\notin\mathrm{dom}(h):h[x\mapsto y]\in\mathcal B\}\big|\Big\}.
--   $$
--   For an ideal cipher with finite key space $\mathcal K$, a keyed database is a family $h=(h_k)_{k\in\mathcal K}$ of partial permutations, ordered keywise; lists consist of triples $(k,x,y)$, a list witnesses a keyed property if its set of triples is exactly the graph of a keyed database in it, and the keyed sparsity takes an additional maximum over the queried key $k$, uses the total size $\sum_k|h_k|\le t$, and extends only $h_k$.
--
--   The sparsity counts, for a database that does not yet satisfy $\mathcal B$, how many answers to a single forward or inverse query can make it satisfy $\mathcal B$; it is the quantity that drives the explicit search bound (Theorem 5.3).
--
--   **Formalization Note** Partial permutations are the published `PartialPerm N` (Mathlib's `PEquiv`), $h[x\mapsto y]$ is the published `addPair`, and $\emptyset$ is `⊥`. Every maximum is a supremum in $\mathbb N$, so a maximum over an empty index set is $0$. "Consistent with a partial permutation belonging to $\mathcal B$" is read as equality of the list's pair set with the graph of a member of $\mathcal B$; this is the reading the proof of Lemma 5.1 uses ("a database containing a witnessing list belongs to $\mathcal B$"), and the weaker reading (some member of $\mathcal B$ contains every listed pair) would make Theorem 5.3 false.
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), §5.1, p.27 (database property, increasing, witnesses; Lemma 5.1, last sentence); §5.2, eq. (84), p.28 and p.29 (keyed sparsity)

import Mathlib
import Definitions.Def_CompPermOracle_PartialPerm

namespace CompPermOracle.Supplement

open CompPermOracle

/-- A database property `𝓑` (a set of partial permutations) is **increasing** if `f ∈ 𝓑` and
`f ⊆ g` imply `g ∈ 𝓑` (Carolan, Majenz, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…),
§5.1, p.27).

**Formalization Note.** `f ⊆ g` is inclusion of graphs: every pair `(x, y)` with `f(x) = y` has
`g(x) = y`. -/
def Increasing {N : ℕ} (B : Set (PartialPerm N)) : Prop :=
  ∀ f g : PartialPerm N, f ∈ B → (∀ x y, f x = some y → g x = some y) → g ∈ B

/-- A list of input-output pairs **witnesses** `𝓑` if it is consistent with a partial permutation
belonging to `𝓑`; repeated pairs impose no additional condition (arXiv:2609.28469, §5.1, p.27).

**Formalization Note.** "Consistent with a partial permutation `f ∈ 𝓑`" is read as: the set of
pairs of the list is exactly the graph of some `f ∈ 𝓑`. The proof of Lemma 5.1 (p.28) uses that "a
database containing a witnessing list belongs to `𝓑`", which is this reading together with
monotonicity; the weaker reading "some `f ∈ 𝓑` contains every listed pair" makes Theorem 5.3
false. -/
def Witnesses {N : ℕ} (B : Set (PartialPerm N)) (l : List (Fin N × Fin N)) : Prop :=
  ∃ f ∈ B, ∀ x y, f x = some y ↔ (x, y) ∈ l

/-- Every listed pair agrees with the permutation `φ`: `φ(x) = y` for each `(x, y)` in the list. -/
def Agrees {N : ℕ} (φ : Equiv.Perm (Fin N)) (l : List (Fin N × Fin N)) : Prop :=
  ∀ p ∈ l, φ p.1 = p.2

open Classical in
/-- The **two-sided sparsity** of a database property (arXiv:2609.28469, §5.2, eq. (84), p.28):
`s_t = max_{|h| ≤ t, h ∉ 𝓑} max{ max_{x ∉ dom(h)} |{y ∉ im(h) : h[x ↦ y] ∈ 𝓑}|,
max_{y ∉ im(h)} |{x ∉ dom(h) : h[x ↦ y] ∈ 𝓑}| }`.

**Formalization Note.** Each maximum is `Finset.sup` in `ℕ`, so a maximum over an empty index set
is `0`. `h[x ↦ y]` is `addPair h x y`, used only for `x ∉ dom(h)` and `y ∉ im(h)`. The source
defines `s_t` for increasing `𝓑` with `∅ ∉ 𝓑`; the definition is total, and the theorems carry those
hypotheses. -/
noncomputable def sparsity {N : ℕ} (B : Set (PartialPerm N)) (t : ℕ) : ℕ :=
  (Finset.univ.filter fun h : PartialPerm N => size h ≤ t ∧ h ∉ B).sup fun h =>
    max ((freeDom h).sup fun x => ((freeIm h).filter fun y => addPair h x y ∈ B).card)
      ((freeIm h).sup fun y => ((freeDom h).filter fun x => addPair h x y ∈ B).card)

/-- A keyed database property (a set of keyed databases `h = (h_k)_{k ∈ 𝒦}`) is **increasing** if
it is closed under keywise graph inclusion (arXiv:2609.28469, Lemma 5.1, last sentence, p.27). -/
def KIncreasing {N : ℕ} {K : Type} (B : Set (K → PartialPerm N)) : Prop :=
  ∀ f g : K → PartialPerm N, f ∈ B → (∀ k x y, f k x = some y → g k x = some y) → g ∈ B

/-- A list of triples `(k, x, y)` **witnesses** a keyed property `𝓑` if its set of triples is
exactly the graph of some keyed database in `𝓑` (arXiv:2609.28469, Lemma 5.1, p.27; same reading as
`Witnesses`). -/
def KWitnesses {N : ℕ} {K : Type} (B : Set (K → PartialPerm N)) (l : List (K × Fin N × Fin N)) :
    Prop :=
  ∃ h ∈ B, ∀ k x y, h k x = some y ↔ (k, x, y) ∈ l

/-- Every listed triple agrees with the ideal cipher `Φ`: `φ_k(x) = y` for each `(k, x, y)`. -/
def KAgrees {N : ℕ} {K : Type} (Φ : K → Equiv.Perm (Fin N)) (l : List (K × Fin N × Fin N)) :
    Prop :=
  ∀ p ∈ l, Φ p.1 p.2.1 = p.2.2

open Classical in
/-- The two-sided sparsity of a keyed property (arXiv:2609.28469, p.29: "For a keyed database, take
an additional maximum over the key being queried, and use total database size in the condition
`|h| ≤ t`").

**Formalization Note.** The outer maximum is over keyed databases `h` with `∑_k |h_k| ≤ t` and
`h ∉ 𝓑`, the next one over the queried key `k`, and the extension `h[x ↦ y]` under key `k` changes
only `h_k`. Maxima over empty sets are `0`. -/
noncomputable def keyedSparsity {N : ℕ} {K : Type} [Fintype K] [DecidableEq K]
    (B : Set (K → PartialPerm N)) (t : ℕ) : ℕ :=
  (Finset.univ.filter fun h : K → PartialPerm N => ∑ k, size (h k) ≤ t ∧ h ∉ B).sup fun h =>
    Finset.univ.sup fun k =>
      max ((freeDom (h k)).sup fun x =>
          ((freeIm (h k)).filter fun y => Function.update h k (addPair (h k) x y) ∈ B).card)
        ((freeIm (h k)).sup fun y =>
          ((freeDom (h k)).filter fun x => Function.update h k (addPair (h k) x y) ∈ B).card)

end CompPermOracle.Supplement


