-- Prove2me | Definitions.Def_VecKnapsackMitM_Main_Algorithm3
-- name    : VecKnapsackMitM_Main_Algorithm3
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:35:09.020546+00:00
-- url     : https://prove2.me/theorems/308868fb-6f76-4ac8-b2b9-98921331e021
-- title:
--   Algorithm 3 (dKnapsack-MitM) as a specification, with the guarantees of Lemma 4.2
-- statement:
--   Algorithm 3 (printed p. 19) as the set of outputs it can return. A virtual item is identified with the set it represents; the paper's list $L_{k+1}$ is `L k` for `k : Fin (n+1)`.
--
--   * `pAt I k` $=p(k+1)$ with the convention $p(n+1)=0$.
--   * `RepFamily I ε L` (Lemma 4.2, bullets 2–4): for every $k$, each $v\in L_{k+1}$ is a subset of $\{k+1,\dots,n\}$; $\emptyset\in L_{k+1}$; and every $S\subseteq\{k+1,\dots,n\}$ has some $v\in L_{k+1}$ with $\bar w(v)\le\bar w(S)$, $p(v)\ge(1-\varepsilon)p(S)-(d-1+\varepsilon/n)\,p(k+1)$ and $p(v)\ge\frac{1-\varepsilon}{d}p(S)-\frac{\varepsilon}{n}p(k+1)$.
--   * Line 2: `alg3q` $q=\lceil (d-1)/\varepsilon-d+\rho\rceil$, `alg3l1` $\ell_1=\lfloor (q+d-1)/2\rfloor$, `alg3l2` $\ell_2=\max\{q-\ell_1,1\}$; Line 4: `alg3delta` $\delta=\varepsilon^2\rho/(2(d-1))$.
--   * `nextIdx S₂`: the list index $\max(S_2)+1$ of Line 6.
--   * `ORSAnswer I ℓ₁ hi ans` (Lines 3, 7): the ORS stores every $S$ with $|S|\le\ell_1$ at `embed S` with profit $p(S)$; `none` is a correct answer iff no stored point is in the box `[rangeLo, hi]`, and `some S₁` iff $S_1$ is stored, in the box, and of maximum profit among stored sets in the box.
--   * `Alg3Returns J ε ρ L ans S` (Lines 5–9): candidates are triples $(S_1,S_2,v)$ with $1\le|S_2|\le\ell_2$, $v\in L_{\max(S_2)+1}$ and $S_1$ the answer to the query $\mathrm{range}_{\bar W}(S_2\cup v)$, of value $p(S_1)+p(S_2)+p(v)$; since `best` starts at $\emptyset$ (value $0$) and changes only on a strictly larger value, the returned set is $\emptyset$ if no candidate has positive value and otherwise $S_1\cup S_2\cup v$ for a candidate of maximum value (any, by the iteration order).
--   * `Alg3Output inst ε ρ S`: for some order $\sigma$ of non-increasing profit (Line 1, ties arbitrary), some lists $L$ with `RepFamily` for the sorted instance and error $\delta$ (Line 4), and correct answers to all queries, $S$ is $\sigma$'s image of a set returned by Lines 5–9.
--
--   The size bullet of Lemma 4.2 is not part of `RepFamily`: correctness does not use it, and Lemma 4.2 itself states it.
-- source:
--   Bringmann, Kulik, Węgrzycki (2026), Fine-Grained Complexity of Approximating Vector Knapsack: A Faster Algorithm and Equivalence with k-SUM in 2D, STOC 2027 submission, SHA-256 966f42f7…10ac98; Algorithm 3, printed p. 19 (PDF 20); Lemma 4.2, printed pp. 15–16 (PDF 16–17); Definition 4.3, printed p. 18 (PDF 19)

import Mathlib
import Definitions.Def_VecKnapsackMitM_Main_Instance
import Definitions.Def_VecKnapsackMitM_Main_Geometry

namespace VecKnapsackMitM.Main

/-! Algorithm 3, `dKnapsack-MitM(I, W̄, ε, ρ)` (Bringmann, Kulik, Węgrzycki 2026, printed p. 19,
PDF 20), as a specification: the set of all outputs it can return, over every admissible
choice the pseudocode leaves open (the order among equal profits in Line 1, the representative
solutions of Line 4 — any family with the properties Lemma 4.2 guarantees, a virtual item being
identified with the set it represents — the answer of each range query in Line 7 among the
maximizers, and the iteration order of Line 6). Item indices are 0-based: the paper's list
`L_{k+1}` is `L k` (`k : Fin (n + 1)`), and the paper's `{k + 1, …, n}` is `suffix n k`. -/

/-- `p(k + 1)` of the paper for `k : Fin (n + 1)`, with the convention `p(n + 1) = 0`. -/
def pAt {d n : ℕ} (I : Items d n) (k : Fin (n + 1)) : ℝ :=
  if h : k.val < n then I.p ⟨k.val, h⟩ else 0

/-- The properties of Lemma 4.2 (bullets 2–4, error parameter `ε`) for a family of lists
`L 0, …, L n` (the paper's `L_1, …, L_{n+1}`), virtual items identified with their sets:
every `v ∈ L k` is contained in `{k + 1, …, n}` (paper indices); `∅ ∈ L k`; and for every
`S ⊆ {k + 1, …, n}` some `v ∈ L k` has `w̄(v) ≤ w̄(S)`,
`p(v) ≥ (1 − ε) p(S) − (d − 1 + ε/n) p(k + 1)` and `p(v) ≥ (1 − ε)/d · p(S) − (ε/n) p(k + 1)`,
with `p(n + 1) = 0`. -/
def RepFamily {d n : ℕ} (I : Items d n) (ε : ℝ) (L : Fin (n + 1) → Finset (Finset (Fin n))) :
    Prop :=
  ∀ k : Fin (n + 1),
    (∀ v ∈ L k, v ⊆ Items.suffix n k.val) ∧ (∅ : Finset (Fin n)) ∈ L k ∧
    ∀ S ⊆ Items.suffix n k.val, ∃ v ∈ L k,
      (∀ t, I.weight v t ≤ I.weight S t) ∧
      (1 - ε) * I.profit S - ((d : ℝ) - 1 + ε / n) * pAt I k ≤ I.profit v ∧
      (1 - ε) / d * I.profit S - ε / n * pAt I k ≤ I.profit v

/-- Line 2: `q = ⌈(d − 1)/ε − d + ρ⌉`. -/
noncomputable def alg3q (d : ℕ) (ε ρ : ℝ) : ℤ := ⌈((d : ℝ) - 1) / ε - d + ρ⌉

/-- Line 2: `ℓ₁ = ⌊(q + d − 1)/2⌋`. -/
noncomputable def alg3l1 (d : ℕ) (ε ρ : ℝ) : ℤ := ⌊((alg3q d ε ρ : ℝ) + d - 1) / 2⌋

/-- Line 2: `ℓ₂ = max{q − ℓ₁, 1}`. -/
noncomputable def alg3l2 (d : ℕ) (ε ρ : ℝ) : ℤ := max (alg3q d ε ρ - alg3l1 d ε ρ) 1

/-- Line 4: `δ = ε² ρ / (2 (d − 1))`. -/
noncomputable def alg3delta (d : ℕ) (ε ρ : ℝ) : ℝ := ε ^ 2 * ρ / (2 * ((d : ℝ) - 1))

/-- Line 6: the index of the list `L_{max(S₂)+1}` (paper), i.e. `L k` with `k` one more than the
largest 0-based index of the nonempty `S₂`. -/
def nextIdx {n : ℕ} (S₂ : Finset (Fin n)) : Fin (n + 1) :=
  ⟨S₂.sup fun i => i.val + 1, Nat.lt_succ_of_le (Finset.sup_le fun i _ => i.isLt)⟩

/-- Line 7: `ans` is a correct answer of the ORS of Line 3 (storing every `S` with `|S| ≤ ℓ₁` at
the point `embed(S)` with profit `p(S)`) to the query box with upper corner `hi`: `none` (`⊥`)
if no stored set has its point in the box, otherwise a stored set `S₁` with its point in the
box and maximum profit among those. -/
def ORSAnswer {d n : ℕ} (I : Items d n) (l1 : ℤ) (hi : Fin (d + 1) → EReal)
    (ans : Option (Finset (Fin n))) : Prop :=
  match ans with
  | none => ∀ S : Finset (Fin n), (S.card : ℤ) ≤ l1 → ¬ InBox (rangeLo d) hi (embed I S)
  | some S₁ => (S₁.card : ℤ) ≤ l1 ∧ InBox (rangeLo d) hi (embed I S₁) ∧
      ∀ S : Finset (Fin n), (S.card : ℤ) ≤ l1 → InBox (rangeLo d) hi (embed I S) →
        I.profit S ≤ I.profit S₁

/-- Lines 5–9 on the profit-sorted instance `J`, for given lists `L` and query answers `ans`
(`ans S₂ v` answers the query `range_W̄(set(S₂ ∪ {v}))`): a candidate is a triple
`(S₁, S₂, v)` with `1 ≤ |S₂| ≤ ℓ₂`, `v ∈ L_{max(S₂)+1}` and `ans S₂ v = S₁ ≠ ⊥`, of value
`p(S₁) + p(S₂) + p(v)`; `best` starts at `∅` (value `0`) and is replaced only by a candidate of
strictly larger value, so over all iteration orders the returned `set(best)` is `∅` if no
candidate has positive value, and otherwise `S₁ ∪ S₂ ∪ v` for a candidate of maximum value. -/
def Alg3Returns {d n : ℕ} (J : Instance d n) (ε ρ : ℝ)
    (L : Fin (n + 1) → Finset (Finset (Fin n)))
    (ans : Finset (Fin n) → Finset (Fin n) → Option (Finset (Fin n)))
    (S : Finset (Fin n)) : Prop :=
  let IsCand : Finset (Fin n) → Finset (Fin n) → Finset (Fin n) → Prop := fun S₁ S₂ v =>
    1 ≤ S₂.card ∧ (S₂.card : ℤ) ≤ alg3l2 d ε ρ ∧ v ∈ L (nextIdx S₂) ∧ ans S₂ v = some S₁
  let val : Finset (Fin n) → Finset (Fin n) → Finset (Fin n) → ℝ := fun S₁ S₂ v =>
    J.toItems.profit S₁ + J.toItems.profit S₂ + J.toItems.profit v
  ((∀ S₁ S₂ v, IsCand S₁ S₂ v → val S₁ S₂ v ≤ 0) ∧ S = ∅) ∨
    ∃ S₁ S₂ v, IsCand S₁ S₂ v ∧ 0 < val S₁ S₂ v ∧
      (∀ S₁' S₂' v', IsCand S₁' S₂' v' → val S₁' S₂' v' ≤ val S₁ S₂ v) ∧ S = S₁ ∪ S₂ ∪ v

/-- `S` is a possible output of Algorithm 3 on `(inst, ε, ρ)`: Line 1 lists the items in an
order `σ` of non-increasing profit (the sorted instance `J = inst.reindex σ`, whose item `j` is
`σ j`); Line 4 returns lists `L` satisfying Lemma 4.2's guarantees with error
`δ = ε²ρ/(2(d−1))` for `J`; every query of Line 7 is answered correctly; and `S` is the image
under `σ` of a set Lines 5–9 can return. -/
def Alg3Output {d n : ℕ} (inst : Instance d n) (ε ρ : ℝ) (S : Finset (Fin n)) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), (inst.reindex σ).toItems.SortedByProfit ∧
    ∃ (L : Fin (n + 1) → Finset (Finset (Fin n)))
      (ans : Finset (Fin n) → Finset (Fin n) → Option (Finset (Fin n))) (S' : Finset (Fin n)),
      RepFamily (inst.reindex σ).toItems (alg3delta d ε ρ) L ∧
      (∀ S₂ v, ORSAnswer (inst.reindex σ).toItems (alg3l1 d ε ρ)
        (rangeHi (inst.reindex σ) (S₂ ∪ v)) (ans S₂ v)) ∧
      Alg3Returns (inst.reindex σ) ε ρ L ans S' ∧ S = S'.map σ.toEmbedding

end VecKnapsackMitM.Main


