-- Prove2me | Definitions.Def_SecSampling_AOSp
-- name    : SecSampling_AOSp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:29:43.953893+00:00
-- url     : https://prove2.me/theorems/09df12ee-df3b-4038-906c-abc4b24b1b40
-- title:
--   The adversarial-order secretary problem with $p$-sampling (AOSp), ordinal algorithms, and the $k$-max algorithm
-- statement:
--   **The problem AOSp** (p.2). There are $n$ elements with distinct values $\alpha_1,\dots,\alpha_n$, unknown to the player. Each element is **sampled** independently with probability $p$; let $S$ be the sampled set and $V$ the remaining **online** elements. The elements of $V$ are revealed one at a time in an order chosen by an adversary who knows all values and the sets $S$ and $V$. When an element is revealed the player either picks it and stops, or drops it forever. The player wins if she picks the maximum of $V$; if $V=\emptyset$ she wins by vacuity.
--
--   The probability of sampling exactly $S$ is $p^{|S|}(1-p)^{n-|S|}$, so the **success probability** of an algorithm on values $v$ and an order rule $S\mapsto \sigma(S)$ of the online set is
--   $$\sum_{S\subseteq[n]} p^{|S|}(1-p)^{n-|S|}\;\Pr\big[\text{the algorithm stops at }\max_{x\in V} v_x \;\big|\; S,\ \sigma(S)\big].$$
--
--   **Ordinal algorithms** (p.2). When the $i$-th online element $o_i$ arrives, the player has seen $|S|$, $n$, and, for each $j\le i$, the pair $(a_j,b_j)$: $a_j$ is the number of sampled elements with larger value than $o_j$ and $b_j$ the number of earlier online elements $o_1,\dots,o_{j-1}$ with larger value than $o_j$. These pairs are exactly the relative ranking of the values seen so far. An algorithm is a rule $A(n,|S|,(a_1,b_1),\dots,(a_i,b_i))\in[0,1]$ giving the probability of stopping at $o_i$.
--
--   **The $k$-max algorithm** (pp.2, 4). With $k=\lfloor 1/(1-p)\rfloor$, the threshold is the $k$-th largest sampled value ($-\infty$ if fewer than $k$ elements are sampled) and the algorithm accepts the first online element above it, i.e. the first $o_i$ with $a_i<k$. Its claimed success guarantee is $c(p)=k\,p^{k}(1-p)$.
--
--   These objects are the model in which the goal theorem and Lemma 1 are stated.
--
--   **Formalization Note.** Elements are `Fin n`; the sum over sampled sets is a finite sum over `Finset (Fin n)`. The adversary's order is a function `ord : Finset (Fin n) → List (Fin n)` required (by `IsOnlineOrder`) to list each online element exactly once; `indexOrder n` is the oblivious order by index. `kOf p` is $\lfloor 1/(1-p)\rfloor$ (`Nat.floor`), `guarantee p` is $k p^k(1-p)$.
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, §1 "The problem", p.2 (PDF p.3); footnotes 3–4; §2, pp.4–5 (PDF pp.5–6), definition of the k-max algorithm

import Mathlib

namespace SecSampling

/-- The threshold index `k = ⌊1/(1−p)⌋` of the k-max algorithm (Correa, Cristi, Feuilloley,
Oosterwijk & Tsigonias-Dimitriadis, *The Secretary Problem with Independent Sampling*,
arXiv:2011.07869v1, Theorem 1, p.5 and p.14).

**Formalization Note.** `⌊·⌋₊` is `Nat.floor`; for `p ∈ (0,1)` it is the usual floor of the
positive real `1/(1−p) ≥ 1`, so `kOf p ≥ 1`. -/
noncomputable def kOf (p : ℝ) : ℕ := ⌊1 / (1 - p)⌋₊

/-- The success guarantee `k pᵏ (1−p)` with `k = ⌊1/(1−p)⌋` (arXiv:2011.07869v1, Theorem 1,
p.14; Lemma 1, p.5). -/
noncomputable def guarantee (p : ℝ) : ℝ := (kOf p : ℝ) * p ^ kOf p * (1 - p)

/-- The probability `p^{|S|} (1−p)^{n−|S|}` that independent `p`-sampling of the `n` elements
produces exactly the sampled set `S` (arXiv:2011.07869v1, §1 "The problem", p.2: "Each element
is sampled independently with probability p").

**Formalization Note.** Elements are `Fin n`; the random sampled set is summed over all
`S : Finset (Fin n)` with this weight, so every probability below is a finite sum. -/
noncomputable def sampleWeight (p : ℝ) {n : ℕ} (S : Finset (Fin n)) : ℝ :=
  p ^ S.card * (1 - p) ^ (n - S.card)

/-- An **ordinal, possibly randomized algorithm** for AOSp (arXiv:2011.07869v1, p.2: "All
algorithms considered in this paper are ordinal, i.e., algorithms whose decision to stop at a
given point depend only on the relative rankings of the values seen so far ... plus, possibly, on
some external randomness").

`A n s h` is the probability of stopping at the current online element, given the number `n` of
elements, the number `s = |S|` of sampled elements, and the ordinal history `h` (see `hist`) of
the online elements seen so far, the current one last.

**Formalization Note.** Randomization is behavioural (one stopping probability per history);
since the history has perfect recall this is equivalent to any external randomness (Kuhn). The
algorithm may depend on `n` and, being chosen after `p`, on `p`. It sees no values, no indices,
and nothing about future elements. -/
abbrev Algorithm : Type := ℕ → ℕ → List (ℕ × ℕ) → ℝ

/-- An algorithm's stopping probabilities lie in `[0, 1]`. -/
def IsAlgorithm (A : Algorithm) : Prop :=
  ∀ (n s : ℕ) (h : List (ℕ × ℕ)), 0 ≤ A n s h ∧ A n s h ≤ 1

/-- The ordinal datum of an online element `x` that arrives after the online elements `earlier`:
the pair (number of sampled elements with larger value than `x`, number of earlier online
elements with larger value than `x`). -/
noncomputable def rankPair {n : ℕ} (v : Fin n → ℝ) (S : Finset (Fin n)) (earlier : List (Fin n))
    (x : Fin n) : ℕ × ℕ :=
  ((S.filter (fun y => v x < v y)).card, (earlier.filter (fun y => decide (v x < v y))).length)

/-- The **ordinal history** after the online elements `l = [o₁, …, oᵢ]` have been revealed: the
list of `rankPair`s `(aⱼ, bⱼ)`, `j = 1, …, i`, where `aⱼ` counts the samples above `oⱼ` and `bⱼ`
the earlier online elements `o₁, …, o_{j−1}` above `oⱼ`.

**Formalization Note.** Together with `|S|`, these insertion ranks determine exactly the relative
order of `S ∪ {o₁, …, oᵢ}` with the samples unlabelled, i.e. "the relative rankings of the values
seen so far" (p.2), and nothing more. -/
noncomputable def hist {n : ℕ} (v : Fin n → ℝ) (S : Finset (Fin n)) (l : List (Fin n)) :
    List (ℕ × ℕ) :=
  List.ofFn (fun j : Fin l.length => rankPair v S (l.take j) l[j])

/-- Probability that algorithm `A` stops at the maximum-valued element of the online sequence
`L`, given that the online elements `seen` have already been passed and `rest` remain. At each
element `x`, `A` stops with probability `a = A n |S| (history up to x)`; it wins if `x` is the
maximum of `L`, and otherwise continues with probability `1 − a`. -/
noncomputable def stopAtMaxProb (A : Algorithm) {n : ℕ} (v : Fin n → ℝ) (S : Finset (Fin n))
    (L : List (Fin n)) : List (Fin n) → List (Fin n) → ℝ
  | _, [] => 0
  | seen, x :: rest =>
      (if ∀ y ∈ L, v y ≤ v x then A n S.card (hist v S (seen ++ [x])) else 0) +
        (1 - A n S.card (hist v S (seen ++ [x]))) * stopAtMaxProb A v S L (seen ++ [x]) rest

/-- Success probability of `A` for a fixed sampled set `S` when the online elements are presented
in the order `L`. If `L` is empty (everything was sampled) the player wins by vacuity
(arXiv:2011.07869v1, p.2: "For consistency in this case we assume, by vacuity, that we win"). -/
noncomputable def winOnSample (A : Algorithm) {n : ℕ} (v : Fin n → ℝ) (S : Finset (Fin n))
    (L : List (Fin n)) : ℝ :=
  if L = [] then 1 else stopAtMaxProb A v S L [] L

/-- The **success probability** of algorithm `A` on the instance with values `v`, when the
online set `V = Sᶜ` is presented in the order `ord S`: the expectation over independent
`p`-sampling (arXiv:2011.07869v1, p.2).

**Formalization Note.** `ord : Finset (Fin n) → List (Fin n)` may depend on the sampled set, which
is the AOSp adversary that "knows all values α₁, …, αₙ and the random sets S and V" (p.2). -/
noncomputable def winProb (p : ℝ) (A : Algorithm) {n : ℕ} (v : Fin n → ℝ)
    (ord : Finset (Fin n) → List (Fin n)) : ℝ :=
  ∑ S : Finset (Fin n), sampleWeight p S * winOnSample A v S (ord S)

/-- `ord` presents, for every sampled set `S`, each online element (each element of `Sᶜ`)
exactly once. -/
def IsOnlineOrder {n : ℕ} (ord : Finset (Fin n) → List (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), (ord S).Nodup ∧ ∀ x : Fin n, x ∈ ord S ↔ x ∉ S

/-- The oblivious order: the online elements in increasing index order (fixed before sampling;
any fixed order reduces to it by relabelling the values). -/
def indexOrder (n : ℕ) (S : Finset (Fin n)) : List (Fin n) :=
  (List.finRange n).filter (fun x => decide (x ∉ S))

/-- The **k-max algorithm** with `k = ⌊1/(1−p)⌋` (arXiv:2011.07869v1, p.2 and p.4): the k-th
largest sampled value is the threshold (`−∞` if there are fewer than `k` samples, footnote 4), and
the algorithm accepts the first online element whose value surpasses it.

**Formalization Note.** An online element surpasses the k-th largest sample iff fewer than `k`
samples are larger than it, i.e. iff the first coordinate of its `rankPair` is `< k`; with fewer
than `k` samples this always holds, matching the `−∞` convention. -/
noncomputable def kmax (p : ℝ) : Algorithm := fun _ _ h =>
  match h.getLast? with
  | some (a, _) => if a < kOf p then 1 else 0
  | none => 0

end SecSampling


