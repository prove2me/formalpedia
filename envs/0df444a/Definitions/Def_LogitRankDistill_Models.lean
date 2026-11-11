-- Prove2me | Definitions.Def_LogitRankDistill_Models
-- name    : LogitRankDistill_Models
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:58:09.654697+00:00
-- url     : https://prove2.me/theorems/d397ee67-9684-4d65-a93d-9d3b3c1e9f0b
-- title:
--   Language models on Σ^T, conditionals, mean-centered logits, softmax, logit oracles, α-bounded rank-d logit matrices and approximate bounded low logit rank
-- statement:
--   Let $\Sigma$ be a finite alphabet and $T$ a positive integer. A **language model** is a distribution $M$ on $\Sigma^T$ (Definition 1.1). For a history $h=y_{1:t}$ and a token $y$, $M(y\mid h)=\Pr_M(y_{t+1}=y\mid y_{1:t}=h)$, computed as the ratio of the prefix masses $\Pr_M(y_{1:t+1}=h\circ y)/\Pr_M(y_{1:t}=h)$. $M$ has **full support** when $M(x)>0$ for every $x\in\Sigma^T$; then every conditional with $t\le T-1$ is positive.
--
--   The **mean-centering projection** is $\Pi_1(v)=v-\frac1{|\Sigma|}(\mathbf 1^\top v)\mathbf 1$ for $v\in\mathbb R^\Sigma$, and the **mean-centered logits** are (Definition 1.2)
--   $$L_M(y\mid h)=\log M(y\mid h)-\frac1{|\Sigma|}\sum_{z\in\Sigma}\log M(z\mid h).$$
--   The logit matrix $L_M(H,F)$ (Definition 1.3) has $(h,(f,z))$-entry $L_M(z\mid h\circ f)$. $\mathrm{softmax}(L)(y)=e^{L(y)}/\sum_z e^{L(z)}$.
--
--   A function $O$ from sequences to $\mathbb R^\Sigma$ is an **exact logit oracle** for $M$ (Definition 1.7) if $O(y_{1:t})=\log M(\cdot\mid y_{1:t})$ for every $t\le T-1$, and an **$\varepsilon$-approximate logit oracle** (Definition 4.1) if $\|\Pi_1O(y_{1:t})-L_M(\cdot\mid y_{1:t})\|_\infty\le\varepsilon$ for every $t\le T-1$. From one oracle call, $L_{\mathrm{oracle}}(y_{1:t})=\Pi_1(O(y_{1:t-1}))_{y_t}$ (Eq. (11)).
--
--   A matrix $L\in\mathbb R^{\Sigma^s\times(\Sigma^{\le T-s-1}\times\Sigma)}$ is **$\alpha$-bounded of rank $d$** (Definition 4.2) if there are vectors $A^{\mathrm{hist}}_h,A^{\mathrm{fut}}_{f,y}\in\mathbb R^d$ of Euclidean norm at most $\alpha$, the first depending only on $h$ and the second only on $(f,y)$, with $L_{h,(f,y)}=\langle A^{\mathrm{fut}}_{f,y},A^{\mathrm{hist}}_h\rangle$.
--
--   $M$ has **$\varepsilon$-approximate $\alpha$-bounded logit rank $d$** (Definitions 1.6 and 4.3) if for each $0\le s\le T$ there is an $\alpha$-bounded rank-$d$ matrix $L^{(s)}$ such that for all $0\le s<t\le T$
--   $$\mathbb E\,\big|L^{(s)}(h,(f,y_t))-L_M(y_t\mid h\circ f)\big|\le\varepsilon,$$
--   where $h=y_{1:s-1}\circ y_s$ with $y_{1:s-1}\sim M_{1:s-1}$ and $y_s\sim\mathrm{Unif}(\Sigma)$, $f\sim M_{s+1:t-1}$ and $y_t\sim\mathrm{Unif}(\Sigma)$, all independent (the history and the future are read from two independent draws of $M$); at $s=0$ the history is empty.
--
--   An oracle's **execution trace** (the list of queried sequences) is **$\varepsilon$-approximately $\alpha$-bounded of rank $d$** (Definition 4.4) if for each $s\in[T]$ there is an $\alpha$-bounded rank-$d$ matrix $L^{(s)}$ with $\|\Pi_1(O(y_{1:t-1}))-L^{(s)}(y_{1:s},(y_{s+1:t-1},\cdot))\|_\infty\le\varepsilon$ for every query $y_{1:t-1}$ of the trace with $s<t\le T$.
--
--   **Formalization Note.** $M$ is a `PMF (Fin T → Tok)`; histories, futures and queries are `List Tok`, `h ++ f` is $h\circ f$; `pre x k` $=y_{1:k}$ and `seg x a b` $=y_{a:b}$ (1-based, inclusive). Conditionals are prefix-mass ratios (Lean's $a/0=0$ only matters off the support). An oracle is a function `List Tok → Tok → ℝ`; its values on sequences of length $\ge T$ are unconstrained. Matrices are functions `L h f y`; Definition 4.2 constrains only the entries with $|h|=s$, $s+|f|+1\le T$. Total variation is the published `IsingLTL.BeliefProp.tvDist` ($\tfrac12\ell_1$).
-- source:
--   Golowich, Liu, Shetty, Provably Distilling from Modern Language Models via Low Logit Rank, manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), p. 2 Definition 1.1; p. 3 Definitions 1.2, 1.3 and footnote 2; p. 4 Definition 1.6; p. 6 Definition 1.7; p. 17 Π₁, Definitions 4.1, 4.2, 4.3; p. 18 Definition 4.4; p. 20 Eq. (11)

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist

namespace LogitRankDistill

/-!
# Language models on `Σ^T`, logits, oracles and approximate bounded low logit rank

Golowich, Liu, Shetty, *Provably Distilling from Modern Language Models via Low Logit Rank*,
manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…): §1.1 pp. 2–6
(Definitions 1.1, 1.2, 1.3, 1.6, 1.7, footnote 2) and §4.1 pp. 17–18 (Π₁, Definitions 4.1–4.4,
Eq. (11)).

Conventions.
* The alphabet `Σ` is a finite type `Tok`. A **language model** (Definition 1.1) is a probability
  mass function `M : PMF (Fin T → Tok)` on full sequences; position `j ∈ {1, …, T}` of the paper
  is the index `j - 1` of `Fin T`.
* Histories, futures and oracle queries are lists of tokens (`List Tok`); `h ++ f` is `h ∘ f`.
  For a full sequence `x`, `pre x k = y_{1:k}` and `seg x a b = y_{a:b}` (1-based, inclusive,
  empty when `b < a`).
* `M(f | h)` is the ratio of prefix masses; it is a genuine conditional probability when
  `M(h) > 0`, which holds for every prefix under `FullSupport M`.
* The total variation distance is the published `IsingLTL.BeliefProp.tvDist p q = ½ ∑|p − q|`.
-/

variable {Tok : Type*} [Fintype Tok] [DecidableEq Tok]

/-- `y_{1:k}` of a full sequence `x`, as a list (the first `k` tokens; all of `x` if `k ≥ T`). -/
def pre {T : ℕ} (x : Fin T → Tok) (k : ℕ) : List Tok :=
  (List.ofFn x).take k

/-- `y_{a:b}` of a full sequence `x` (positions `a, …, b`, 1-based and inclusive), as a list;
empty when `b < a`. -/
def seg {T : ℕ} (x : Fin T → Tok) (a b : ℕ) : List Tok :=
  ((List.ofFn x).drop (a - 1)).take (b + 1 - a)

/-- The prefix mass `Pr_M(y_{1:t} = h)` of a history `h` (`t = |h|`); it is `0` when `|h| > T`. -/
noncomputable def prefixMass {T : ℕ} (M : PMF (Fin T → Tok)) (h : List Tok) : ℝ :=
  ∑ x, if pre x h.length = h then (M x).toReal else 0

/-- `M(y | h) = Pr_M(y_{t+1} = y | y_{1:t} = h)` (Definition 1.1), as the ratio of prefix masses. -/
noncomputable def condProb {T : ℕ} (M : PMF (Fin T → Tok)) (h : List Tok) (y : Tok) : ℝ :=
  prefixMass M (h ++ [y]) / prefixMass M h

/-- `M` gives positive probability to every full sequence. Under it every conditional
probability `M(y | h)` with `|h| < T` is positive, so logits and the exact logit oracle are
defined at every prefix. -/
def FullSupport {T : ℕ} (M : PMF (Fin T → Tok)) : Prop :=
  ∀ x, M x ≠ 0

/-- The mean-centering projection `Π₁(v) = v − (1/|Σ|)(1ᵀv)·1` (§4.1, p. 17). -/
noncomputable def center (v : Tok → ℝ) : Tok → ℝ :=
  fun y => v y - (1 / (Fintype.card Tok : ℝ)) * ∑ z, v z

/-- The mean-centered logit `L_M(y | h) = log M(y | h) − (1/|Σ|) ∑_{z} log M(z | h)`
(Definition 1.2). The logit matrix `L_M(H, F)` of Definition 1.3 has `(h, (f, z))`-entry
`logit M (h ++ f) z`. -/
noncomputable def logit {T : ℕ} (M : PMF (Fin T → Tok)) (h : List Tok) (y : Tok) : ℝ :=
  center (fun z => Real.log (condProb M h z)) y

/-- `softmax L` (footnote 2, p. 3): `softmax(L)(y) = exp(L(y)) / ∑_z exp(L(z))`. -/
noncomputable def softmax (L : Tok → ℝ) : Tok → ℝ :=
  fun y => Real.exp (L y) / ∑ z, Real.exp (L z)

/-- `O` is an **exact logit oracle** for `M` (Definition 1.7): on every sequence `y_{1:t}` with
`t ≤ T − 1` it returns the vector `log M(y_{t+1} = · | y_{1:t}) ∈ ℝ^Σ`. Its values on longer
sequences are unconstrained (never queried). -/
def IsExactOracle {T : ℕ} (M : PMF (Fin T → Tok)) (O : List Tok → Tok → ℝ) : Prop :=
  ∀ h : List Tok, h.length < T → ∀ y, O h y = Real.log (condProb M h y)

/-- `O` is an **`ε`-approximate logit oracle** for `M` (Definition 4.1):
`‖Π₁ O(y_{1:t}) − L_M(y_{t+1} = · | y_{1:t})‖_∞ ≤ ε` for every `y_{1:t}` with `t ≤ T − 1`. -/
def IsApproxOracle {T : ℕ} (M : PMF (Fin T → Tok)) (ε : ℝ) (O : List Tok → Tok → ℝ) : Prop :=
  ∀ h : List Tok, h.length < T → ∀ y, |center (O h) y - logit M h y| ≤ ε

/-- `L_oracle(y_{1:t}) := Π₁(O(y_{1:t−1}))_{y_t}` (Eq. (11)), computed from one oracle call on
`y_{1:t−1}`; `0` on the empty sequence (never used). -/
noncomputable def Lor (O : List Tok → Tok → ℝ) (q : List Tok) : ℝ :=
  match q.getLast? with
  | none => 0
  | some y => center (O q.dropLast) y

/-- A matrix `L ∈ ℝ^{Σ^s × (Σ^{≤T−s−1} × Σ)}`, given as `L h f y` for its `(h, (f, y))` entry,
is **`α`-bounded of rank `d`** (Definition 4.2): there are vectors `A^hist_h, A^fut_{f,y} ∈ ℝ^d`,
the first depending on `h` only and the second on `(f, y)` only, with Euclidean norms at most `α`
and `L h f y = ⟨A^fut_{f,y}, A^hist_h⟩` for every row `h ∈ Σ^s` and every column `(f, y)` with
`|f| ≤ T − s − 1`. Entries outside these rows and columns are unconstrained. -/
def IsBoundedRank (T s d : ℕ) (α : ℝ) (L : List Tok → List Tok → Tok → ℝ) : Prop :=
  ∃ (Ah : List Tok → EuclideanSpace ℝ (Fin d)) (Af : List Tok → Tok → EuclideanSpace ℝ (Fin d)),
    (∀ h : List Tok, h.length = s → ‖Ah h‖ ≤ α) ∧
    (∀ (f : List Tok) (y : Tok), s + f.length + 1 ≤ T → ‖Af f y‖ ≤ α) ∧
    ∀ (h f : List Tok) (y : Tok), h.length = s → s + f.length + 1 ≤ T →
      L h f y = inner ℝ (Af f y) (Ah h)

/-- The average error in Eq. (1) of Definition 1.6 for `0 ≤ s < t ≤ T`:
`E |L^{(s)}(h, (f, y_t)) − L_M(y_t | h ∘ f)|` where `h = y_{1:s−1} ∘ y_s` with
`y_{1:s−1} ∼ M_{1:s−1}`, `y_s ∼ Unif(Σ)`, `f ∼ M_{s+1:t−1}`, `y_t ∼ Unif(Σ)`, all independent
(`h` is read from a sample `x`, `f` from an independent sample `x'`). At `s = 0` the history is
empty. -/
noncomputable def avgErr {T : ℕ} (M : PMF (Fin T → Tok)) (L : List Tok → List Tok → Tok → ℝ)
    (s t : ℕ) : ℝ :=
  if s = 0 then
    ∑ x' : Fin T → Tok, ∑ v : Tok,
      (M x').toReal / (Fintype.card Tok : ℝ) *
        |L [] (seg x' 1 (t - 1)) v - logit M (seg x' 1 (t - 1)) v|
  else
    ∑ x : Fin T → Tok, ∑ u : Tok, ∑ x' : Fin T → Tok, ∑ v : Tok,
      (M x).toReal * (M x').toReal / (Fintype.card Tok : ℝ) ^ 2 *
        |L (pre x (s - 1) ++ [u]) (seg x' (s + 1) (t - 1)) v -
          logit M (pre x (s - 1) ++ [u] ++ seg x' (s + 1) (t - 1)) v|

/-- `M` has **`ε`-approximate `α`-bounded logit rank `d`** (Definitions 1.6 and 4.3): for each
`0 ≤ s ≤ T` there is a matrix `L^{(s)}` that is `α`-bounded of rank `d` (Definition 4.2) such
that the average error (1) is at most `ε` for every `0 ≤ s < t ≤ T`. -/
def HasApproxBoundedLogitRank {T : ℕ} (M : PMF (Fin T → Tok)) (ε α : ℝ) (d : ℕ) : Prop :=
  ∃ L : ℕ → List Tok → List Tok → Tok → ℝ,
    (∀ s, s ≤ T → IsBoundedRank T s d α (L s)) ∧
    ∀ s t, s < t → t ≤ T → avgErr M (L s) s t ≤ ε

/-- The **execution trace** `Q` (the list of sequences on which `O` was called) is
**`ε`-approximately `α`-bounded of rank `d`** (Definition 4.4): for each `s ∈ [T]` there is a
matrix `L^{(s)}`, `α`-bounded of rank `d`, such that every query `q = y_{1:t−1}` of the trace
with `t ∈ [T]` and `t > s` satisfies
`‖Π₁(O(y_{1:t−1})) − L^{(s)}(y_{1:s}, (y_{s+1:t−1}, ·))‖_∞ ≤ ε`. -/
def TraceBoundedRank (T d : ℕ) (α ε : ℝ) (O : List Tok → Tok → ℝ) (Q : List (List Tok)) :
    Prop :=
  ∀ s, 1 ≤ s → s ≤ T → ∃ L : List Tok → List Tok → Tok → ℝ, IsBoundedRank T s d α L ∧
    ∀ q ∈ Q, s ≤ q.length → q.length + 1 ≤ T → ∀ y : Tok,
      |center (O q) y - L (q.take s) (q.drop s) y| ≤ ε

end LogitRankDistill


