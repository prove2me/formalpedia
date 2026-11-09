-- Prove2me | Definitions.Def_TarskiQuasiFPT_UpperBound_QueryAnswerSets
-- name    : TarskiQuasiFPT_UpperBound_QueryAnswerSets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:38.042828+00:00
-- url     : https://prove2.me/theorems/8a5e4937-ee0e-4b2f-9f52-ac5954b23e29
-- title:
--   Query-answer sets, postfixed points, $J_s(Q)$, $M_s(Q)$, Fix$(Q)$, Fix$^{\pm}(Q)$, bad pairs $R(Q)$, antipodal set-pairs
-- statement:
--   Fix $n\ge1$ and $k$.
--
--   1. **Query-answer sets (§2.3).** A query-answer set $Q=\{(x^1,r^1),\dots,(x^q,r^q)\}$ records distinct points $x^j\in[n]^k$ with answers $r^j\in[n]^k\times\{\pm1\}$. A function $h$ is **consistent** with $Q$, written $h\Rightarrow Q$, if $h(x)=r$ for all $(x,r)\in Q$; $Q\subseteq Q'$ is inclusion of pairs; $Q$ is **safe** if some safe $h\Rightarrow Q$ exists.
--   2. **Postfixed and prefixed points.** $y\in L_s$ is **postfixed for $Q$ on $s$** if $h(y)_i\ge y_i$ for every $i\in F(s)$ and every **monotone** (not necessarily safe) $h\Rightarrow Q$; **prefixed** with $\le$ instead.
--   3. **$J_s(Q)$ and $M_s(Q)$.** $J_s(Q)$ is the coordinatewise join of all postfixed points for $Q$ on $s$ and $M_s(Q)$ the coordinatewise meet of all prefixed points; by Lemma 2 these are the greatest postfixed and least prefixed points when $Q$ is safe. $J(Q)$ and $M(Q)$ are the values on the all-$*$ slice.
--   4. **Candidate sets (§2.4).**
--   $$\mathrm{Fix}(Q)=\{x\in[n]^k:\ J_s(Q)\preceq x\preceq M_s(Q)\ \text{for every slice } s \text{ with } x\in L_s\},$$
--   $\mathrm{Fix}^-(Q)=\{x\in\mathrm{Fix}(Q):$ no $(y,r)\in Q$ has $y\preceq x$ and $r_{k+1}=+1\}$ and $\mathrm{Fix}^+(Q)=\{x\in\mathrm{Fix}(Q):$ no $(y,r)\in Q$ has $x\preceq y$ and $r_{k+1}=-1\}$.
--   5. **Coordinate separation and bad pairs (§2.5).** $(A,B)$ is coordinate-separable if $\max_{x\in A}x_k\le\min_{y\in B}y_k$; the bad point-pairs are $R(Q)=\{(x,y): x\in\mathrm{Fix}^-(Q),\ y\in\mathrm{Fix}^+(Q),\ x_k>y_k\}$.
--   6. **Antipodal set-pairs (Lemma 10 (ii)).** $(S^-,S^+)$ is antipodal if there are a partition $[k]=J\sqcup H$ with $k\in H$ and $t\in[n]^k$ such that for all $x\in S^-$, $y\in S^+$: $x_J\preceq t_J\preceq y_J$ and $x_H\succeq t_H\succeq y_H$; and $x_k\ge t_k+1$ for every $x\in S^-$.
--
--   These objects carry the whole proof of Theorem 5.
--
--   **Formalization Note** $Q$ is a partial function `Point n k → Option (Point n k × Label)`. $J_s(Q)$ and $M_s(Q)$ are `Finset.sup`/`Finset.inf` over the finite set of postfixed/prefixed points, so they are defined for every $Q$ (bottom/top point on an empty set, which Lemma 2 excludes for safe $Q$); nothing is defined through a choice that only Lemma 2 justifies. Coordinate separation is "$x_c\le y_c$ for all $x\in A$, $y\in B$", which agrees with max ≤ min on nonempty sets and is vacuous when a set is empty (the case Lemma 9's proof calls trivial). The distinguished coordinate is a parameter `c`; theorems fix it to the last one. In the antipodal predicate the finset `J` (not containing `c`) is the paper's $J$ and its complement is $H$; $x_k\ge t_k+1$ is written $t_c<x_c$.
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, §2.3 (PDF p. 6 / printed p. 5), J_s and M_s after Lemma 2 (PDF p. 7 / printed p. 6), §2.4 Fix, Fix± (PDF pp. 7–8 / printed pp. 6–7), §2.5 coordinate-separable and R(Q) (PDF pp. 9–10 / printed pp. 8–9), Lemma 10 (ii) (PDF p. 11 / printed p. 10)

import Mathlib
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid

set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound

/-! # Query-answer sets, postfixed/prefixed points, `J_s(Q)`, `M_s(Q)`, `Fix(Q)`, `Fix±(Q)`,
bad point-pairs `R(Q)` and antipodal set-pairs

Chen, Gao, Li, Rubinstein, Yannakakis, *Tarski Fixed Points in Quasi-FPT Queries*,
STOC 2027 submission #403, §2.3–§2.6 (PDF pp. 6–11). -/

variable {n k : ℕ}

/-- A query-answer set `Q` (§2.3): the recorded queried points, each with its answer in
`[n]^k × {±1}`. Encoded as a partial function, `Q x = some r` meaning `(x, r) ∈ Q`, so the
queried points are automatically distinct and `Q` is finite. -/
abbrev QASet (n k : ℕ) := Point n k → Option (Point n k × Label)

/-- `h ⇒ Q` (`h` is consistent with `Q`): `h(x) = r` for every `(x, r) ∈ Q`. -/
def Consistent (h : Point n k → Point n k × Label) (Q : QASet n k) : Prop :=
  ∀ x r, Q x = some r → h x = r

/-- `Q ⊆ Q'`: every recorded pair of `Q` is a recorded pair of `Q'`. -/
def QASubset (Q Q' : QASet n k) : Prop :=
  ∀ x r, Q x = some r → Q' x = some r

/-- `Q` is a **safe** query-answer set: some safe function is consistent with it. -/
def IsSafeQA (Q : QASet n k) : Prop :=
  ∃ h : Point n k → Point n k × Label, IsSafe h ∧ Consistent h Q

/-- `Q` extended by the answers `(y, g y)` of `g` at every point `y` of the list `L`. -/
def extendQA (Q : QASet n k) (g : Point n k → Point n k × Label) (L : List (Point n k)) :
    QASet n k :=
  fun x => if x ∈ L then some (g x) else Q x

/-- `y` is **postfixed for `Q` on slice `s`** (§2.3): `y ∈ L_s` and `h(y)_i ≥ y_i` for every
free coordinate `i ∈ F(s)` and every **monotone** (not necessarily safe; footnote 3)
`h : [n]^k → [n]^k × {±1}` consistent with `Q`. -/
def IsPostfixed (Q : QASet n k) (s : Slice n k) (y : Point n k) : Prop :=
  InSlice s y ∧ ∀ h : Point n k → Point n k × Label, Monotone h → Consistent h Q →
    ∀ i : Fin k, s i = none → y i ≤ (h y).1 i

/-- `y` is **prefixed for `Q` on slice `s`**: `y ∈ L_s` and `h(y)_i ≤ y_i` for every
`i ∈ F(s)` and every monotone `h ⇒ Q`. -/
def IsPrefixed (Q : QASet n k) (s : Slice n k) (y : Point n k) : Prop :=
  InSlice s y ∧ ∀ h : Point n k → Point n k × Label, Monotone h → Consistent h Q →
    ∀ i : Fin k, s i = none → (h y).1 i ≤ y i

open Classical in
/-- `J_s(Q)` (§2.3, after Lemma 2): the coordinatewise maximum (join) of all postfixed points
for `Q` on `s`. By Lemma 2 (for safe `Q`) this set is nonempty and join-closed, so `J_s(Q)` is
the greatest postfixed point. If the set were empty the value would be the bottom point. -/
noncomputable def Js [NeZero n] (Q : QASet n k) (s : Slice n k) : Point n k :=
  (Finset.univ.filter fun y => IsPostfixed Q s y).sup id

open Classical in
/-- `M_s(Q)`: the coordinatewise minimum (meet) of all prefixed points for `Q` on `s`; by
Lemma 2, for safe `Q`, the least prefixed point. If the set were empty the value would be the
top point. -/
noncomputable def Ms [NeZero n] (Q : QASet n k) (s : Slice n k) : Point n k :=
  (Finset.univ.filter fun y => IsPrefixed Q s y).inf id

/-- The all-`∗` slice `(∗, …, ∗)`, whose point set is the whole grid. -/
def allStar : Slice n k := fun _ => none

/-- `J(Q) = J_{(∗,…,∗)}(Q)`. -/
noncomputable def J [NeZero n] (Q : QASet n k) : Point n k := Js Q allStar

/-- `M(Q) = M_{(∗,…,∗)}(Q)`. -/
noncomputable def M [NeZero n] (Q : QASet n k) : Point n k := Ms Q allStar

open Classical in
/-- `Fix(Q) = {x ∈ [n]^k : J_s(Q) ⪯ x ⪯ M_s(Q) for every slice s with x ∈ L_s}` (§2.4). -/
noncomputable def Fix [NeZero n] (Q : QASet n k) : Finset (Point n k) :=
  Finset.univ.filter fun x => ∀ s : Slice n k, InSlice s x → Js Q s ≤ x ∧ x ≤ Ms Q s

open Classical in
/-- `Fix⁻(Q) = {x ∈ Fix(Q) : there is no (y, r) ∈ Q with y ⪯ x and r_{k+1} = +1}`. -/
noncomputable def FixMinus [NeZero n] (Q : QASet n k) : Finset (Point n k) :=
  (Fix Q).filter fun x => ¬ ∃ y r, Q y = some r ∧ y ≤ x ∧ r.2 = Label.pos

open Classical in
/-- `Fix⁺(Q) = {x ∈ Fix(Q) : there is no (y, r) ∈ Q with x ⪯ y and r_{k+1} = −1}`. -/
noncomputable def FixPlus [NeZero n] (Q : QASet n k) : Finset (Point n k) :=
  (Fix Q).filter fun x => ¬ ∃ y r, Q y = some r ∧ x ≤ y ∧ r.2 = Label.neg

/-- `(A, B)` is **coordinate-separable** along coordinate `c` (§2.5):
`max_{x ∈ A} x_c ≤ min_{y ∈ B} y_c`, written as `x_c ≤ y_c` for all `x ∈ A`, `y ∈ B`
(the paper uses `c = k`, the last coordinate). -/
def CoordSeparable (c : Fin k) (A B : Finset (Point n k)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, x c ≤ y c

/-- `R(Q)`, the **bad point-pairs** along coordinate `c` (§2.5):
`{(x, y) : x ∈ Fix⁻(Q), y ∈ Fix⁺(Q), x_c > y_c}` (the paper uses `c = k`). -/
noncomputable def badPairs [NeZero n] (Q : QASet n k) (c : Fin k) :
    Finset (Point n k × Point n k) :=
  (FixMinus Q ×ˢ FixPlus Q).filter fun p => p.2 c < p.1 c

/-- `(S⁻, S⁺)` is **antipodal** (item (ii) of Lemma 10), with distinguished coordinate `c`
(the paper's coordinate `k`): there are a partition `[k] = J ⊔ H` with `c ∈ H` (here `J` is a
finset not containing `c` and `H` its complement) and a vector `t ∈ [n]^k` such that for every
`x ∈ S⁻` and `y ∈ S⁺`, `x_J ⪯ t_J ⪯ y_J` and `x_H ⪰ t_H ⪰ y_H`; moreover `x_c ≥ t_c + 1`
(i.e. `t_c < x_c`) for every `x ∈ S⁻`. -/
def IsAntipodal (c : Fin k) (Sm Sp : Finset (Point n k)) : Prop :=
  ∃ (Jset : Finset (Fin k)) (t : Point n k), c ∉ Jset ∧
    (∀ x ∈ Sm, ∀ y ∈ Sp, ∀ i : Fin k,
      (i ∈ Jset → x i ≤ t i ∧ t i ≤ y i) ∧ (i ∉ Jset → t i ≤ x i ∧ y i ≤ t i)) ∧
    ∀ x ∈ Sm, t c < x c

end TarskiQuasiFPT.UpperBound


