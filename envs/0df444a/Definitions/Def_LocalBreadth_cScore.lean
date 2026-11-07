-- Prove2me | Definitions.Def_LocalBreadth_cScore
-- name    : LocalBreadth_cScore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:53:08.645957+00:00
-- url     : https://prove2.me/theorems/b02dfe64-7be0-40d8-aea0-c8269e600cc9
-- title:
--   The pairing scores p(H, J) and c_n(H)
-- statement:
--   The **layers** of a chain $H=(L_0\supsetneq\dots\supsetneq L_d)$ are $L_d$ and the differences $L_i\setminus L_{i+1}$; they partition $L_0$. A **relative interval** of $A$ is a finite set of consecutive points of $A$. The **raw pairing score** of $H$ on a relative interval $J$ of its starting language $A$ is
--   $$p(H,J)=\frac1{|J|}\sum_{\text{layers }E\text{ of }H}\Bigl\lfloor\frac{|E\cap J|}2\Bigr\rfloor,$$
--   and the **pairing score** is
--   $$c_n(H)=\lim_{R\to\infty}\ \inf_{\substack{J\text{ a relative interval of }A\\|J|\ge n,\ J\cap[-R,R]=\emptyset}}p(H,J).$$
--   Here $n$ stays fixed: short intervals far from the origin still count.
--
--   The score measures how many points a generator can hold in the alternating game on each layer.
--
--   **Formalization Note** A relative interval is `A ∩ Icc a b`, and a chain is a plain list, so the same functions also score the compressed chains of §5.8.2. The limit is a supremum over natural $R$, since the infimum increases with $R$ and is at most $1/2$ for an infinite starting language and $n\ge1$.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Definition 2.1, eq. (6), p.14; eq. (8), p.15

import Mathlib

namespace LocalBreadth

/-- The **layers** of a chain `L₀ ⊋ ⋯ ⊋ L_d` (p.14): the sets `L_i \ L_{i+1}` and `L_d`. -/
def layers : List (Set ℤ) → List (Set ℤ)
  | [] => []
  | [L] => [L]
  | L :: M :: t => (L \ M) :: layers (M :: t)

/-- A **relative interval** of `A` (p.5): a finite run of consecutive points of `A`.

**Formalization Note.** Every such run is `A ∩ Icc a b`; the families below always ask `|J| ≥ n` with
`n ≥ 1`, which excludes the empty run. -/
def IsRelInterval (A J : Set ℤ) : Prop := ∃ a b : ℤ, J = A ∩ Set.Icc a b

/-- The **raw pairing score**. Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…),
Definition 2.1, eq. (6), p.14: `p(H, J) = (1/|J|) Σ_{layers E of H} ⌊|E ∩ J|/2⌋`.

**Formalization Note.** A chain is a list of languages, so the same function scores a history and
the compressed chain `H[a, v]` of §5.8.2. -/
noncomputable def pScore (c : List (Set ℤ)) (J : Set ℤ) : ℝ :=
  (((layers c).map fun E => (E ∩ J).ncard / 2).sum : ℕ) / (J.ncard : ℝ)

/-- The **pairing score**, eq. (8), p.15:
`c_n(H) = lim_{R→∞} inf_{J relative interval of A, |J| ≥ n, J ∩ [−R, R] = ∅} p(H, J)`, where `A` is
the starting language of `H`.

**Formalization Note.** The infimum increases with `R` (fewer intervals) and is at most `1/2`, so
the limit is this supremum over `R : ℕ`. `n` stays fixed: short intervals far out still count. For
infinite `A` and `n ≥ 1` the index family is nonempty, as the page remarks. -/
noncomputable def cScore (n : ℕ) (c : List (Set ℤ)) : ℝ :=
  ⨆ R : ℕ, ⨅ J : {J : Set ℤ // IsRelInterval (c.headD ∅) J ∧ n ≤ J.ncard ∧
      Disjoint J (Set.Icc (-(R : ℤ)) (R : ℤ))},
    pScore c J.1

end LocalBreadth


