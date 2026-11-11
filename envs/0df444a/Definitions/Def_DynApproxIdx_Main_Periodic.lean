-- Prove2me | Definitions.Def_DynApproxIdx_Main_Periodic
-- name    : DynApproxIdx_Main_Periodic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:51:21.883722+00:00
-- url     : https://prove2.me/theorems/44f99708-8a30-438f-89b4-236cb33a79cc
-- title:
--   Q-decompositions, d-far strings (Definitions 7.3, 7.4) and the shift by one period
-- statement:
--   Let $Q$ be a primitive string (nonempty and not a power $U^e$ with $e\ge2$) and $Q^s$ the concatenation of $s$ copies of $Q$.
--
--   **Definition 7.3 ($Q$-decomposition).** A decomposition $S=\bigodot_{j=0}^{t}S_j$ of a string $S$ is a **$Q$-decomposition** when
--   - $S_0=Q[i..|Q|)\,Q^{s_0}$ for some $i\in[0..|Q|]$ and $s_0\ge0$;
--   - $S_j=Q^{s_j}$, $s_j\ge0$, for every even $j\in(0..t)$;
--   - $S_j$ is nonempty for every odd $j\in(0..t)$;
--   - $S_t=Q^{s_t}\,Q[0..\ell)$ for some $\ell\in[0..|Q|)$ and $s_t\ge0$.
--
--   The factor $S_i$ occupies $S[a_i..b_i)$ with $a_i=|S_0|+\dots+|S_{i-1}|$ and $b_i=a_i+|S_i|$.
--
--   **Definition 7.4 ($d$-far).** Strings $X=\bigodot_{i=0}^{t}X_i$ and $Y=\bigodot_{j=0}^{r}Y_j$ are **$d$-far** with respect to these decompositions when for all odd $i\in(0..t)$ and odd $j\in(0..r)$,
--   $$[a_i-12d\,..\,b_i+12d)\cap[a'_j..b'_j)=\emptyset,\qquad X_i=X[a_i..b_i),\ Y_j=Y[a'_j..b'_j).$$
--   The odd factors are the "clutter"; far-ness says the clutter of $X$ and of $Y$ is separated by at least $12d$ positions.
--
--   **The shift.** For a string $X$ and $q\ge0$, $X'=X[q..|X|)\odot X[|X|-q..|X|)$: $X$ moved left by $q$ positions, with its last $q$ characters repeated.
--
--   These notions are the hypotheses and the conclusion of Lemmas 7.5, 7.8 and Claim 7.9, which justify moving all clutter of $X$ by one period.
--
--   **Formalization Note.** A decomposition is the nonempty list $[S_0,\dots,S_t]$ of its factors, $t$ being the list length minus one; $j\in(0..t)$ means $0<j<t$. Intervals in Definition 7.4 are integer intervals, so $a_i-12d$ may be negative. Primitivity of $Q$ is a hypothesis of each lemma rather than part of the definition.
-- source:
--   Charalampopoulos, Ellert, Radoszewski, Dynamic Approximate Text Indexing, STOC 2027 submission (manuscript sha256 7f902057…), Definitions 7.3 and 7.4, p. 30 (PDF 32); Lemmas 7.5 and 7.8, pp. 30, 32 (PDF 32, 34)

import Mathlib
import Definitions.Def_PMEdits_Main_Strings

namespace DynApproxIdx.Main

open PMEdits.Main

/-! # Q-decompositions, d-far strings and the shift by one period

Charalampopoulos, Ellert, Radoszewski, *Dynamic Approximate Text Indexing*, STOC 2027 submission
(manuscript sha256 7f902057…): Definitions 7.3 and 7.4, p. 30 (PDF 32); the string `X′` of
Lemmas 7.5 and 7.8, pp. 30, 32 (PDF 32, 34).

**Formalization Note.** A decomposition `S = S_0 S_1 ⋯ S_t` is the list `[S_0, …, S_t]` of its
factors (a nonempty list whose concatenation is `S`, `t = length − 1`). The start of `S_i` in `S`
is `a_i = |S_0| + ⋯ + |S_{i−1}|` and its end `b_i = a_i + |S_i|`, so `S_i = S[a_i..b_i)`. Odd and
even indices are the paper's; `j ∈ (0..t)` means `0 < j < t`. The primitivity of `Q` is a
hypothesis of the lemmas that use these notions. -/

/-- `Q^s`, the concatenation of `s` copies of `Q`. -/
def qpow (Q : List ℕ) (s : ℕ) : List ℕ := (List.replicate s Q).flatten

/-- Definition 7.3: `S = ⊙_{j=0}^t S_j` (the list `Ss`) is a `Q`-decomposition of `S`:
`S_0 = Q[i..|Q|) Q^{s_0}` with `i ∈ [0..|Q|]`, `s_0 ≥ 0`; `S_j = Q^{s_j}` for even `j ∈ (0..t)`;
`S_j` nonempty for odd `j ∈ (0..t)`; `S_t = Q^{s_t} Q[0..ℓ)` with `ℓ ∈ [0..|Q|)`, `s_t ≥ 0`. -/
def IsQDecomp (Q S : List ℕ) (Ss : List (List ℕ)) : Prop :=
  Ss ≠ [] ∧ Ss.flatten = S ∧
  (∃ i s : ℕ, i ≤ Q.length ∧ Ss.head? = some (frag Q i Q.length ++ qpow Q s)) ∧
  (∀ (j : ℕ) (hj : j < Ss.length), 0 < j → j + 1 < Ss.length → Even j →
    ∃ s : ℕ, Ss[j] = qpow Q s) ∧
  (∀ (j : ℕ) (hj : j < Ss.length), 0 < j → j + 1 < Ss.length → Odd j → Ss[j] ≠ []) ∧
  (∃ ℓ s : ℕ, ℓ < Q.length ∧ Ss.getLast? = some (qpow Q s ++ frag Q 0 ℓ))

/-- The start `a_i = |S_0| + ⋯ + |S_{i−1}|` of the factor `S_i` of a decomposition. -/
def startPos (Ss : List (List ℕ)) (i : ℕ) : ℕ := ((Ss.take i).map List.length).sum

/-- The end `b_i = a_i + |S_i|` of the factor `S_i` of a decomposition. -/
def endPos (Ss : List (List ℕ)) (i : ℕ) : ℕ := startPos Ss (i + 1)

/-- Definition 7.4: `X = ⊙_{i=0}^t X_i` and `Y = ⊙_{j=0}^r Y_j` are `d`-far with respect to these
decompositions: for all odd `i ∈ (0..t)` and odd `j ∈ (0..r)`, the integer intervals
`[a_i − 12d .. b_i + 12d)` and `[a′_j .. b′_j)` are disjoint, where `X_i = X[a_i..b_i)` and
`Y_j = Y[a′_j..b′_j)`. -/
def IsFar (d : ℕ) (Xs Ys : List (List ℕ)) : Prop :=
  ∀ i j : ℕ, 0 < i → i + 1 < Xs.length → Odd i → 0 < j → j + 1 < Ys.length → Odd j →
    ∀ x : ℤ, ¬ ((startPos Xs i : ℤ) - 12 * (d : ℤ) ≤ x ∧ x < (endPos Xs i : ℤ) + 12 * (d : ℤ) ∧
      (startPos Ys j : ℤ) ≤ x ∧ x < (endPos Ys j : ℤ))

/-- `X′ = X[q..|X|) ⊙ X[|X| − q..|X|)`: `X` shifted left by `q`, with its last `q` characters
appended again (Lemmas 7.5 and 7.8). -/
def shiftQ (X : List ℕ) (q : ℕ) : List ℕ := frag X q X.length ++ frag X (X.length - q) X.length

end DynApproxIdx.Main


