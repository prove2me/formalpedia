-- Prove2me | Definitions.Def_KarpLiptonOM_OGTD
-- name    : KarpLiptonOM_OGTD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:42.410326+00:00
-- url     : https://prove2.me/theorems/73fe130d-3e46-4cea-8f9d-f949ef10a482
-- title:
--   $\mathrm{OGTD}[\mathrm{FP}^X, \mathcal B, \mathrm P]$: generator–tester–decoder computations (Definition A.2.10)
-- statement:
--   Let $X$ be a class of promise problems and $\mathcal B$ a class of languages of pairs (testers). A language $L$ belongs to $\mathrm{OGTD}[\mathrm{FP}^X, \mathcal B, \mathrm P]$ if there are
--
--   1. a **generator**: a deterministic polynomial-time oracle transducer $G$ with an oracle $\Pi \in X$, whose output on $1^n$ has length $p(n)$ for a polynomial $p$;
--   2. a **tester** $T \in \mathcal B$, a language of pairs $(1^n, a)$;
--   3. a **decoder** $D \in \mathrm P$, a language of pairs $(x, a)$,
--
--   such that for every $n$
--   $$
--   \mathrm{Out}_G(n) \subseteq \mathrm{Acc}_T(n) \subseteq \mathrm{Good}_D(n), \tag{A.1}
--   $$
--   where $\mathrm{Out}_G(n) = \{G^O(1^n) : O \text{ consistent with } \Pi\}$ are the legal outputs, $\mathrm{Acc}_T(n) = \{a : (1^n, a) \in T\}$ the accepted advice strings, and $\mathrm{Good}_D(n) = \{a \in \{0,1\}^{p(n)} : D(x, a) = L(x) \text{ for all } x \in \{0,1\}^n\}$ the good advice strings.
--
--   The generator computes advice from $1^n$ alone; the tester checks it without seeing the input; the decoder uses it to decide $L$ on all inputs of length $n$.
--
--   **Formalization Note** With $\mathcal B$ the class of all languages ($*$), only $\mathrm{Out}_G(n) \subseteq \mathrm{Good}_D(n)$ matters; this is $\mathrm{OGTD}[X] = \mathrm{OGTD}[\mathrm{FP}^X, *, \mathrm P]$, and $\mathrm{OGTD}[\Pi]$ is the case $X = \{\Pi\}$. A class of languages enters as the promise problems $(A, \overline A)$.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Definition A.2.10, pp.23–24

import Mathlib
import Definitions.Def_KarpLiptonOM_PromiseProblem
import Definitions.Def_KarpLiptonOM_Consistent
import Definitions.Def_KarpLiptonOM_OracleTM_IsPolyTime
import Definitions.Def_KarpLiptonOM_OracleTM_out
import Definitions.Def_KarpLiptonOM_PolyPred2
import Definitions.Def_KarpLiptonOM_tupleEnc

namespace KarpLiptonOM

/-- `OGTD[FP^X, B, P]` (Definition A.2.10, Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), pp.23–24), for a class `X` of promise problems (the
generator's oracles) and a class `B` of testers: `L` belongs to it if there are `Π ∈ X`, a
deterministic polynomial-time oracle transducer `G` whose output on `1ⁿ` has length `p(n)` with every
`O` consistent with `Π`, a tester `T ∈ B` (a language of pairs `(1ⁿ, a)`) and a polynomial-time decoder
`D` (pairs `(x, a)`) with `Out_G(n) ⊆ Acc_T(n) ⊆ Good_D(n)` for every `n` (A.1), where
`Out_G(n) = {G^O(1ⁿ) : O consistent with Π}`, `Acc_T(n) = {a : (1ⁿ, a) ∈ T}` and
`Good_D(n) = {a ∈ {0,1}^{p(n)} : D(x, a) = L(x) for all x ∈ {0,1}ⁿ}`.

**Formalization Note** `OGTD X Set.univ` is `OGTD[X] = OGTD[FP^X, ∗, P]` (no test); `OGTD {Π} Set.univ`
is `OGTD[Π]`, and `OGTD (toPromise '' C) Set.univ` is `OGTD[C]` for a class `C` of languages. -/
def OGTD (X : Set PromiseProblem) (B : Set (List Bool → List Bool → Prop)) :
    Set (Set (List Bool)) :=
  {L | ∃ PP ∈ X, ∃ (G : OracleTM) (k : ℕ) (p : Polynomial ℕ), G.IsPolyTime k ∧
    (∀ O, Consistent O PP → ∀ n : ℕ,
      (G.out O k (tupleEnc [List.replicate n true])).length = p.eval n) ∧
    ∃ T ∈ B, ∃ D : List Bool → List Bool → Prop, PolyPred2 D ∧ ∀ n : ℕ,
      (∀ O, Consistent O PP →
        T (List.replicate n true) (G.out O k (tupleEnc [List.replicate n true]))) ∧
      (∀ a, T (List.replicate n true) a →
        a.length = p.eval n ∧ ∀ x : List Bool, x.length = n → (D x a ↔ x ∈ L))}

end KarpLiptonOM


