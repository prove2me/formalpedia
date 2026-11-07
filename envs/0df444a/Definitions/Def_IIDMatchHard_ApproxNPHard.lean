-- Prove2me | Definitions.Def_IIDMatchHard_ApproxNPHard
-- name    : IIDMatchHard_ApproxNPHard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:28.693709+00:00
-- url     : https://prove2.me/theorems/dff26c5a-6da7-4c7c-a05c-342c784c159a
-- title:
--   NP-hardness of approximating a real-valued function within a factor $1\pm\varepsilon$
-- statement:
--   Let $F$ assign a real number to every input in a domain $\mathcal D$, with inputs written as binary strings by an encoding $\mathrm{enc}$. **Approximating $F$ within a factor $1\pm\varepsilon$ on $\mathcal D$ is NP-hard** if every language $L$ in NP, over any finite nonempty alphabet, reduces as follows. There are
--
--   1. a polynomial-time instance map $x\mapsto f(x)$ with $f(x)\in\mathcal D$, computed on the encoding $\mathrm{enc}(f(x))$;
--   2. a polynomial-time answer map $g$ that reads $x$ and a rational number $q$,
--
--   such that for every string $x$ and **every** rational $q$ with
--   $$|q-F(f(x))|\le\varepsilon\,F(f(x)),$$
--   the answer map accepts, outputting $[\mathrm{true}]$, exactly when $x\in L$.
--
--   In words: an algorithm that returns some number $\bar V$ with $|\bar V-F(I)|\le\varepsilon F(I)$, the task of §2, can be used once to decide any NP language.
--
--   **Formalization Note** Turing machines, polynomial time and NP are those of `CookPvsNP` (Cook's Clay problem description). The answer map reads $x$, a separator, and the binary code of $q$. This one-query reduction is the reduction carried out in App. B.9, and it implies hardness under polynomial-time oracle reductions.
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), §2, p.4 (PDF p.5) (the approximation task); Theorem 3.1, p.5; App. B.9, p.23

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ImpatientMatching_Input

set_option autoImplicit false

namespace IIDMatchHard

/-- The input of the answer map of a reduction: the original string `x` over `Sym`, a separator,
and the binary code `encRat q` of the rational answer `q` returned for the constructed instance.
The separator is `none`; `some (inl a)` is a symbol of `x`, `some (inr b)` a bit of `encRat q`. -/
def pairInput {Sym : Type} (x : List Sym) (q : ℚ) : List (Option (Sym ⊕ Bool)) :=
  x.map (some ∘ Sum.inl) ++ none :: (ImpatientMatching.encRat q).map (some ∘ Sum.inr)

/-- **Approximating `F` within a factor `1 ± ε` on the inputs satisfying `Dom` is NP-hard**:
for every language `L` in NP over any finite nonempty alphabet there are a polynomial-time
instance map `f` (with values in `Dom`, measured on the encoding `enc`) and a polynomial-time
answer map `g` such that for every string `x` and **every** rational `q` with
`|q − F(f x)| ≤ ε·F(f x)`, the map `g`, reading `x` and `q`, outputs `[true]` exactly when
`x ∈ L`. Teng, Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of
Nov. 3, 2026, sha256 f0193d92…), §2, p.4 (PDF p.5) (the approximation task "find a number V̄ with
|V̄ − OPT(I)| ≤ εOPT(I)") and Theorem 3.1, p.5.

**Formalization Note.** "NP-hard" is read as a polynomial-time reduction from every NP language
that queries an approximation **once** and post-processes the answer, the reduction carried out
in the proof of Theorem 3.1 (App. B.9, p.23). It implies hardness under polynomial-time oracle
(Cook) reductions. Correctness is required for every admissible rational answer. Machines,
`NP` and polynomial time are Cook's (`CookPvsNP`). -/
def ApproxNPHard {α : Type} (enc : α → List Bool) (Dom : α → Prop) (F : α → ℝ) (ε : ℝ) :
    Prop :=
  ∀ (Sym : Type) [Fintype Sym] [Nonempty Sym] (L : CookPvsNP.Lang Sym), L ∈ CookPvsNP.NP Sym →
    ∃ (f : List Sym → α) (g : List (Option (Sym ⊕ Bool)) → List Bool),
      CookPvsNP.PolyTimeComputable (fun x => enc (f x)) ∧
      CookPvsNP.PolyTimeComputable g ∧
      (∀ x, Dom (f x)) ∧
      ∀ (x : List Sym) (q : ℚ), |(q : ℝ) - F (f x)| ≤ ε * F (f x) →
        (g (pairInput x q) = [true] ↔ x ∈ L)

end IIDMatchHard


