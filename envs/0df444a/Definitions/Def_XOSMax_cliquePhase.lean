-- Prove2me | Definitions.Def_XOSMax_cliquePhase
-- name    : XOSMax_cliquePhase
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:26.270604+00:00
-- url     : https://prove2.me/theorems/f2b74c60-db42-4dc0-8036-73e51e74860c
-- title:
--   The while-loop of Algorithm 4 (Lines 1–6)
-- statement:
--   Lines 1–6 of Algorithm 4 read:
--
--   1. Let $R\leftarrow\emptyset$ and $\ell\leftarrow0$;
--   2. **while** $R\ne V$ **do**
--   3. let $\ell\leftarrow\ell+1$;
--   4. pick $v\in V\setminus R$ and let $V_\ell\leftarrow\{v\}$ and $R\leftarrow R+v$;
--   5. **foreach** $u\in V-v$ **do**
--   6. if $f(V_\ell+u)=f(V_\ell)+f(u)$ then let $V_\ell\leftarrow V_\ell+u$ and $R\leftarrow R\cup\{u\}$.
--
--   The program returns the list $V_1,\dots,V_\ell$.
--
--   It is a separate program so that Lemma 10 can state its output, and Algorithm 4 is built on it.
--
--   **Formalization Note** "Pick $v\in V\setminus R$" is the first element of $L$ outside $R$. Since $R$ only grows, the while-loop is one pass over $L$ that skips the elements of $R$. Each element costs a step for the membership test; each clique costs `growClique` and $n$ steps for updating $R$.
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Algorithm 4, Lines 1–6, p.7

import Mathlib
import Definitions.Def_XOSMax_OracleProg
import Definitions.Def_XOSMax_growClique

namespace XOSMax

open OracleProg

variable {E : Type} [DecidableEq E]

/-- One element of the pass of `cliquePhase`. The state is `(R, [V₁, …, V_ℓ])`. An element of `R` is
skipped. Otherwise it is the `v` picked in Line 4, its clique is grown, appended, and added to `R`.

**Formalization Note** Charges: one step for the test `v ∈ R`, the cost of `growClique`, and `n`
steps (`n` the length of `L`) for adding the new clique to `R` (the paper adds its elements one at a
time in Lines 4 and 6, at most `n` of them). -/
noncomputable def cliqueStep (L : List E) (st : Finset E × List (Finset E)) (v : E) :
    OracleProg E (Finset E × List (Finset E)) := do
  tick
  if v ∈ st.1 then
    pure st
  else
    let V' ← growClique L v
    ticks L.length
    pure (st.1 ∪ V', st.2 ++ [V'])

/-- Lines 1–6 of Algorithm 4: the while-loop, returning the list `V₁, …, V_ℓ`
(Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3, Algorithm 4, p.7).

**Formalization Note** The while-loop `while R ≠ V`, with "Pick `v ∈ V \ R`" the first element of `L`
outside `R`, is one pass over `L`: `R` only grows, so the position of the first element outside `R`
only moves forward, and the loop ends when the pass ends. -/
noncomputable def cliquePhase (L : List E) : OracleProg E (List (Finset E)) := do
  let st ← L.foldlM (cliqueStep L) (∅, [])
  pure st.2

end XOSMax


