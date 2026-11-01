-- Prove2me | Definitions.Def_XOSMax_alg3
-- name    : XOSMax_alg3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:35.704108+00:00
-- url     : https://prove2.me/theorems/edcf349c-a023-43a3-908d-ef41c4ce8622
-- title:
--   Algorithm 3: exact maximization of 2-XOS functions
-- statement:
--   Algorithm 3 of the paper, on the ground list $L$:
--
--   1. pick $v_1\in V$ and let $V_1\leftarrow\{v_1\}$;
--   2. for each $u\in V-v_1$: if $f(V_1+u)=f(V_1)+f(u)$ then let $V_1\leftarrow V_1+u$;
--   3. if $V_1=V$ then return $V_1$;
--   4. pick $v_2\in V\setminus V_1$ and let $V_2\leftarrow\{v_2\}$;
--   5. for each $u\in V-v_2$: if $f(V_2+u)=f(V_2)+f(u)$ then let $V_2\leftarrow V_2+u$;
--   6. let $Y_i\leftarrow V_i\cup\{v\in V\setminus V_i: f(V_i+v)>f(V_i)\}$ for $i=1,2$;
--   7. return $\tilde X\in\arg\max_{X\in\{Y_1,Y_2\}}f(X)$.
--
--   The program returns a record holding $V_1$, the triple $(V_2,Y_1,Y_2)$ when it is computed, and the output, so that Lemmas 8 and 9 can speak about them.
--
--   **Formalization Note** The picks are the head of $L$ and the first element of $L$ outside $V_1$. The absence of such an element is the test $V_1=V$ (charged $n$ steps). Ties in the last line go to $Y_1$. On the empty list, which the paper excludes, the program returns $\emptyset$.
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Algorithm 3, p.6

import Mathlib
import Definitions.Def_XOSMax_OracleProg
import Definitions.Def_XOSMax_growClique
import Definitions.Def_XOSMax_buildY

namespace XOSMax

open OracleProg

/-- What an execution of Algorithm 3 leaves behind: the set `V₁`, the triple `(V₂, Y₁, Y₂)` when
the algorithm goes past Line 4 and `none` when it returns there, and the output `X̃`. -/
structure Alg3Run (E : Type) where
  /-- The set `V₁` of Lines 1–3. -/
  V₁ : Finset E
  /-- `(V₂, Y₁, Y₂)`, computed unless `V₁ = V`. -/
  second : Option (Finset E × Finset E × Finset E)
  /-- The output `X̃`. -/
  output : Finset E

variable {E : Type} [DecidableEq E]

/-- **Algorithm 3**, the exact algorithm for 2-XOS maximization (Filmus, Kawase, Kobayashi &
Yamaguchi, arXiv:1811.09045v3, §2.3, p.6). The ground set is the list `L`.

Line 1 picks the head of `L`, Lines 2–3 are `growClique`. Lines 4–5 look for the first element `v₂`
of `L` outside `V₁`: if there is none then `V₁ = V`, and the algorithm returns `V₁`. Lines 6–7 are
`growClique`, Line 8 is `buildY` for `i = 1, 2`, and Line 9 returns the better of `Y₁, Y₂`, with
`Y₁` on ties.

**Formalization Note** The search of Lines 4–5 is charged `n` steps and the comparison of Line 9 one
step. On the empty list, which the paper excludes, the algorithm returns `∅`. -/
noncomputable def alg3 (L : List E) : OracleProg E (Alg3Run E) :=
  match L with
  | [] => pure ⟨∅, none, ∅⟩
  | v₁ :: rest => do
    let V₁ ← growClique (v₁ :: rest) v₁
    ticks (v₁ :: rest).length
    match (v₁ :: rest).find? (fun u => decide (u ∉ V₁)) with
    | none => pure ⟨V₁, none, V₁⟩
    | some v₂ =>
      let V₂ ← growClique (v₁ :: rest) v₂
      let Y₁ ← buildY (v₁ :: rest) V₁
      let Y₂ ← buildY (v₁ :: rest) V₂
      let a ← ask Y₁
      let b ← ask Y₂
      tick
      if a < b then
        pure ⟨V₁, some (V₂, Y₁, Y₂), Y₂⟩
      else
        pure ⟨V₁, some (V₂, Y₁, Y₂), Y₁⟩

end XOSMax


