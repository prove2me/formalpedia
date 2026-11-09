-- Prove2me | Definitions.Def_TreeEquivalenceHORS_Equivalence_Encoding
-- name    : TreeEquivalenceHORS_Equivalence_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:59.804307+00:00
-- url     : https://prove2.me/theorems/8feafdd9-71a1-44c6-9368-9504b33727d8
-- title:
--   The constructor encoding $E$ of $\Sigma_0$-trees into $\Sigma_2$-trees
-- statement:
--   The final compiler pass replaces the intermediate constructors by fixed $\Sigma_2$-contexts (Equation (26)):
--   $$E(z)=e,\qquad E(a\,t)=d(e,E(t)),\qquad E(b(t_0,t_1,t_2))=d\bigl(d(e,e),\,d(E(t_0),\,d(E(t_1),E(t_2)))\bigr).$$
--   These guarded equations define $E$ on finite and infinite trees: the encoded child of $a$ sits at address $1$, the encoded children of $b$ at $10$, $110$, $111$.
--
--   **Formalization Note** Trees are label functions on addresses; `encAt T w` computes the label of $E(T)$ at $w$ by recursion on $w$. A $\bot$ root stays $\bot$ (productive inputs have none), and labels outside $\Sigma_0$ give absent nodes.
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Section 5.6, Equation (26), printed p. 20 / PDF p. 22; addresses printed p. 21 / PDF p. 23

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Semantics

namespace TreeEquivalenceHORS.Equivalence

/-! # The constructor encoding `E` of `Σ₀`-trees into `Σ₂`-trees (Section 5.6, Equation (26); PDF p. 22)

`E(z) = e`, `E(a t) = d(e, E(t))`,
`E(b(t₀, t₁, t₂)) = d(d(e, e), d(E(t₀), d(E(t₁), E(t₂))))`.
Trees are given by their labels at all finite addresses (`List ℕ → Lab`), so `E` applies to finite
and infinite trees. Labels: `Σ₀` has `z = term 0`, `a = term 1`, `b = term 2`; `Σ₂` has
`e = term 0`, `d = term 1`. -/

/-- `E(T)` at an address, by recursion on the address. A `⊥` node stays `⊥` (with absent children);
labels outside `Σ₀` and absent nodes give absent nodes. -/
def encAt (T : List ℕ → Lab) : List ℕ → Lab
  | [] =>
      match T [] with
      | .term 0 => .term 0
      | .term 1 => .term 1
      | .term 2 => .term 1
      | .bot => .bot
      | _ => .absent
  | i :: w =>
      match T [] with
      | .term 1 =>
          -- `E(a t) = d(e, E(t))`: child `0` is the leaf `e`, child `1` is `E(t)`.
          if i = 0 then (if w = [] then .term 0 else .absent)
          else if i = 1 then encAt (fun x => T (0 :: x)) w
          else .absent
      | .term 2 =>
          -- `E(b(t₀,t₁,t₂)) = d(d(e,e), d(E(t₀), d(E(t₁), E(t₂))))`.
          if i = 0 then
            (match w with
             | [] => .term 1
             | [j] => if j = 0 ∨ j = 1 then .term 0 else .absent
             | _ => .absent)
          else if i = 1 then
            (match w with
             | [] => .term 1
             | 0 :: w' => encAt (fun x => T (0 :: x)) w'
             | [1] => .term 1
             | 1 :: 0 :: w'' => encAt (fun x => T (1 :: x)) w''
             | 1 :: 1 :: w'' => encAt (fun x => T (2 :: x)) w''
             | _ => .absent)
          else .absent
      | _ => .absent

end TreeEquivalenceHORS.Equivalence


