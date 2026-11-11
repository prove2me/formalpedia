-- Prove2me | Definitions.Def_AaronsonAmbainis_Short
-- name    : AaronsonAmbainis_Short
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T04:17:44.514533+00:00
-- url     : https://prove2.me/theorems/76b78719-a0de-42dc-b479-010e99882209
-- title:
--   Decision trees of bounded depth on the Boolean cube
-- statement:
--   `Short.DTree n h` holds when the function $h$ on $\{0,1\}^\iota$ is computed by a deterministic decision tree making at most $n$ queries on every input: $h$ is constant, or $h(x)=h_{x_i}(x)$ for a coordinate $i$ and functions $h_0,h_1$ computed by trees of depth at most $n-1$.
-- source:
--   Huffstutler, Miloschewsky and Podder, A short proof of the Aaronson-Ambainis Conjecture via the completion framework, arXiv:2611.12795, Section 2.

import Definitions.Def_AaronsonAmbainis_Defs

/-!
# Decision trees on the Boolean cube

`Short.DTree n h` says that `h` is computed by a deterministic decision tree
of depth at most `n`: a tree either outputs a constant or queries one
coordinate and continues with a subtree chosen by the answer.
-/

namespace AaronsonAmbainis
namespace Short

/-- `DTree n h`: the function `h` on the cube is computed by a decision tree
making at most `n` queries on every input. -/
inductive DTree {ι : Type*} {α : Type*} : ℕ → (Cube ι → α) → Prop
  | const (n : ℕ) (c : α) : DTree n (fun _ => c)
  | query (n : ℕ) (i : ι) (h0 h1 : Cube ι → α) :
      DTree n h0 → DTree n h1 → DTree (n + 1) (fun x => if x i then h1 x else h0 x)

end Short
end AaronsonAmbainis


