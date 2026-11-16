-- Prove2me | Definitions.Def_InvariantMoneySecurity_Decomposition_Supplement_ConditionH
-- name    : InvariantMoneySecurity_Decomposition_Supplement_ConditionH
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:30:34.805347+00:00
-- url     : https://prove2.me/theorems/6fa926f4-7147-4775-be69-44853fbf6ffc
-- title:
--   Definitions 4.3 and 4.5 — coset parameterizations acting through the moves, condition (H)
-- statement:
--   Fix a seed $x$ and write $C:=C_{k(x)}$ for its orbit. A **coset parameterization** of $C$ at $x$ is a finite group $W$ of bit strings of polynomial length (the labels), with identity $1_W$, that acts on $C$, together with the map $\varphi_x(w)=w\cdot x$, which maps $W$ onto $C$; multiplication and inversion in $W$, the action of $W$ on $C$, and the preparation of the uniform superposition $|W\rangle$ to within negligible error are computable in polynomial time. It **acts through the moves** if for each move $s$ there is $g_s\in W$, computable in polynomial time from $s$, with
--   $$\varphi_x(g_s w)=s(\varphi_x(w))\qquad\text{for all }w\in W.$$
--
--   A family of seeds $G$ satisfies **condition (H)** if, for each $x\in G_n$, a coset parameterization $(W_x,\varphi_x)$ of $C_{k(x)}$ at $x$ that acts through the moves is computable in polynomial time from $x$.
--
--   Concretely the data are, for every $n$ and seed $x$: a label length $\ell(n)$ bounded by a polynomial; a finite set $W_x\subseteq\{0,1\}^{\ell(n)}$; a product, an inverse, an identity, an action $w\cdot y$ and elements $g_s$. At every $x\in G_n$ they satisfy the group laws on $W_x$ (closure, associativity, left identity, left inverse), the action laws on $C$ ($1\cdot y=y$, $(ww')\cdot y=w\cdot(w'\cdot y)$, $w\cdot y\in C$), the onto condition $\varphi_x(W_x)=C$, and the acting-through-the-moves identity. The product, the inverse, the action and $g_s$ are computed by polynomial-time classical functions from the unary $n$, the seed $x$ and the operands, and $|W_x\rangle$ can be prepared from $x$ to within negligible norm error in the pure-output sense of Definition 3.10.
--
--   **Formalization Note** Labels have one fixed length $\ell(n)$; variable-length labels of polynomial length are padded. The polynomial-time maps are the published classical Turing-machine notion, correct on valid operands. Exact preparation of $|W_x\rangle$ is not required.
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), p. 17, Definition 4.3; p. 18, Definition 4.5

import Definitions.Def_InvariantMoneySecurity_Decomposition_Supplement_Words
import Definitions.Def_InvariantMoneySecurity_Decomposition_Supplement_OrbitPreparation
set_option autoImplicit false
noncomputable section

namespace InvariantMoneySecurity.Decomposition.Supplement

open InvariantMoneySecurity.Decomposition

/-- Definitions 4.3 and 4.5: condition (H) for a seed family `G`.
For every seed `x ∈ G n`, the labels form a finite group `W_x ⊆ {0,1}^{ℓ(n)}` (with product
`mul`, inverse `inv`, identity `one`) acting on the orbit `C = C_{k(x)}` by `act`, with
`φ_x(w) = w · x` onto `C`, acting through the moves via `g_s = gen s`; the group operations, the
action and `g_s` are polynomial-time from `x` and the operands, and `|W_x⟩` can be prepared from
`x` to within negligible error (pure output with an `x`-dependent ancilla, as in Definition 3.10).
The laws are hypotheses on the data, imposed at every seed of `G`. -/
structure ConditionH (D : Scheme) (G : SeedFamily D) where
  labelBits : ℕ → ℕ
  labelBits_poly : ∃ q : Polynomial ℕ, ∀ n, labelBits n ≤ q.eval n
  carrier : ∀ n, (D.data n).Object → Finset (Bits (labelBits n))
  one : ∀ n, (D.data n).Object → Bits (labelBits n)
  mul : ∀ n, (D.data n).Object → Bits (labelBits n) → Bits (labelBits n) → Bits (labelBits n)
  inv : ∀ n, (D.data n).Object → Bits (labelBits n) → Bits (labelBits n)
  act : ∀ n, (D.data n).Object → Bits (labelBits n) → Bits n → Bits n
  gen : ∀ n, (D.data n).Object → Fin (D.data n).moveCount → Bits (labelBits n)
  one_mem : ∀ n, ∀ x ∈ G n, one n x ∈ carrier n x
  mul_mem : ∀ n, ∀ x ∈ G n, ∀ w ∈ carrier n x, ∀ w' ∈ carrier n x, mul n x w w' ∈ carrier n x
  inv_mem : ∀ n, ∀ x ∈ G n, ∀ w ∈ carrier n x, inv n x w ∈ carrier n x
  mul_assoc : ∀ n, ∀ x ∈ G n, ∀ a ∈ carrier n x, ∀ b ∈ carrier n x, ∀ c ∈ carrier n x,
    mul n x (mul n x a b) c = mul n x a (mul n x b c)
  one_mul : ∀ n, ∀ x ∈ G n, ∀ w ∈ carrier n x, mul n x (one n x) w = w
  inv_mul : ∀ n, ∀ x ∈ G n, ∀ w ∈ carrier n x, mul n x (inv n x w) w = one n x
  act_mem : ∀ n, ∀ x ∈ G n, ∀ w ∈ carrier n x, ∀ y ∈ (D.data n).orbit x,
    act n x w y ∈ (D.data n).orbit x
  one_act : ∀ n, ∀ x ∈ G n, ∀ y ∈ (D.data n).orbit x, act n x (one n x) y = y
  mul_act : ∀ n, ∀ x ∈ G n, ∀ w ∈ carrier n x, ∀ w' ∈ carrier n x, ∀ y ∈ (D.data n).orbit x,
    act n x (mul n x w w') y = act n x w (act n x w' y)
  orbit_onto : ∀ n, ∀ x ∈ G n, ∀ y ∈ (D.data n).orbit x, ∃ w ∈ carrier n x, act n x w x.val = y
  gen_mem : ∀ n, ∀ x ∈ G n, ∀ s, gen n x s ∈ carrier n x
  gen_act : ∀ n, ∀ x ∈ G n, ∀ s, ∀ w ∈ carrier n x,
    act n x (mul n x (gen n x s) w) x.val = moveBits (D.data n) s (act n x w x.val)
  mul_computable : ∃ f : List Bool → List Bool, QAlgorithms.Complexity.PolyTimeComputable f ∧
    ∀ n, ∀ x ∈ G n, ∀ w ∈ carrier n x, ∀ w' ∈ carrier n x,
      f (codeNat n ++ codeBits (List.ofFn x.val) ++ codeBits (List.ofFn w) ++
        codeBits (List.ofFn w')) = List.ofFn (mul n x w w')
  inv_computable : ∃ f : List Bool → List Bool, QAlgorithms.Complexity.PolyTimeComputable f ∧
    ∀ n, ∀ x ∈ G n, ∀ w ∈ carrier n x,
      f (codeNat n ++ codeBits (List.ofFn x.val) ++ codeBits (List.ofFn w)) =
        List.ofFn (inv n x w)
  act_computable : ∃ f : List Bool → List Bool, QAlgorithms.Complexity.PolyTimeComputable f ∧
    ∀ n, ∀ x ∈ G n, ∀ w ∈ carrier n x, ∀ y ∈ (D.data n).orbit x,
      f (codeNat n ++ codeBits (List.ofFn x.val) ++ codeBits (List.ofFn w) ++
        codeBits (List.ofFn y)) = List.ofFn (act n x w y)
  gen_computable : ∃ f : List Bool → List Bool, QAlgorithms.Complexity.PolyTimeComputable f ∧
    ∀ n, ∀ x ∈ G n, ∀ s,
      f (codeNat n ++ codeBits (List.ofFn x.val) ++ codeBits (List.ofFn (D.index n s))) =
        List.ofFn (gen n x s)
  uniform_preparable : PreparableFrom D G labelBits (fun n x => uniformVector (carrier n x))

end InvariantMoneySecurity.Decomposition.Supplement


