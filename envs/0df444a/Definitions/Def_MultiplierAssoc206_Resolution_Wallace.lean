-- Prove2me | Definitions.Def_MultiplierAssoc206_Resolution_Wallace
-- name    : MultiplierAssoc206_Resolution_Wallace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:18:36.455878+00:00
-- url     : https://prove2.me/theorems/16f3abaa-6e98-45cd-a394-cc7d62d41732
-- title:
--   The Wallace-tree multiplier with a final carry-lookahead adder
-- statement:
--   **Wallace tree (Definition A.2).** Layer $\ell$ consists of subcolumns $\mathrm{Col}(\ell,i)$, ordered lists of layer variables $t_{\ell,i,j}$ of weight $2^i$ (row $j$ is the position in the list). Layer $0$ holds the partial products, $t_{0,i,j}=x_{i-j}\wedge y_j$ for $i<n$ and $t_{0,i,j}=x_{n-1-j}\wedge y_{i-n+j+1}$ for $i\ge n$. Layer $\ell+1$ is built from layer $\ell$ by partitioning the rows into sets of three, from top to bottom: adder $A_{\ell,i,J}$ takes the variables of column $i$ in rows $3J,3J+1,3J+2$ (nonexistent ones replaced by $0$) and outputs $s=a_0\oplus a_1\oplus a_2$ and $c=\mathrm{MAJ}(a_0,a_1,a_2)$. For each set of rows $J=0,1,\dots$ and each column $i$ in increasing order, the sum bit of $A_{\ell,i,J}$ is appended to $\mathrm{Col}(\ell+1,i)$ and its carry bit to $\mathrm{Col}(\ell+1,i+1)$. An adder with one constant input is a half adder; an adder with two constant inputs acts as a wire and contributes only its sum bit. The tree stops at the first layer $\ell_{\max}$ with at most two rows.
--
--   **Carry-lookahead adder (Definition A.1).** The two rows $X,Y$ of layer $\ell_{\max}$ (missing entries $0$) are summed by a $4^L$-bit carry-lookahead adder, $4^L$ the least power of $4$ with $4^L\ge2n$, inputs above column $2n-1$ being $0$. Its wires are: the bitwise signals $p_i=X_i\oplus Y_i$, $q_i=X_iY_i$; the group pairs at every level $1\le\ell\le L$, including the root pair, $p^\ell_a=\prod_{t<4}p^{\ell-1}_{a+t4^{\ell-1}}$ and $q^\ell_a=q_3\oplus q_2p_3\oplus q_1p_2p_3\oplus q_0p_1p_2p_3$ of the level-$\ell$ sub-adder on $[a,a+4^\ell)$ (with $(p^0_i,q^0_i)=(p_i,q_i)$); the carries $c_i$ for $1\le i\le4^L$ (including the final carry-out), where for $i=a+r4^\ell$ with $4^{\ell+1}\mid a$, $1\le r\le3$, the carry is computed from $c_a$ and the level-$\ell$ pairs at $a,a+4^\ell,\dots,a+(r-1)4^\ell$ by the unrolled recurrence $c_{t+1}=q_t\oplus p_tc_t$, with $c_0=0$; and the sum bits $(X+Y)_i=p_i\oplus c_i$, for all $i<4^L$, of which the bits with $i<2n$ are the multiplier outputs.
--
--   Every gate has fan-in at most eight, so the clauses of the encoding have constant width.
--
--   **Formalization Note** The order in which adder outputs are appended, the absence of adders with no variable input, the rule that a pass-through adder emits no carry, and the padding of the adder to width $4^L$ are readings of Definitions A.1 and A.2; with them each layer reduces $N$ rows to $\lceil 2N/3\rceil$, as the definition states. Layer variables in columns at or above $4^L$ are not fed to the adder; they are always $0$ because the weighted sum of every layer is the product.
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF pp.26–28 (printed pp.25–27), Definitions A.1, A.2 and Figures 9, 10 (PDF pp.26–29)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_ArrayMultiplier

namespace MultiplierAssoc206.Resolution

/-! # The Wallace-tree multiplier with a final carry-lookahead adder

Liew, *Associativity of Multiplication Is Hard for Resolution*, Definitions A.1 and A.2
(PDF pp. 26–28). Layer `ℓ` of the Wallace tree is a family of subcolumns `Col(ℓ, i)`, each an
ordered list of layer variables `t_{ℓ,i,j}` (row `j` = position in the list). Layer `0` holds the
partial products; layer `ℓ + 1` is made by adders `A_{ℓ,i,J}` acting on rows `3J, 3J+1, 3J+2` of
column `i`. The last layer has at most two rows, which a `4^L`-bit carry-lookahead adder sums
(`4^L ≥ 2n`, the inputs above column `2n − 1` being constant `0`). -/

/-- Names of the wires of the Wallace-tree multiplier. -/
inductive WallaceName where
  /-- the partial product `x_a ∧ y_b` -/
  | pp (a b : ℕ)
  /-- the sum bit of adder `A_{ℓ,i,J}` -/
  | sum (l i J : ℕ)
  /-- the carry bit of adder `A_{ℓ,i,J}` -/
  | carry (l i J : ℕ)
  /-- the CLA propagate signal `p_i = x_i ⊕ y_i` -/
  | p (i : ℕ)
  /-- the CLA generate signal `q_i = x_i y_i` -/
  | q (i : ℕ)
  /-- the CLA group propagate `p^ℓ_a` of the level-`ℓ` sub-adder on `[a, a + 4^ℓ)`, `ℓ ≥ 1` -/
  | gp (l a : ℕ)
  /-- the CLA group generate `q^ℓ_a` of the level-`ℓ` sub-adder on `[a, a + 4^ℓ)`, `ℓ ≥ 1` -/
  | gq (l a : ℕ)
  /-- the CLA carry `c_i` into column `i`, `i ≥ 1` -/
  | c (i : ℕ)
  /-- the CLA sum bit `(x + y)_i` -/
  | s (i : ℕ)
  deriving DecidableEq

namespace Wallace

/-- `Col(0, i)`: `t_{0,i,j} = x_{i−j} ∧ y_j` for `i < n` and
`t_{0,i,j} = x_{n−1−j} ∧ y_{i−n+j+1}` for `i ≥ n` (Definition A.2). -/
def col0 (n i : ℕ) : List WallaceName :=
  if i < n then (List.range (i + 1)).map fun j => .pp (i - j) j
  else if i < 2 * n - 1 then (List.range (2 * n - 1 - i)).map fun j => .pp (n - 1 - j) (i - n + j + 1)
  else []

/-- The `J`-th set of three rows of a subcolumn (rows `3J, 3J+1, 3J+2` that exist). -/
def group (col : List WallaceName) (J : ℕ) : List WallaceName := (col.drop (3 * J)).take 3

/-- `Col(ℓ+1, i)` from layer `ℓ`: for each set of rows `J = 0, 1, …` (and each column, in
increasing order) the adder `A_{ℓ,i,J}` appends its sum bit to `Col(ℓ+1, i)` and the adder
`A_{ℓ,i−1,J}` its carry bit. An adder exists when its group has a variable; an adder with two
constant inputs acts as a wire (sum bit only, no carry). -/
def next (l : ℕ) (cols : ℕ → List WallaceName) (i : ℕ) : List WallaceName :=
  (List.range ((cols i).length + (if i = 0 then 0 else (cols (i - 1)).length))).flatMap fun J =>
    (if i ≠ 0 ∧ 2 ≤ (group (cols (i - 1)) J).length then [WallaceName.carry l (i - 1) J] else []) ++
    (if 1 ≤ (group (cols i) J).length then [WallaceName.sum l i J] else [])

/-- The subcolumns `Col(ℓ, i)` of layer `ℓ`. -/
def layer (n : ℕ) : ℕ → ℕ → List WallaceName
  | 0 => col0 n
  | l + 1 => next l (layer n l)

/-- The number of rows of layer `ℓ` (its columns lie below `2n + ℓ`). -/
def height (n l : ℕ) : ℕ := ((List.range (2 * n + l)).map fun i => (layer n l i).length).foldl max 0

/-- `ℓ_max`: the first layer with at most two rows. -/
def lmax (n : ℕ) : ℕ := ((List.range (n + 1)).find? fun l => height n l ≤ 2).getD n

/-- The number of levels `L` of the carry-lookahead adder: `4^L` is the least power of `4` that
is at least `2n`. -/
def claLevels (n : ℕ) : ℕ := Nat.clog 4 (2 * n)

/-- The CLA width `4^L`. -/
def claWidth (n : ℕ) : ℕ := 4 ^ claLevels n

/-- The CLA summands: row `0` (`r = 0`) and row `1` (`r = 1`) of column `i` of the last layer;
`none` (the constant `0`) when that variable does not exist. -/
def claIn (n r i : ℕ) : Option WallaceName :=
  if i < 2 * n then (layer n (lmax n) i)[r]? else none

/-- The level-`ℓ` propagate wire on `[a, a + 4^ℓ)`: `p_a` at level `0`, `p^ℓ_a` above. -/
def P (l a : ℕ) : WallaceName := if l = 0 then .p a else .gp l a

/-- The level-`ℓ` generate wire on `[a, a + 4^ℓ)`: `q_a` at level `0`, `q^ℓ_a` above. -/
def Q (l a : ℕ) : WallaceName := if l = 0 then .q a else .gq l a

/-- The largest `ℓ` with `4^ℓ ∣ i` (for `i ≥ 1`). -/
def v4 (i : ℕ) : ℕ := Nat.factorization i 2 / 2

/-- The carry recurrence `c' = q ⊕ (p ∧ c)` folded from the carry-in `c` over the pairs
`(q_t, p_t)`; unrolled, it is the parallel carry formula of Definition A.1. -/
def carryFold (c : Bool) (qs ps : List Bool) : Bool :=
  (List.zip qs ps).foldl (fun c qp => xor qp.1 (qp.2 && c)) c

/-- All wire names of the `n`-bit Wallace-tree multiplier, including the root group pair,
the final carry-out, and the padded adder's high sum bits (Definition A.1). -/
def names (n : ℕ) : List WallaceName :=
  ((List.range n).flatMap fun a => (List.range n).map fun b => WallaceName.pp a b) ++
  ((List.range (lmax n + 1)).flatMap fun l =>
      (List.range (2 * n + lmax n)).flatMap fun i => if l = 0 then [] else layer n l i) ++
  ((List.range (claWidth n)).flatMap fun i => [WallaceName.p i, WallaceName.q i]) ++
  ((List.range (claLevels n + 1)).flatMap fun l =>
      if l = 0 then []
      else (List.range (claWidth n / 4 ^ l)).flatMap fun t =>
        [WallaceName.gp l (t * 4 ^ l), WallaceName.gq l (t * 4 ^ l)]) ++
  ((List.range (claWidth n + 1)).flatMap fun i => if i = 0 then [] else [WallaceName.c i]) ++
  ((List.range (claWidth n)).map WallaceName.s)

/-- The wires: the names of `names n`. -/
abbrev WWire (n : ℕ) := {w : WallaceName // w ∈ (names n).toFinset}

/-- A wire name as a gate input: the wire itself, or the constant `0` if it is not a wire. -/
def src (n : ℕ) (w : WallaceName) : Option (MulVar (WWire n) n) :=
  if h : w ∈ (names n).toFinset then some (.wire ⟨w, h⟩) else none

/-- The ordered inputs of each gate. -/
def ins (n : ℕ) : WallaceName → List (Option (MulVar (WWire n) n))
  | .pp a b =>
      [if h : a < n then some (.x ⟨a, h⟩) else none, if h : b < n then some (.y ⟨b, h⟩) else none]
  | .sum l i J => (group (layer n l i) J).map (src n)
  | .carry l i J => (group (layer n l i) J).map (src n)
  | .p i => [(claIn n 0 i).bind (src n), (claIn n 1 i).bind (src n)]
  | .q i => [(claIn n 0 i).bind (src n), (claIn n 1 i).bind (src n)]
  | .gp l a => (List.range 4).map fun t => src n (P (l - 1) (a + t * 4 ^ (l - 1)))
  | .gq l a =>
      ((List.range 4).map fun t => src n (Q (l - 1) (a + t * 4 ^ (l - 1)))) ++
      ((List.range 4).map fun t => src n (P (l - 1) (a + t * 4 ^ (l - 1))))
  | .c i =>
      let l := v4 i
      let r := (i / 4 ^ l) % 4
      let a := i - r * 4 ^ l
      [if a = 0 then none else src n (.c a)] ++
      ((List.range r).map fun t => src n (Q l (a + t * 4 ^ l))) ++
      ((List.range r).map fun t => src n (P l (a + t * 4 ^ l)))
  | .s i => [src n (.p i), if i = 0 then none else src n (.c i)]

/-- The Boolean function of each gate. -/
def op : WallaceName → List Bool → Bool
  | .pp _ _ => fun l => l.all id
  | .sum _ _ _ => xorList
  | .carry _ _ _ => majList
  | .p _ => xorList
  | .q _ => fun l => l.all id
  | .gp _ _ => fun l => l.all id
  | .gq _ _ => fun l => carryFold false (l.take 4) (l.drop 4)
  | .c i => fun l =>
      let r := (i / 4 ^ v4 i) % 4
      carryFold (l.headD false) ((l.drop 1).take r) ((l.drop (1 + r)).take r)
  | .s _ => xorList

theorem s_mem (n : ℕ) (k : Fin (2 * n)) : WallaceName.s k ∈ (names n).toFinset := by
  have hk : (k : ℕ) < claWidth n :=
    lt_of_lt_of_le k.2 (Nat.le_pow_clog (by decide : 1 < 4) (2 * n))
  simp [names, hk]

end Wallace

open Wallace in
/-- Definition A.2 with Definition A.1: the standard `n`-bit Wallace-tree multiplier whose final
two rows are summed by a carry-lookahead adder, as a gate circuit. Output bit `k` is the CLA sum
bit `(x + y)_k = p_k ⊕ c_k`. -/
def wallaceCircuit (n : ℕ) : GateCircuit n where
  W := WWire n
  ins := fun w => Wallace.ins n w.1
  op := fun w => Wallace.op w.1
  out := fun k => ⟨.s k, s_mem n k⟩

/-- The Wallace-tree multiplier encodings, one for each bit-width `n` (Definition A.2). -/
noncomputable def wallaceMultiplier (n : ℕ) : MulEncoding n := (wallaceCircuit n).toEncoding

end MultiplierAssoc206.Resolution


