-- Prove2me | Definitions.Def_MultiplierAssoc206_Resolution_Multiplier
-- name    : MultiplierAssoc206_Resolution_Multiplier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:11:33.591942+00:00
-- url     : https://prove2.me/theorems/d05a4c4e-e3ef-497e-ae4c-5ab49c5d4a25
-- title:
--   Exact and strip-local multiplier encodings, partial products, $g$-strips and $g$-sparse restrictions
-- statement:
--   Bit-vectors are little-endian: $x=(x_0,\dots,x_{n-1})\in\{0,1\}^n$ represents $\sum_{i<n}x_i2^i$.
--
--   **Exact multiplier encoding (Definition 2.3).** A multiplier encoding $\mathrm{Mul}_n(x,y;xy)$ is a CNF over the bits of the $n$-bit inputs $x,y$ and auxiliary variables called wires, where every wire $w$ carries a Boolean function $f_w(x,y)$ of the input bits and $2n$ designated wires form the output $xy$. It is **exact** when the satisfying assignments of the CNF are exactly the assignments in which every wire takes the value $f_w(x,y)$, and output wire $k$ computes bit $k$ of the product of the two input integers.
--
--   **Partial products (Definition 2.4).** $t_{i,j}=x_i\wedge y_j$ for $0\le i,j<n$; it lies in column $i+j$.
--
--   **Strips and sparse restrictions (Definitions 4.1, 4.2).** For an integer $g\ge1$ the $g$-strip with base $bg$ is the interval of columns $[bg,(b+1)g)$, and a $g$-column is a multiple of $g$. A restriction of the input bit-vectors (each bit set to $0$, set to $1$, or left unset) is **$g$-sparse** if every partial product not forced to $0$ (that is, neither of whose factors $x_i,y_j$ is set to $0$) lies in a $g$-column, and each $g$-column contains strictly fewer than $2^{g-1}$ such partial products.
--
--   **Strip-local (Definition 4.3).** A family $(\mathrm{Mul}_n)_{n\ge0}$ of encodings is **strip-local** if every member is exact, one constant bounds the width of every clause of every member, and for every $n$, every $g\ge1$ and every $g$-sparse restriction of the inputs of $\mathrm{Mul}_n$, every wire is a Boolean function of the partial products belonging to a single strip: there is a base $b$ such that any two input assignments consistent with the restriction that agree on the partial products of columns $[bg,(b+1)g)$ give the wire the same value.
--
--   The lower bound of the mission applies to every strip-local family.
--
--   **Formalization Note** A family is a function from the bit-width $n$ to encodings; its wire type may depend on $n$. The strip may depend on $n$, $g$, the restriction and the wire.
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF pp.5–7 (printed pp.4–6), §2 Notation, Definitions 2.3, 2.4 (PDF p.5), Definitions 4.1–4.3 (PDF p.7)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF

namespace MultiplierAssoc206.Resolution

open Classical

/-! # Exact and strip-local multiplier encodings

Liew, *Associativity of Multiplication Is Hard for Resolution*, §2 Notation, Definitions 2.3
and 2.4 (PDF p. 5), Definitions 4.1–4.3 (PDF p. 7). Bit-vectors are little-endian:
`x : Fin n → Bool` represents `∑_{i<n} x_i 2^i`. -/

/-- The integer represented by a little-endian bit-vector. -/
def bitsVal {n : ℕ} (x : Fin n → Bool) : ℕ := ∑ i : Fin n, if x i then 2 ^ (i : ℕ) else 0

/-- The variables of a multiplier encoding with `n`-bit inputs and wire type `W`: the input
bits `x_i`, `y_i` (`i < n`) and the wires. -/
inductive MulVar (W : Type) (n : ℕ) where
  | x (i : Fin n) : MulVar W n
  | y (i : Fin n) : MulVar W n
  | wire (w : W) : MulVar W n

/-- A multiplier encoding with `n`-bit inputs (Definition 2.3, data part): a CNF over the
input bits and the wires, the Boolean function of the inputs attached to each wire, and the
`2n` designated output wires. -/
structure MulEncoding (n : ℕ) where
  /-- The auxiliary variables (wires). -/
  W : Type
  /-- The clauses of the encoding. -/
  cnf : CNF (MulVar W n)
  /-- The Boolean function of the inputs `(x, y)` computed by each wire. -/
  fn : W → (Fin n → Bool) → (Fin n → Bool) → Bool
  /-- The designated output `xy`: output bit `k` is the wire `out k`. -/
  out : Fin (2 * n) → W

/-- Definition 2.3 (Exact multiplier encoding). The satisfying assignments of the CNF are
exactly the assignments in which every wire takes the value of its function of the input
bits, and the output wire `k` computes bit `k` of the product of the two input integers. -/
def MulEncoding.IsExact {n : ℕ} (M : MulEncoding n) : Prop :=
  (∀ a : MulVar M.W n → Bool,
      CNFSat a M.cnf ↔
        ∀ w : M.W, a (.wire w) = M.fn w (fun i => a (.x i)) (fun i => a (.y i))) ∧
  ∀ (x y : Fin n → Bool) (k : Fin (2 * n)),
      M.fn (M.out k) x y = Nat.testBit (bitsVal x * bitsVal y) k

/-- Definition 2.4: the partial product `t_{i,j} = x_i ∧ y_j`; it lies in column `i + j`. -/
def partialProduct {n : ℕ} (x y : Fin n → Bool) (i j : Fin n) : Bool := x i && y j

/-- A restriction of the two input bit-vectors `x` and `y` of a multiplier. -/
abbrev InputRestr (n : ℕ) := (Fin n → Option Bool) × (Fin n → Option Bool)

/-- The partial product `t_{i,j}` is forced to `0` by `r` when `r` sets `x_i` or `y_j` to `0`. -/
def ForcedZero {n : ℕ} (r : InputRestr n) (i j : Fin n) : Prop :=
  r.1 i = some false ∨ r.2 j = some false

/-- The partial products not forced to `0` that lie in column `c`. -/
noncomputable def freeInColumn {n : ℕ} (r : InputRestr n) (c : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => ¬ ForcedZero r p.1 p.2 ∧ (p.1 : ℕ) + p.2 = c

/-- Definition 4.2 (g-sparse restriction). Every partial product not forced to `0` lies in a
`g`-column (a multiple of `g`), and each `g`-column contains strictly fewer than `2^(g-1)`
such partial products. -/
def IsGSparse {n : ℕ} (g : ℕ) (r : InputRestr n) : Prop :=
  (∀ i j : Fin n, ¬ ForcedZero r i j → g ∣ (i : ℕ) + j) ∧
  ∀ c : ℕ, g ∣ c → (freeInColumn r c).card < 2 ^ (g - 1)

/-- An assignment `(x, y)` of the input bits is consistent with the input restriction `r`. -/
def ConsistentInputs {n : ℕ} (r : InputRestr n) (x y : Fin n → Bool) : Prop :=
  (∀ i b, r.1 i = some b → x i = b) ∧ (∀ j b, r.2 j = some b → y j = b)

/-- Definition 4.1: column `c` belongs to the `g`-strip with base `b g`, the interval of
columns `[b g, (b+1) g)`. -/
def InStrip (g b c : ℕ) : Prop := b * g ≤ c ∧ c < (b + 1) * g

/-- Under the input restriction `r`, the wire `w` is a Boolean function of the partial
products belonging to the `g`-strip with base `b g`: any two input assignments consistent with
`r` that agree on those partial products give the wire the same value. -/
def WireOfStrip {n : ℕ} (M : MulEncoding n) (r : InputRestr n) (g b : ℕ) (w : M.W) : Prop :=
  ∀ x y x' y', ConsistentInputs r x y → ConsistentInputs r x' y' →
    (∀ i j : Fin n, InStrip g b ((i : ℕ) + j) →
      partialProduct x y i j = partialProduct x' y' i j) →
    M.fn w x y = M.fn w x' y'

/-- Definition 4.3 (Strip-local), for a family `Mul n` of encodings, one for each bit-width
`n`: every member is exact, one constant bounds the width of every clause of every member, and
for every `g ≥ 1`, every `n` and every `g`-sparse restriction of the input bit-vectors of
`Mul n`, every wire is a Boolean function of the partial products of a single strip. -/
def StripLocal (Mul : (n : ℕ) → MulEncoding n) : Prop :=
  (∀ n, (Mul n).IsExact) ∧
  (∃ w₀ : ℕ, ∀ n, cnfWidth (Mul n).cnf ≤ w₀) ∧
  ∀ (n g : ℕ), 1 ≤ g → ∀ r : InputRestr n, IsGSparse g r →
    ∀ w : (Mul n).W, ∃ b : ℕ, WireOfStrip (Mul n) r g b w

/-- The number of partial products in column `c` that evaluate to `1` under `(x, y)`. -/
noncomputable def columnCount {n : ℕ} (x y : Fin n → Bool) (c : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n =>
      (p.1 : ℕ) + p.2 = c ∧ partialProduct x y p.1 p.2 = true).card

end MultiplierAssoc206.Resolution


