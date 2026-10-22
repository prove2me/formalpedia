-- Prove2me | Definitions.Def_DynamicOnlineLP_LowerBound_HardInstance
-- name    : DynamicOnlineLP_LowerBound_HardInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T20:01:53.875978+00:00
-- url     : https://prove2.me/theorems/0c67bec7-0541-4a42-90da-dedb9aabd2cd
-- title:
--   The worst-case instance of §4: complementary demand vectors v_i, w_i from bit strings, with profits 4, 3, 2, 1
-- statement:
--   Fix integers $z\ge 1$ and $k\ge 0$ and put $m=2^z$ and $B=zk$ (so $B/z=k$). The $m$ **items** are indexed $j=0,\dots,2^z-1$, and item $j$ is identified with its $z$-bit binary string; $s_{ij}\in\{0,1\}$ is the $i$-th bit of $j$ ($i=0,\dots,z-1$, bit $0$ the least significant). For each $i$ the **demand vectors** $v_i,w_i\in\{0,1\}^m$ are
--
--   $$v_{ij}=s_{ij},\qquad w_{ij}=1-s_{ij}.$$
--
--   The two vectors of a pair are complementary and share no item, while any $z$ vectors consisting of exactly one of $v_i,w_i$ for each $i$ share the item whose bit string records the choices.
--
--   Given moreover a number $s\ge 0$ and numbers $q_i\le 2k$, the **constructed instance** has, for each pair $i$: $k$ inputs with profit coefficient $4$ and demand vector $v_i$; $q_i$ inputs with profit $3$ and demand vector $w_i$; $s$ inputs with profit $2$ and demand vector $w_i$; and $2k-q_i$ inputs with profit $1$ and demand vector $w_i$. Every item has capacity $B=zk$. For a solution $x$ (a number $x_c$ for each input $c$), $r_i(x)$ denotes the total amount $\sum x_c$ accepted over the inputs of pair $i$ with demand vector $w_i$.
--
--   In Agrawal, Wang and Ye's lower-bound construction $q_i$ is a Binomial$(2B/z,1/2)$ random variable and $s=\sqrt{B/4z}$; for every realization of the $q_i$ the instance is the deterministic one defined here.
--
--   **Formalization Note** Inputs are indexed by the finite type $\Sigma_{i<z}\ (\mathrm{Fin}\,k\oplus\mathrm{Fin}\,q_i\oplus\mathrm{Fin}\,s\oplus\mathrm{Fin}\,(2k-q_i))$; the four summands are the profit-4 ($v_i$), profit-3, profit-2 and profit-1 ($w_i$) inputs. Pairs are indexed from $0$ (the paper's $i=1,\dots,z$), bit $i$ being `Nat.testBit j i`, which matches the paper's Table 2 ($v_1$ is the lowest bit). The number $s$ of profit-2 inputs is a free parameter; the paper takes $s=\sqrt{B/4z}$, implicitly assumed to be an integer. $2k-q_i$ is natural-number subtraction, exact under $q_i\le 2k$, which every theorem using this file assumes.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, §4, p. 885 (construction and Table 2); p. 886, Claim 1 (r_i)

import Mathlib

namespace DynamicOnlineLP.LowerBound

/-- The demand vector `v_i ∈ {0,1}^m`, `m = 2^z`, of Agrawal–Wang–Ye 2014, §4 (p. 885): items are
indexed from `0` to `2^z - 1`, item `j` is identified with its `z`-bit binary string, and
`v_{ij} = s_{ij}` is the `i`-th bit of `j` (pairs indexed `i = 0, …, z-1`, bit `0` the lowest,
as in Table 2 where `v_1` is the lowest bit). -/
def vVec (z : ℕ) (i : Fin z) : Fin (2 ^ z) → ℝ :=
  fun j => if Nat.testBit j.val i.val then 1 else 0

/-- The complementary demand vector `w_{ij} = 1 - s_{ij}` (p. 885). -/
def wVec (z : ℕ) (i : Fin z) : Fin (2 ^ z) → ℝ :=
  fun j => 1 - vVec z i j

/-- The inputs of the constructed instance (§4, p. 885), with `B/z = k`: for each pair
`i = 0, …, z-1`,
* `k` inputs with profit coefficient 4 and demand vector `v_i` (`Sum.inl`),
* `q_i` inputs with profit 3 and demand vector `w_i`,
* `s` inputs with profit 2 and demand vector `w_i` (the paper takes `s = √(B/4z)`),
* `2k - q_i` inputs with profit 1 and demand vector `w_i`. -/
abbrev HardCol (z k s : ℕ) (q : Fin z → ℕ) : Type :=
  Σ i : Fin z, Fin k ⊕ Fin (q i) ⊕ Fin s ⊕ Fin (2 * k - q i)

/-- Profit coefficient of an input of the constructed instance: 4, 3, 2 or 1. -/
def hardProfit (z k s : ℕ) (q : Fin z → ℕ) : HardCol z k s q → ℝ
  | ⟨_, Sum.inl _⟩ => 4
  | ⟨_, Sum.inr (Sum.inl _)⟩ => 3
  | ⟨_, Sum.inr (Sum.inr (Sum.inl _))⟩ => 2
  | ⟨_, Sum.inr (Sum.inr (Sum.inr _))⟩ => 1

/-- Demand vector of an input of the constructed instance: `v_i` for the profit-4 inputs of pair
`i`, `w_i` for the others. -/
def hardDemand (z k s : ℕ) (q : Fin z → ℕ) : HardCol z k s q → Fin (2 ^ z) → ℝ
  | ⟨i, Sum.inl _⟩ => vVec z i
  | ⟨i, Sum.inr _⟩ => wVec z i

/-- The right-hand side of the constructed instance: `B = z k` units of each of the `m = 2^z`
items. -/
def hardCapacity (z k : ℕ) : Fin (2 ^ z) → ℝ :=
  fun _ => (z : ℝ) * (k : ℝ)

/-- `r_i(x)`, the (fractional) number of inputs with demand vector `w_i` accepted by the solution
`x` of the constructed instance: `∑` of `x_t` over the inputs of pair `i` of profit 3, 2 or 1. -/
def acceptedW {z k s : ℕ} {q : Fin z → ℕ} (x : HardCol z k s q → ℝ) (i : Fin z) : ℝ :=
  ∑ c : HardCol z k s q, if c.1 = i ∧ c.2.isRight then x c else 0

end DynamicOnlineLP.LowerBound


