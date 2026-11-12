-- Prove2me | Definitions.Def_ReLUWitness_Refuter_Standard
-- name    : ReLUWitness_Refuter_Standard
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T06:54:42.696254+00:00
-- url     : https://prove2.me/theorems/a35c09bf-95a8-4601-88a8-844a22da4ef6
-- title:
--   Standard model, the real function of a network code, MAX_n, and the conclusion of Lemma A.2 for a polynomial p₀
-- statement:
--   The **standard model** has numbers $\mathbb N$ and strings the finite subsets of $\mathbb N$, with $|X|=1+\max X$ (or $0$), and every primitive has its intended meaning (binary values $\sum_{i\in X}2^i$). In it, a valid network code $N$ (that is, $\mathrm{Net}(N,n)$ in the standard model) computes the function $N:\mathbb R^n\to\mathbb R$ obtained by applying the affine maps $y_i=\sum_tW_j[i,t]x_t+\eta_j[i]$ of layers $1,\dots,k+1$ in order, with $\mathrm{ReLU}(t)=\max(0,t)$ at the hidden layers $1,\dots,k$ and no ReLU at the output layer. Here $W_j[i,t]$ and $\eta_j[i]$ are the rational values $a/b$ of the record entries; the sign of a signed code is bit $0$ and magnitude bit $i$ sits at $i+1$. $\mathrm{MAX}_n(x)=\max_{1\le i\le n}x_i$. A vector code $x$ denotes the rational point whose coordinate $i$ is the value of entry $i$.
--
--   For a polynomial $p_0$ with nonnegative integer coefficients, the property $\mathrm{ShortRationalDisagreement}(p_0)$ is the conclusion of Lemma A.2: for every $n$ and every code $N$ with $\mathrm{Net}(N,n)$, if $N(z)\ne\mathrm{MAX}_n(z)$ for some $z\in\mathbb R^n$, then some valid rational $n$-vector $x$ has $|x|\le p_0(|N|)$ and $N(x)\ne\mathrm{MAX}_n(x)$.
--
--   **Formalization Note.** Real inputs are functions $z:\mathbb N\to\mathbb R$ whose coordinates $0,\dots,n-1$ are $x_1,\dots,x_n$; the network reads only those. The standard structure leaves the symbols of programs uninterpreted, and only the primitives are used here.
-- source:
--   Myrisiotis, A Witnessing Duality for ReLU Network Depth, arXiv:2610.38281v1, p. 12 (standard model), p. 19 (network function), p. 21 (MAX_n, p₀), p. 66 (Lemma A.2)

import Mathlib
import Definitions.Def_ReLUWitness_Refuter_Network

open scoped Classical

namespace ReLUWitness.Refuter

/-! The standard model (numbers `ℕ`, strings finite subsets of `ℕ`, every symbol with its
intended meaning, §2 p. 12), the real-valued function `x ↦ N(x)` of a network code (§2.3,
p. 19), `MAX_n`, and the conclusion of Lemma A.2 for a given polynomial `p₀` (p. 66)
(Myrisiotis, arXiv:2610.38281v1). -/

noncomputable section

/-- Length of a string: one more than its largest element, zero when empty. -/
def lenF (X : Finset ℕ) : ℕ := X.sup (· + 1)

/-- The pairing `⟨u,v⟩ = (u+v)(u+v+1)+2v`. -/
def pairN (u v : ℕ) : ℕ := (u + v) * (u + v + 1) + 2 * v

/-- Binary value of a string (bit `i` is the coefficient of `2^i`). -/
def toNatF (X : Finset ℕ) : ℕ := ∑ i ∈ X, 2 ^ i

/-- Binary string of a natural number. -/
def ofNatF (n : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter (fun i => n.testBit i)

/-- Row `a` of `X`: `X[a](i) ↔ i < |X| ∧ X(⟨a,i⟩)`. -/
def rowF (a : ℕ) (X : Finset ℕ) : Finset ℕ := (Finset.range (lenF X)).filter (fun i => pairN a i ∈ X)

/-- Intended meaning of the string-valued primitives. -/
def stdS : Sym → List ℕ → List (Finset ℕ) → Finset ℕ
  | .prim .row, [a], [X] => rowF a X
  | .prim .add, [], [X, Y] => ofNatF (toNatF X + toNatF Y)
  | .prim .sub, [], [X, Y] => ofNatF (toNatF X - toNatF Y)
  | .prim .cut, [b], [X] => X.filter (· < b)
  | .prim .shl, [k], [X] => X.image (· + k)
  | .prim .isum, [b], [X] => ofNatF (∑ a ∈ Finset.range b, toNatF (rowF a X))
  | .prim .mul, [], [X, Y] => ofNatF (toNatF X * toNatF Y)
  | .prim .imul, [i, j], [X] => ofNatF (∏ a ∈ Finset.Ico i j, toNatF (rowF a X))
  | .prim .div, [], [A, B] => ofNatF (toNatF A / toNatF B)
  | .prim .md, [], [A, B] => if toNatF B = 0 then ∅ else ofNatF (toNatF A % toNatF B)
  | .prim .mag, [], [u] => (u.filter (· ≠ 0)).image (· - 1)
  | .prim .sgnd, [s], [X] => (if s = 1 ∧ X.Nonempty then {0} else ∅) ∪ X.image (· + 1)
  | _, _, _ => ∅

/-- Intended meaning of the number-valued primitive (the counting function). -/
def stdN : Sym → List ℕ → List (Finset ℕ) → ℕ
  | .prim .numones, [y], [X] => (X.filter (· < y)).card
  | _, _, _ => 0

/-- The standard structure (chosen definitions of programs are not interpreted here; only the
primitives are used below). -/
def Std : Structure where
  N := ℕ
  S := Finset ℕ
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  le := (· ≤ ·)
  len := lenF
  mem := fun i X => i ∈ X
  nfun := stdN
  sfun := stdS

/-- Integer value of a canonical signed code: sign bit `0`, magnitude bit `i` at `i+1`. -/
def intOfF (u : Finset ℕ) : ℤ :=
  (if 0 ∈ u then -1 else 1) * ((∑ i ∈ u.filter (· ≠ 0), 2 ^ (i - 1) : ℕ) : ℤ)

/-- Rational value `a/b` of a rational pair `(a,b)` (tuple rows one and two). -/
def ratOfF (P : Finset ℕ) : ℚ := (intOfF (rowF 1 P) : ℚ) / (intOfF (rowF 2 P) : ℚ)

/-- Recorded hidden depth of a code. -/
def stdDepth (N : Finset ℕ) : ℕ := lenF (rowF 3 (rowF 1 N))

/-- `d_j`: `n` at `j = 0`, the `j`-th recorded dimension otherwise. -/
def stdDim (N : Finset ℕ) (n j : ℕ) : ℕ := if j = 0 then n else lenF (rowF j (rowF 2 (rowF 1 N)))

/-- Offsets `O_1 = 0`, `O_{j+1} = O_j + d_j d_{j-1} + d_j`. -/
def stdOff (N : Finset ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | j + 2 => stdOff N n (j + 1) + stdDim N n (j + 1) * stdDim N n j + stdDim N n (j + 1)

/-- Weight `W_j[i,t]` (zero-based `i`, `t`), entry `O_j + i d_{j-1} + t + 1` of `Par`. -/
def stdW (N : Finset ℕ) (n j i t : ℕ) : ℚ :=
  ratOfF (rowF (stdOff N n j + i * stdDim N n (j - 1) + t + 1) (rowF 2 N))

/-- Bias `η_j[i]` (zero-based `i`), entry `O_j + d_j d_{j-1} + i + 1` of `Par`. -/
def stdB (N : Finset ℕ) (n j i : ℕ) : ℚ :=
  ratOfF (rowF (stdOff N n j + stdDim N n j * stdDim N n (j - 1) + i + 1) (rowF 2 N))

/-- Values of layer `j` at the real input `z` (coordinate `x_{t+1}` is `z t`): affine maps in
order, ReLU at the hidden layers `1, …, k`, no ReLU at the output layer `k+1`. -/
def layerVal (N : Finset ℕ) (n : ℕ) (z : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => z
  | j + 1 => fun i =>
      if j + 1 ≤ stdDepth N then
        max 0 ((∑ t ∈ Finset.range (stdDim N n j), (stdW N n (j + 1) i t : ℝ) * layerVal N n z j t)
          + (stdB N n (j + 1) i : ℝ))
      else
        (∑ t ∈ Finset.range (stdDim N n j), (stdW N n (j + 1) i t : ℝ) * layerVal N n z j t)
          + (stdB N n (j + 1) i : ℝ)

/-- The function `N(x)` computed by a network code on `ℝ^n`. -/
def netReal (N : Finset ℕ) (n : ℕ) (z : ℕ → ℝ) : ℝ := layerVal N n z (stdDepth N + 1) 0

/-- `MAX_n(z) = max_{1 ≤ i ≤ n} z_i` (coordinate `z_i` is `z (i-1)`; `n ≥ 1`). -/
def realMax (n : ℕ) (z : ℕ → ℝ) : ℝ := ((List.range n).map z).foldr max (z 0)

/-- The rational point denoted by a vector code: coordinate `t` (zero-based) is entry `t+1`. -/
def ratPoint (x : Finset ℕ) : ℕ → ℝ := fun t => (ratOfF (rowF (t + 1) x) : ℝ)

/-- Conclusion of Lemma A.2 for `p₀`: every valid network code `N` that differs from `MAX_n`
somewhere on `ℝ^n` differs from it at a valid rational `n`-vector of code length at most
`p₀(|N|)`. -/
def ShortRationalDisagreement (p₀ : Polynomial ℕ) : Prop :=
  ∀ (n : ℕ) (N : Finset ℕ), Std.Net N n →
    (∃ z : ℕ → ℝ, netReal N n z ≠ realMax n z) →
    ∃ x : Finset ℕ, Std.ValidVec x n ∧ lenF x ≤ p₀.eval (lenF N) ∧
      netReal N n (ratPoint x) ≠ realMax n (ratPoint x)

end

end ReLUWitness.Refuter


