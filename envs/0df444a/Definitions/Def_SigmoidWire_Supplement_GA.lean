-- Prove2me | Definitions.Def_SigmoidWire_Supplement_GA
-- name    : SigmoidWire_Supplement_GA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:40:16.511498+00:00
-- url     : https://prove2.me/theorems/4423a464-5c0b-4cc7-a9ce-21cd0d4c40a7
-- title:
--   The generalized Andreev function $\mathrm{GA}_{n,m}$ (Kane–Williams), with $m=16\lceil\log_2 n\cdot\log_2\log_2 n\rceil$
-- statement:
--   Let $m=16\lceil\log_2 n\cdot\log_2\log_2 n\rceil$ and $\ell=m/2$. Fix an irreducible polynomial $P$ of degree $\ell$ over $\mathbb F_2$ and identify $\{0,1\}^\ell$ with the field $\mathbb F_{2^\ell}=\mathbb F_2[X]/(P)$ through coefficient vectors. For $x\in\{0,1\}^n$ and $z=(u,v)\in\mathbb F_{2^\ell}^2$ let
--   $$F(x,z)=\Big\langle \sum_{i=1}^n x_iu^{i-1},\,v\Big\rangle \bmod 2,$$
--   the inner product of the binary representations. For $x,y\in\{0,1\}^n$, with $y$ parsed into $m$ consecutive blocks $y_1,\dots,y_m$ of length $n/m$,
--   $$\mathrm{GA}_{n,m}(x,y)=F(x,z),\qquad z_i=\text{the parity of the bits of }y_i.$$
--
--   It is the hard function of the depth-three gate and wire lower bounds (Theorems 5.10 and 5.18).
--
--   **Formalization Note** The paper defines $\mathrm{GA}_{n,m}$ only when $m$ divides $n$, and the theorems using it are stated for such $n$. The irreducible polynomial is a parameter (the paper fixes one found deterministically by Shoup's algorithm). The input is $x$ followed by $y$; $u$ is $(z_1,\dots,z_\ell)$ and $v$ is $(z_{\ell+1},\dots,z_m)$; the coefficient of $X^j$ is bit $j$.
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), proof of Lemma 5.16 and the paragraph after it, p.27

import Mathlib

namespace SigmoidWire.Supplement

open Polynomial

/-- **The number of blocks `m = 16⌈log₂ n · log₂ log₂ n⌉`** of the generalized Andreev function.

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), p.27 (PDF p.29):
"Fix m := 16⌈log₂ n · log₂ log₂ n⌉." -/
noncomputable def gaM (n : ℕ) : ℕ :=
  16 * ⌈Real.logb 2 n * Real.logb 2 (Real.logb 2 n)⌉₊

/-- The element of `GF(2)[X]` with coefficient vector `u`: `Σ_{j<ℓ} u_j X^j`. Through an
irreducible `P` of degree `ℓ`, the residues of these polynomials are the elements of
`GF(2^ℓ) = GF(2)[X]/(P)`, and `u` is the binary representation of the element. -/
noncomputable def bitsPoly {ℓ : ℕ} (u : Fin ℓ → Bool) : (ZMod 2)[X] :=
  ∑ j : Fin ℓ, if u j then (X : (ZMod 2)[X]) ^ (j : ℕ) else 0

/-- **The function `F` of Lemma 5.16** (the powering construction), p.27 (PDF p.29): for
`x ∈ {0,1}^n` and `z = (u, v) ∈ GF(2^ℓ)²`, "F(x, z) := ⟨Σ_{i=1}^n x_i u^{i−1}, v⟩ mod 2, where ⟨·,·⟩
is the inner product of the binary representations", the field being `GF(2)[X]/(P)`.

**Formalization Note.** The sum `Σ_i x_i u^{i−1}` is computed in `GF(2)[X]` and reduced modulo
`P`; the binary representation of the result is its coefficient vector of length `ℓ = deg P`. The
paper's index `i ∈ {1, …, n}` is `i + 1` for `i : Fin n`. -/
noncomputable def andreevF (P : (ZMod 2)[X]) {n ℓ : ℕ} (x : Fin n → Bool) (u v : Fin ℓ → Bool) :
    Bool :=
  let q : (ZMod 2)[X] := (∑ i : Fin n, if x i then bitsPoly u ^ (i : ℕ) else 0) % P
  decide ((∑ j : Fin ℓ, if v j then q.coeff j else 0) = 1)

open Classical in
/-- **The generalized Andreev function `GA_{n,m}`**, p.27 (PDF p.29): "We will use the following
function GA_{n,m}(x, y) with n + (n/m)·m = 2n input variables, where x ∈ {0,1}^n and y ∈ {0,1}^n.
The string y is parsed as y_1, …, y_m ∈ {0,1}^{n/m}, and we define GA_{n,m}(x, y) := F(x, z), where
z_i := ⊕(y_i) is the parity of bits in y_i", with `m = gaM n`, `ℓ := m/2` and `F` the function of
Lemma 5.16 for the field `GF(2)[X]/(P)`.

An input is `w : Fin (n + n) → Bool`, `x_i = w i` and `y_k = w (n + k)`. With `b := n / m`, block
`i` of `y` (`i = 0, …, m − 1`) is `y_{ib}, …, y_{ib+b−1}`, so `z_i` is the parity of the `y_k` with
`k / b = i`; `u = (z_0, …, z_{ℓ−1})` and `v = (z_ℓ, …, z_{2ℓ−1})`.

**Formalization Note.** The paper defines `GA_{n,m}` only when `m` divides `n` ("we assume n/m is an
integer"), and the theorems using it are stated for such `n`; the formula is meaningful for every
`n` but only those `n` are used. The irreducible polynomial `P` of degree `ℓ` is a parameter (the
paper fixes one found by [Sho90]; its proofs use only the field structure). -/
noncomputable def GA (n : ℕ) (P : (ZMod 2)[X]) (w : Fin (n + n) → Bool) : Bool :=
  let m := gaM n
  let ℓ := m / 2
  let b := n / m
  let z : ℕ → Bool := fun i =>
    decide (Odd (Finset.univ.filter fun k : Fin n => k.val / b = i ∧ w (Fin.natAdd n k) = true).card)
  andreevF P (n := n) (ℓ := ℓ) (fun i => w (Fin.castAdd n i)) (fun j => z j) (fun j => z (ℓ + j))

end SigmoidWire.Supplement


