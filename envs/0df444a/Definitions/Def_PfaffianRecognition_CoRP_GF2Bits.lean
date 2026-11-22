-- Prove2me | Definitions.Def_PfaffianRecognition_CoRP_GF2Bits
-- name    : PfaffianRecognition_CoRP_GF2Bits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-22T21:16:24.396971+00:00
-- url     : https://prove2.me/theorems/d151ddb2-3ddd-4d5b-bb9a-8c5426e39a2d
-- title:
--   Bit-list arithmetic in $\mathbb F_2[z]/(z^{2m}+z^m+1)$
-- statement:
--   Let $h_m(z)=z^{2m}+z^m+1\in\mathbb F_2[z]$ and $K_m=\mathbb F_2[z]/(h_m)$. An element is stored as a list of $2m$ bits $b_0,\dots,b_{2m-1}$, denoting
--   $$\textstyle\sum_{i<2m} b_i z^i\in K_m .$$
--   Addition is the bitwise exclusive or. Since $z^{3m}-1=(z^m-1)h_m(z)$, the root satisfies $z^{3m}=1$ and $z^e=z^{e-m}+z^{e-2m}$ for $2m\le e<3m$; multiplication therefore reduces each exponent $j+l$ modulo $3m$ and folds the top third down, so coefficient $i$ of a product is the parity of the number of pairs $(j,l)$ with $a_j=b_l=1$ and $(j+l)\bmod 3m\in\{i,\,i+2m\}$ (for $i<m$) or $\{i,\,i+m\}$ (for $i\ge m$). The inverse is computed as $a^{2^{2m}-2}$ by $2m-1$ squarings, and the zero test checks that all bits vanish.
--
--   For $m=3^k$ the trinomial $h_m$ is the cyclotomic polynomial $\Phi_{3^{k+1}}$, irreducible over $\mathbb F_2$, so $K_m$ is the field with $2^{2m}$ elements. This supplies the characteristic-two field $\mathbb F_q$ of the source's orientation test, constructed explicitly instead of by searching for an irreducible polynomial.
--
--   **Formalization Note** The decoding map into `AdjoinRoot` reads missing bits as $0$ and ignores bits beyond position $2m-1$.
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf, §3.1 proof of Theorem 3.2 (p. 7): field F_q of characteristic two with q ≥ 4n, here realized as F_2[z]/(Φ_{3^{k+1}})

import Mathlib
import Definitions.Def_PfaffianRecognition_CoRP_ListLinAlg

/-!
Bit-list arithmetic in `𝔽₂[z]/(z^{2m} + z^m + 1)`.

An element is a list of `2m` bits `b₀, …, b_{2m-1}` standing for `Σ bᵢ zⁱ`. Because
`z^{3m} - 1 = (z^m - 1)(z^{2m} + z^m + 1)`, the root satisfies `z^{3m} = 1` and
`z^{e} = z^{e-m} + z^{e-2m}` for `2m ≤ e < 3m`; multiplication reduces exponents modulo `3m` and then
folds the top third down. For `m = 3^k` the modulus is the cyclotomic polynomial `Φ_{3^{k+1}}`, which is
irreducible over `𝔽₂`, so the quotient is the field with `2^{2m}` elements.
-/

namespace PfaffianRecognition.CoRP

open Polynomial

/-- The trinomial `z^{2m} + z^m + 1` over `𝔽₂`. -/
noncomputable def gfPoly (m : ℕ) : (ZMod 2)[X] := X ^ (2 * m) + X ^ m + 1

/-- The quotient ring `𝔽₂[z]/(z^{2m} + z^m + 1)` (a field when the trinomial is irreducible). -/
abbrev GF (m : ℕ) := AdjoinRoot (gfPoly m)

/-- The value `Σ_{i < 2m} bᵢ zⁱ` of a bit list (missing bits read as `false`, bits beyond `2m`
are ignored). -/
noncomputable def gfDecode (m : ℕ) (a : List Bool) : GF m :=
  ∑ i ∈ Finset.range (2 * m), if a.getD i false then AdjoinRoot.root (gfPoly m) ^ i else 0

def gfZero (m : ℕ) : List Bool := (List.range (2 * m)).map (fun _ => false)

def gfOne (m : ℕ) : List Bool := (List.range (2 * m)).map (fun i => decide (i = 0))

def gfAdd (m : ℕ) (a b : List Bool) : List Bool :=
  (List.range (2 * m)).map (fun i => xor (a.getD i false) (b.getD i false))

/-- Index pairs `(j, l)` with `j, l < 2m`. -/
def gfIndexPairs (m : ℕ) : List (ℕ × ℕ) :=
  (List.range (2 * m)).flatMap (fun j => (List.range (2 * m)).map (fun l => (j, l)))

/-- Coefficient `i` of the product: the parity of the number of pairs `(j, l)` with `aⱼ = b_l = 1`
whose exponent `e = (j + l) mod 3m` contributes to `zⁱ`, namely `e = i`, or `e = i + 2m` (if `i < m`),
or `e = i + m` (if `m ≤ i`). -/
def gfMul (m : ℕ) (a b : List Bool) : List Bool :=
  (List.range (2 * m)).map (fun i =>
    (((gfIndexPairs m).filter (fun jl => a.getD jl.1 false && b.getD jl.2 false &&
      ((jl.1 + jl.2) % (3 * m) == i ||
        (jl.1 + jl.2) % (3 * m) == (if i < m then i + 2 * m else i + m)))).length % 2 == 1))

/-- Inverse by Fermat: `a^{2^{2m} - 2} = ∏_{i=1}^{2m-1} a^{2^i}`, by `2m - 1` squarings. -/
def gfInv (m : ℕ) (a : List Bool) : List Bool :=
  ((List.range (2 * m - 1)).foldl
    (fun st _ => (gfMul m st.1 st.1, gfMul m st.2 (gfMul m st.1 st.1))) (a, gfOne m)).2

def gfIsZero (m : ℕ) (a : List Bool) : Bool :=
  (List.range (2 * m)).all (fun i => !a.getD i false)

/-- The bit-list field operations (negation is the identity in characteristic two). -/
def gfOps (m : ℕ) : FieldOps (List Bool) where
  zero := gfZero m
  one := gfOne m
  add := gfAdd m
  neg := id
  mul := gfMul m
  inv := gfInv m
  isZero := gfIsZero m

end PfaffianRecognition.CoRP


