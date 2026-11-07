-- Prove2me | Definitions.Def_ImplicitParityWL_Address
-- name    : ImplicitParityWL_Address
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:09:04.069656+00:00
-- url     : https://prove2.me/theorems/83bb690c-6087-4778-938d-23418754f780
-- title:
--   Coordinates, the code $C$ and addresses
-- statement:
--   Fix $k$ and $\ell$. The coordinate set is $\mathfrak c=[k]\times\mathbb F_2^\ell$, consisting of $k$ blocks. For $x\in\mathbb F_2^{\mathfrak c}$, $\mathrm{supp}(x)=\{(i,b)\mid x_{i,b}=1\}$. The **code** $C$ consists of the vectors $x$ such that
--
--   1. all block restrictions of $x$ have the same parity, and $x$ is called block-odd or **block-even** accordingly;
--   2. the sum of the block coordinates $b$ over the coordinates $(i,b)$ with $x_{i,b}=1$ is zero in $\mathbb F_2^\ell$.
--
--   An **address** is a codeword with exactly one $1$ per block. Equivalently it is an array $a=(a_1,\dots,a_k)\in(\mathbb F_2^\ell)^k$ with $a_1+\dots+a_k=0$, where $a_{i,b}=1$ if and only if $b=a_i$, and then $\mathrm{supp}(a)=\{(i,a_i)\mid i\in[k]\}$. A seed $z$ assigns to an address the parity $a\cdot z$ of its selected coordinates.
--
--   Addresses index the variables of an implicit parity system: $k2^\ell$ coordinates support $2^{\ell(k-1)}$ addresses.
--
--   **Formalization Note** The primary form of an address is the array; `Address.word` gives the indicator vector. Blocks are `Fin k`, so the first block is the index $0$. A seed is a total function on $\mathfrak c$.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), §4.2, pp.18–19; eq. (9), p.21

import Mathlib

namespace ImplicitParityWL

/-- Block coordinates `𝔽₂^ℓ`. -/
abbrev BlockCoord (ℓ : ℕ) := Fin ℓ → ZMod 2

/-- The coordinate set `𝔠 = [k] × 𝔽₂^ℓ` of `k` blocks (Curticapean, Liu, Neuen, Seppelt, *Lower
Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3,
2026, §4.2, p.18).

**Formalization Note** Blocks are `Fin k`, so the page's block `i` is the index `i - 1` and the
"first block" is the index `0`. -/
abbrev Coord (k ℓ : ℕ) := Fin k × BlockCoord ℓ

/-- Binary vectors `x ∈ 𝔽₂^𝔠`, which also serve as seeds. -/
abbrev Word (k ℓ : ℕ) := Coord k ℓ → ZMod 2

variable {k ℓ : ℕ}

/-- `supp(x) = {(i, b) | x_{i,b} = 1}` (§4.2, p.18). -/
def Word.supp (x : Word k ℓ) : Finset (Coord k ℓ) := Finset.univ.filter (fun c => x c = 1)

/-- The parity of the restriction of `x` to the block `i`. -/
def Word.blockParity (x : Word k ℓ) (i : Fin k) : ZMod 2 := ∑ b : BlockCoord ℓ, x (i, b)

/-- The inner product `x · z = ∑_c x_c z_c`. -/
def Word.dot (x z : Word k ℓ) : ZMod 2 := ∑ c : Coord k ℓ, x c * z c

/-- Membership in the code `C ⊆ 𝔽₂^𝔠` (§4.2, p.18): (a) all block restrictions have the same parity;
(b) the sum of the block coordinates `b` over the coordinates `(i, b)` with `x_{i,b} = 1` is `0`. -/
structure Word.InCode (x : Word k ℓ) : Prop where
  parity : ∀ i j : Fin k, x.blockParity i = x.blockParity j
  checksum : ∑ c : Coord k ℓ, x c • c.2 = 0

/-- `x` is a **block-even** codeword: a codeword all of whose block restrictions have even parity
(§4.2, p.18). -/
def Word.IsBlockEven (x : Word k ℓ) : Prop := x.InCode ∧ ∀ i : Fin k, x.blockParity i = 0

/-- An **address** in its array representation `a = (a₁, …, a_k) ∈ (𝔽₂^ℓ)^k` with
`a₁ + ⋯ + a_k = 0` (§4.2, p.19); `a.1 i` is the block coordinate of the unique `1` in block `i`.

**Formalization Note** The page defines `Σ` as the codewords with exactly one `1` per block and
states the equivalence of the two representations; `Address.word` is the map to the indicator
representation. -/
abbrev Address (k ℓ : ℕ) := {a : Fin k → BlockCoord ℓ // ∑ i, a i = 0}

/-- The codeword of an address: `a_{i,b} = 1` if and only if `b = a_i` (§4.2, p.19). -/
def Address.word (a : Address k ℓ) : Word k ℓ := fun c => if c.2 = a.1 c.1 then 1 else 0

/-- `supp(a) = {(i, a_i) | i ∈ [k]}` (§4.2, p.19). -/
def Address.supp (a : Address k ℓ) : Finset (Coord k ℓ) :=
  Finset.univ.image (fun i : Fin k => (i, a.1 i))

/-- The value `a · z` of a seed `z` on the address `a`, eq. (9), §4.4, p.21: the sum of `z` over
`supp(a)`. -/
def Address.dot (a : Address k ℓ) (z : Word k ℓ) : ZMod 2 := ∑ c ∈ a.supp, z c

end ImplicitParityWL


