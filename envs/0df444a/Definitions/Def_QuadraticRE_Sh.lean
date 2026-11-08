-- Prove2me | Definitions.Def_QuadraticRE_Sh
-- name    : QuadraticRE_Sh
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:03:56.917655+00:00
-- url     : https://prove2.me/theorems/a4480b51-54b5-40bb-a60c-227c333ca0c8
-- title:
--   The recursive sharings $\mathrm{Sh}^j_A$ and $\mathrm{Sh}^j_C$
-- statement:
--   The one-level sharings are
--   $$\mathrm{Sh}_A(a;\theta)=(a+\theta,\,a+\theta,\,\theta,\,\theta),\qquad \mathrm{Sh}_C(c;\theta_1,\theta_2)=(c+\theta_1,\,\theta_1,\,c+\theta_2,\,\theta_2).$$
--   The depth-$j$ sharing $\mathrm{Sh}^j_X(s;\theta)$, $X\in\{A,C\}$, applies the one-level rule at the root and then recursively to each of the four children, with fresh masks at every internal node, for $j$ levels. Its $L=4^j$ coordinates are the leaves, listed by their sequence of child indices (the same order for $A$ and $C$). The sharing of $A$ uses $m=(L-1)/3$ masks, that of $C$ uses $2m$.
--
--   These are the two linear secret-sharing schemes whose corresponding leaf shares multiply to $ac$ in sum.
--
--   **Formalization Note** Leaves are numbered $0,\dots,L-1$: the base-4 digits of a leaf, most significant first, are its child indices. Internal nodes have heap indices (root $0$, child $\nu$ of node $n$ at $4n+1+\nu$), the breadth-first labels of Fig. 3; node $n$ of $A$ uses mask $n$, node $n$ of $C$ uses masks $2n$ and $2n+1$. Distinct nodes read distinct masks.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), §2.1.1, p.7; §4.1, p.16; Fig. 3, p.17

import Mathlib
import Definitions.Def_QuadraticRE_SD

namespace QuadraticRE

/-- The one-level sharing `ShA(a; θ) = (a + θ, a + θ, θ, θ)` of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), §4.1, p.16. -/
def shA (a θ : F2) : Fin 4 → F2 := ![a + θ, a + θ, θ, θ]

/-- The one-level sharing `ShC(c; θ₁, θ₂) = (c + θ₁, θ₁, c + θ₂, θ₂)`, p.16. -/
def shC (c θ₁ θ₂ : F2) : Fin 4 → F2 := ![c + θ₁, θ₁, c + θ₂, θ₂]

/-- The two sharing schemes `X ∈ {A, C}`. -/
inductive Scheme where
  | A : Scheme
  | C : Scheme

/-- One level of a recursive sharing at the internal node `n` holding the value `v`. The masks are
read from a table `θ`: node `n` of `A` uses `θ n`, node `n` of `C` uses `θ (2n)`, `θ (2n + 1)`. -/
def oneLevel : Scheme → (ℕ → F2) → ℕ → F2 → Fin 4 → F2
  | .A, θ, n, v => shA v (θ n)
  | .C, θ, n, v => shC v (θ (2 * n)) (θ (2 * n + 1))

/-- The value at leaf `i` of the depth-`j` subtree rooted at the internal node `n` holding `v`.
Leaf `i` lies in the child block `i / 4^(j-1)`, and within it has number `i % 4^(j-1)`.

**Formalization Note.** Internal nodes have heap indices (root `0`, child `ν` of `n` at
`4n + 1 + ν`), the breadth-first labels of Fig. 3, p.17. Distinct nodes have distinct indices, which
is "Every instantiation uses fresh independent masks", p.7. -/
def leafShare (X : Scheme) (θ : ℕ → F2) : (j n : ℕ) → (v : F2) → (i : ℕ) → F2
  | 0, _, v, _ => v
  | j + 1, n, v, i =>
    let ν : Fin 4 := Fin.ofNat 4 (i / 4 ^ j)
    leafShare X θ j (4 * n + 1 + ν) (oneLevel X θ n v ν) (i % 4 ^ j)

/-- `m = (L − 1)/3` with `L = 4^j`, p.16: the number of internal nodes, and of masks of `Sh^j_A`. -/
def mA (j : ℕ) : ℕ := (4 ^ j - 1) / 3

/-- The number of masks: `m` for `A`, `2m` for `C`, p.17. -/
def maskLen : Scheme → ℕ → ℕ
  | .A, j => mA j
  | .C, j => 2 * mA j

/-- Reads coordinate `n` of a bit vector. In-range reads are the only ones used (verification file);
the value `0` out of range never occurs. -/
def rd {ρ : ℕ} (R : Fin ρ → F2) (n : ℕ) : F2 :=
  if h : n < ρ then R ⟨n, h⟩ else 0

/-- The recursive sharing `Sh^j_X(s; θ)`, §2.1.1 p.7, §4.1 p.16, Fig. 3 p.17: its coordinates are the
`L = 4^j` leaves of a complete four-ary tree of depth `j`, listed by child-index sequence (base-4
digits of `i`, most significant first), the same for `A` and for `C`. -/
def Sh (X : Scheme) (j : ℕ) (s : F2) (θ : Fin (maskLen X j) → F2) (i : Fin (4 ^ j)) : F2 :=
  leafShare X (rd θ) j 0 s i

end QuadraticRE


