-- Prove2me | Definitions.Def_EditMulticoloring_Code_Graph
-- name    : EditMulticoloring_Code_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T18:48:17.34895+00:00
-- url     : https://prove2.me/theorems/f7682a6f-d9ca-49c1-8753-0171dfdbae09
-- title:
--   Identifier polynomials, first separating points and prime color palettes
-- statement:
--   For a finite simple graph $G=(V,E)$ with neighbor sets $N(v)$, let $r$ bound the degree and let $K$ bound the bit length of injective vertex identifiers. Set $Q=2^{\lceil\log_2(rK+1)\rceil}$. In a field of order $Q$, with a fixed bijection to $\{0,\ldots,Q-1\}$, use exactly $K$ base-$Q$ identifier digits as polynomial coefficients. The first separating point is found by scanning field labels in increasing order, and its point/evaluation pair supplies the color.
--
--   For a proper $B$-bit coloring $f$, set
--
--   $$L=4(r+1)(B+1),\qquad J=q^{\lfloor\log_q(L/2)\rfloor}.$$
--
--   Prime index $i$ is zero based, so its prime is $p_{i+1}$. Good indices distinguish $f(v)$ from every neighboring label modulo that prime. The allocation takes the first $J$ good indices, with pair $(i,f(v)\bmod p_{i+1})$. These definitions supply the mathematical graph interface and make no assumption that a separating point or sufficiently many good primes exist; those are theorem conclusions.
-- source:
--   Huiling Xie, Zitan Chen, Explicit Edit Codes via Multicoloring, STOC 2027 submission #819 (October 2026), §2.1, Definitions 6 and 8, Eqs. (3)–(6), printed pp. 6–8 (PDF pp. 7–9); pinned repository artifact papers/stoc2027-819/source.pdf, SHA256 00172d5da76bf6bc886b8a1f87450befb76480107f54cb367988a065737eb376.

import Definitions.Def_EditMulticoloring_Code_Words

noncomputable section

namespace EditMulticoloring.Code

/-- General graph objects use Mathlib's finite simple graphs. -/
def neighbors {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Adj v)

def fieldSize (r K : ℕ) : ℕ := 2 ^ ceilLog 2 (r * K + 1)

def fieldElement {F : Type} [Field F] {Q : ℕ} (e : F ≃ Fin Q) (a : ℕ) : F :=
  (((List.finRange Q).map e.symm)[a % Q]?).getD 0

def identifierPoly {F : Type} [Field F] {Q : ℕ} (e : F ≃ Fin Q)
    (K id : ℕ) : Polynomial F :=
  ∑ j ∈ Finset.range K, Polynomial.C (fieldElement e (id / Q ^ j)) * Polynomial.X ^ j

def Separates {V F : Type} [Field F] {Q : ℕ} (G : SimpleGraph V)
    (e : F ≃ Fin Q) (K : ℕ) (id : V → ℕ) (v : V) (a : F) : Prop :=
  ∀ u, G.Adj v u → (identifierPoly e K (id v)).eval a ≠
    (identifierPoly e K (id u)).eval a

def firstSeparating {V F : Type} [Fintype V] [Field F] {Q : ℕ}
    (G : SimpleGraph V) (e : F ≃ Fin Q) (K : ℕ) (id : V → ℕ) (v : V) : F := by
  classical
  exact (((List.finRange Q).map e.symm).find? (fun a => Separates G e K id v a)).getD 0

def polynomialColor {V F : Type} [Fintype V] [Field F] {Q : ℕ}
    (G : SimpleGraph V) (e : F ≃ Fin Q) (K : ℕ) (id : V → ℕ) (v : V) : ℕ :=
  let a := firstSeparating G e K id v
  Q * (e a).val + (e ((identifierPoly e K (id v)).eval a)).val

def primeAt (i : ℕ) : ℕ := Nat.nth Nat.Prime i

def paletteLength (r B : ℕ) : ℕ := 4 * (r + 1) * (B + 1)
def foldCount (q L : ℕ) : ℕ := q ^ floorLog q (L / 2)

def Good {V : Type} (G : SimpleGraph V) (f : V → ℕ) (v : V) (i : ℕ) : Prop :=
  ∀ u, G.Adj v u → f v % primeAt i ≠ f u % primeAt i

def goodIndices {V : Type} [Fintype V] (G : SimpleGraph V) (f : V → ℕ)
    (L : ℕ) (v : V) : List ℕ := by
  classical
  exact (List.range L).filter (Good G f v)

def colorPair {V : Type} [Fintype V] (G : SimpleGraph V) (f : V → ℕ)
    (L : ℕ) (v : V) (j : ℕ) : ℕ × ℕ :=
  let i := ((goodIndices G f L v)[j]?).getD L
  (i, f v % primeAt i)

def assigned {V : Type} [Fintype V] (G : SimpleGraph V) (f : V → ℕ)
    (L J : ℕ) (v : V) : Finset (ℕ × ℕ) :=
  ((List.range J).map (colorPair G f L v)).toFinset

def palette (L : ℕ) : Finset (ℕ × ℕ) :=
  ((List.range L).flatMap fun i => (List.range (primeAt i)).map (i, ·)).toFinset

end EditMulticoloring.Code


