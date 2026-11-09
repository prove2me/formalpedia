-- Prove2me | Definitions.Def_QuadraticProbe717_Insertion_arithmetic
-- name    : QuadraticProbe717_Insertion_arithmetic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:20:25.812253+00:00
-- url     : https://prove2.me/theorems/0afa84ae-e7d9-4264-82e8-fba52f871483
-- title:
--   Square differences, translated prefixes, and rectangle counts
-- statement:
--   For a prefix length $k$ and residues modulo $n$, define
--   $$R(k)=\max_{r\ne0}\#\{(a,b):0\le a<b<k,\ b^2-a^2=r\pmod n\},\qquad Q=\{i^2:0\le i<k\}.$$
--   A maximum over no residues is zero. The auxiliary divisor maximum is $\max_{1\le i<k^2}\tau(i)$, with the same empty-maximum convention. Write $Q+j$ for a modular translate. For a finite set $J$ of shifts, count $\bigcap_{j\in J}(Q+j)$; its empty intersection is the full slot universe. For an occupied set $A$, the bad shifts are those $j$ with $Q+j\subseteq A$.
--
--   The covering threshold and rectangle count are
--   $$L_{k,n}=\left\lceil2(n/k)\ln(\varepsilon^{-1})\right\rceil,\quad H=\#\{(i,j):1\le i\le X,\ 1\le j\le Y,\ (U+i)(V+j)=r\pmod n\}.$$
--   These definitions contain no cardinality estimates. Natural-number slots and interval endpoints represent the source's zero-based finite sets; congruences are equalities in $\mathbb Z/n\mathbb Z$.
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), equation (4); Section 6.1, p. 12; Section 6.2, p. 13, p. 8 (PDF p. 8)

import Mathlib

set_option autoImplicit false

namespace QuadraticProbe717.Insertion

def squarePairs (n k : ℕ) (r : ZMod n) : Finset (Fin k × Fin k) :=
  Finset.univ.filter (fun ab => ab.1 < ab.2 ∧ (ab.2.val : ZMod n)^2 - (ab.1.val : ZMod n)^2 = r)

/-- Maximum over nonzero residues; max' is avoided so the empty maximum is explicitly zero. -/
def multiplicity (n k : ℕ) [NeZero n] : ℕ :=
  (Finset.univ.filter (fun r : ZMod n => r ≠ 0)).sup (fun r => (squarePairs n k r).card)

def maxDivisors (k : ℕ) : ℕ :=
  (Finset.Ico 1 (k^2)).sup (fun i => i.divisors.card)

def squarePrefix (n k : ℕ) : Finset (ZMod n) :=
  (Finset.range k).image (fun i : ℕ => (i : ZMod n)^2)

def shiftedPrefix (n k : ℕ) (j : ZMod n) : Finset (ZMod n) :=
  (squarePrefix n k).image (fun q => q + j)

def shiftIntersection (n k : ℕ) [NeZero n] (J : Finset (ZMod n)) : Finset (ZMod n) :=
  Finset.univ.filter (fun x => ∀ j ∈ J, x ∈ shiftedPrefix n k j)

def badShifts (n k : ℕ) [NeZero n] (A : Finset (ZMod n)) : Finset (ZMod n) :=
  Finset.univ.filter (fun j => shiftedPrefix n k j ⊆ A)

noncomputable def coveringThreshold (n k : ℕ) (ε : ℝ) : ℕ :=
  ⌈2 * ((n : ℝ) / k) * Real.log ε⁻¹⌉₊

def hyperbolaCount (n U V X Y : ℕ) (r : ZMod n) : ℕ :=
  (((Finset.Icc 1 X).product (Finset.Icc 1 Y)).filter
    (fun ij => ((U + ij.1 : ℕ) : ZMod n) * ((V + ij.2 : ℕ) : ZMod n) = r)).card

end QuadraticProbe717.Insertion


