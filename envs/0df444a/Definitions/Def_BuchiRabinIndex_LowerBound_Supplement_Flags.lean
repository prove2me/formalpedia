-- Prove2me | Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Flags
-- name    : BuchiRabinIndex_LowerBound_Supplement_Flags
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:49:43.122715+00:00
-- url     : https://prove2.me/theorems/43d07fc5-db6f-48f4-ba43-1bce51099261
-- title:
--   Minimum flags and the literal canonical flag algorithm
-- statement:
--   For $n\ge1$, use the published full ordered tree $T^{(n)}$, chain $C(x)$ and coexistence graph $G_n$. Let $G_{n,w}$ be the induced subgraph on the names of weight $w$. Independently of the canonical algorithm, define
--   $$\operatorname{sf}(n,w)=\chi(G_{n,w}),\qquad \chi(n)=\chi(G_n).$$
--   Thus sf is the minimum number of flags distinguishing distinct coexisting names at that weight. Colours may be relabelled $1,\ldots,k$; the minimum is unchanged. Both graphs are finite, so converting their extended natural chromatic numbers to natural numbers loses no value.
--
--   The canonical flag $\operatorname{cf}(n,x)$ is the literal recursion of Definition 17: the root has flag 1; a name starting with 1 strips that first entry and recurses at $n-1$; a name starting with at least 2 decrements its first entry and recurses at $n-1$, adding $2^{\operatorname{weight}(x)-2}$ exactly when $\operatorname{weight}(x)\le n/2$. For positive $n$, the integer $n/2$ equals $\lceil(n-1)/2\rceil$. The offset branch on a valid name has weight at least 2. The extension at $n=0$ returns 1; inputs outside the full tree are outside the mathematical claims.
--
--   The canonical identifier is
--   $$I_c(x)=(\operatorname{weight}(x),\operatorname{cf}(n,x)).$$
--   Its colour carrier is exactly the finite image of this map on $T^{(n)}$. The weight coordinate is retained. These objects provide the concrete algorithm used in Theorem 19 and in the reduced acceptance condition; no correctness assertion is built into their definitions.
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf, pp. 11–17, Lemma 15 setting, Definition 17, Algorithm 1, Definition 20; Definition 34, p. 26

import Definitions.Def_BuchiRabinIndex_LowerBound_Nodes

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Supplement
noncomputable section
open scoped Classical

/-- The induced coexistence graph on exactly the names of weight w. -/
def weightGraph (n w : ℕ) := (graph n).induce {x | weight x.val = w}

/-- Independent minimum-colouring definition, not the answer of Lemma 15.
Both graphs are finite, so their ENat chromatic numbers are finite. -/
def sf (n w : ℕ) : ℕ := (weightGraph n w).chromaticNumber.toNat

def chi (n : ℕ) : ℕ := (graph n).chromaticNumber.toNat

/-- Definition 17 / Algorithm 1, with recursion on n. The n=0 clause is a
 total extension outside the source domain. For valid non-root inputs n≥2. -/
def cf : ℕ → Node → ℕ
  | 0, _ => 1
  | n + 1, x =>
    match x with
    | [] => 1
    | i :: _v =>
      if i = 1 then cf n (phi1 x)
      else if weight x ≤ (n + 1) / 2 then cf n (phi2 x) + 2 ^ (weight x - 2)
      else cf n (phi2 x)

/-- Definition 20: weight remains a coordinate. -/
def canonicalId (n : ℕ) (x : Node) : ℕ × ℕ := (weight x, cf n x)

def identifiers (n : ℕ) : Finset (ℕ × ℕ) := (fullTree n).image (canonicalId n)

abbrev Identifier (n : ℕ) := ↥(identifiers n)

def canonicalColour (n : ℕ) (x : Vertex n) : Identifier n :=
  ⟨canonicalId n x.val, Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩

end
end BuchiRabinIndex.LowerBound.Supplement


