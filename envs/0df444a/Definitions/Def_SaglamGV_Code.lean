-- Prove2me | Definitions.Def_SaglamGV_Code
-- name    : SaglamGV_Code
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:46:10.071192+00:00
-- url     : https://prove2.me/theorems/f292bd64-5b07-4790-847e-d124d0728fca
-- title:
--   Punctured Hamming ball $B_d$, its size $V$, and distance-$d$ linear codes
-- statement:
--   Words of length $n$ are vectors $x\in\mathbb F_2^n$, and $|x|$ is the Hamming weight of $x$ (its number of nonzero coordinates). For $d\ge 0$ the **punctured Hamming ball** is
--
--   $$
--   B_d=\{x\in\mathbb F_2^n : 0<|x|<d\},
--   $$
--
--   the set of nonzero words of weight at most $d-1$, and $V=|B_d|=\sum_{i=1}^{d-1}\binom ni$. A **binary linear code** is a subspace $C\subseteq\mathbb F_2^n$; it has **distance $d$** (in the sense used throughout the paper) if no nonzero codeword has weight less than $d$, equivalently $C\cap B_d=\emptyset$. This is the condition "$Hx\ne 0$ for all $x\in B_d$" on a parity check matrix $H$ with $C=\ker H$. The module also fixes the dot product $x\cdot y=\sum_i x_iy_i\in\mathbb F_2$.
--
--   These are the objects of the main theorem: the paper constructs subspaces with $C\cap B_d=\emptyset$ that are larger than the Gilbert–Varshamov bound $2^n/(V+1)$ by a factor $\Omega(n)$.
--
--   **Formalization Note** Words are `Fin n → ZMod 2`, the weight is Mathlib's `hammingNorm`, codes are `Submodule (ZMod 2) (Fin n → ZMod 2)`. `HasDistAtLeast C d` says every nonzero codeword has weight at least $d$; for a linear code this is minimum distance at least $d$ (not exactly $d$). For $d\le 1$, $B_d=\emptyset$ and $V=0$.
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), §1, p.1 (B_d, V, parity check matrices); §2, p.3 (distance-d code); §3.1, p.3 (x·y)

import Mathlib

namespace SaglamGV

/-- The punctured Hamming ball `B_d = {x ∈ 𝔽₂ⁿ | 0 < |x| < d}`
(M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript
(held version, sha256 ac6f2bba…), §1, p.1: "Denote B_d = {x ∈ F_2^n | 0 < |x| < d} the set of all
0-1 vectors with weight between 1 and d − 1").

**Formalization Note** Words are `Fin n → ZMod 2` and the weight `|x|` is Mathlib's `hammingNorm`
(the number of nonzero coordinates). For `d ≤ 1` the set is empty. -/
def ballP (n d : ℕ) : Finset (Fin n → ZMod 2) :=
  Finset.univ.filter (fun x => 0 < hammingNorm x ∧ hammingNorm x < d)

/-- `V = |B_d|`, the number of nonzero words of weight below `d` (Saglam, §1, p.1: "set V = |B_d|").
It equals `∑_{i=1}^{d−1} C(n,i)`. -/
def vol (n d : ℕ) : ℕ := (ballP n d).card

/-- A binary linear code `C ⊆ 𝔽₂ⁿ` has **distance `d`** in the sense of the paper: no nonzero codeword
has weight below `d` (Saglam, §1, p.1: a parity check matrix `H` "satisfying Hx ≠ 0 for all x ∈ B_d";
§2, p.3: "a parity-check matrix for a distance-d code").

**Formalization Note** For a linear code the minimum distance equals the minimum weight of a nonzero
codeword, so this is "minimum distance at least `d`"; it does not require the minimum distance to be
exactly `d`. Codes are `Submodule (ZMod 2) (Fin n → ZMod 2)`. -/
def HasDistAtLeast {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2)) (d : ℕ) : Prop :=
  ∀ x ∈ C, x ≠ 0 → d ≤ hammingNorm x

/-- The dot product `x · y = ∑ᵢ xᵢ yᵢ` in `𝔽₂` (Saglam, §2, p.3, the row vector `v` acting on a
column `x`; §3.1, p.3, the exponent of `χ_y(x) = (−1)^{x·y}`). -/
def dot {n : ℕ} (x y : Fin n → ZMod 2) : ZMod 2 := ∑ i, x i * y i

end SaglamGV


