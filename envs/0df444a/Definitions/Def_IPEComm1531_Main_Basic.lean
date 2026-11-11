-- Prove2me | Definitions.Def_IPEComm1531_Main_Basic
-- name    : IPEComm1531_Main_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:00:31.735209+00:00
-- url     : https://prove2.me/theorems/60fd32a9-ea45-45b3-a348-da6f98efba2e
-- title:
--   Bit strings, the field $\mathbb F_{2^{24}}$, tower lengths $r_j$, Hamming distance and monochromatic rectangles
-- statement:
--   Bit strings of length $n$ are maps $[n]\to\mathbb F_2$, so that addition is bitwise XOR $\oplus$; $|x|$ is the Hamming weight and $|x\oplus y|$ the Hamming distance. The density of a set $X\subseteq\{0,1\}^n$ is $|X|/2^n$.
--
--   The field is $\mathbb F_q$ with $q=2^{24}$, together with one fixed ordered $\mathbb F_2$-basis $(\gamma_1,\dots,\gamma_{24})$; a field element $a=\sum_i a_i\gamma_i$ is encoded by its coefficient string $(a_1,\dots,a_{24})$, and a 24-bit string is decoded the same way. Under this encoding field addition is XOR.
--
--   With $\delta=2^{-9}$ the tower lengths are
--   $$r_j=\frac{q^{(j+2)/2}}{4}=2^{12j+22}\qquad(j=0,1,2,\dots),$$
--   and $\delta r_j=r_j/512$ is an integer. For an input length $n$, the level used is the largest $j$ with $2r_j\le n$.
--
--   For a function $F:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}$, a rectangle $A\times B$ ($A,B$ arbitrary subsets) is monochromatic if $F$ is constant on it (either colour), and its uniform density is $|A||B|/2^{2n}$. Finally, the $r$-bit slice starting at offset $o$ of an $n$-bit input reads bits $o,\dots,o+r-1$.
--
--   These are the shared conventions of §2–§3 used by every statement of the mission.
--
--   **Formalization Note** The field is `GaloisField 2 24` with a basis chosen once by `Module.finBasisOfFinrankEq`. Bit strings are `Fin n → ZMod 2` internally and `Fin n → Bool` for the communication inputs. The level is `0` when no $j$ satisfies $2r_j\le n$; that case is never used, since the function family is constant there.
-- source:
--   Haoyu Wang, Pei Wu, Efficient Randomized Communication Without Large Monochromatic Rectangles, STOC 2027 submission #1531 (October 2026), PDF sha256 b5961a61deb8c9214217a3a78e8963de31cc748f73e562aad19dd584eb9eb136, §2 Notation, Finite-field arithmetic and Rectangles, pp.5–6; §3 parameter choice, p.7

import Mathlib

set_option autoImplicit false

namespace IPEComm1531.Main

/-- Bit strings of length `n`, with XOR as addition (§2, p.5). -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The field `F_q`, `q = 2^24` (§3, p.7). -/
abbrev F := GaloisField 2 24

noncomputable instance fieldFintype : Fintype F := Fintype.ofFinite F

/-- A fixed ordered `F₂`-basis `(γ₁, …, γ₂₄)` of `F_q` (§2, p.5). -/
noncomputable def fieldBasis : Module.Basis (Fin 24) (ZMod 2) F :=
  Module.finBasisOfFinrankEq (ZMod 2) F (GaloisField.finrank 2 (n := 24) (by decide))

/-- `r_j = q^{(j+2)/2}/4 = 2^{12 j + 22}` (§3, p.7, `q = 2^24`). -/
def radius (j : ℕ) : ℕ := 2 ^ (12 * j + 22)

/-- `δ r_j` with `δ = 2^{-9}`; exact since `2^9 ∣ r_j`. -/
def slack (j : ℕ) : ℕ := radius j / 512

/-- Hamming weight `|x|`. -/
def weight {n : ℕ} (x : Bits n) : ℕ := (Finset.univ.filter fun i => x i ≠ 0).card

/-- Hamming distance `|x ⊕ y|`. -/
def distance {n : ℕ} (x y : Bits n) : ℕ := weight (x + y)

/-- Density `|X|/2^n` of a set of `n`-bit strings. -/
noncomputable def density {n : ℕ} (X : Finset (Bits n)) : ℝ := (X.card : ℝ) / (2 : ℝ) ^ n

def bitBool (b : ZMod 2) : Bool := decide (b ≠ 0)
def boolBit (b : Bool) : ZMod 2 := if b then 1 else 0

/-- A bit string as the list of its bits, in index order. -/
def bitList {n : ℕ} (x : Bits n) : List Bool := (List.finRange n).map fun i => bitBool (x i)

/-- The 24 coefficient bits of a field element in the fixed basis (§2, p.5). -/
noncomputable def encodeField (a : F) : List Bool := bitList fun i => fieldBasis.repr a i

/-- The field element with the given 24 coefficient bits. -/
noncomputable def decodeField (a : Bits 24) : F := ∑ i, a i • fieldBasis i

/-- Value of a bit string read as a binary number, most significant bit first. -/
def bitsNat {n : ℕ} (x : Bits n) : ℕ :=
  ∑ i : Fin n, if x i = 0 then 0 else 2 ^ (n - 1 - i.val)

/-- The `n`-bit binary expansion of `a` (most significant bit first). -/
def bitsOfNat (n a : ℕ) : Bits n := fun i => boolBit (a.testBit (n - 1 - i.val))

/-- Bits `off, off+1, …, off+r-1` of a Boolean input string (zero beyond its end). -/
def slice {n : ℕ} (r off : ℕ) (x : Fin n → Bool) : Bits r :=
  fun i => if h : off + i.val < n then boolBit (x ⟨off + i.val, h⟩) else 0

/-- Uniform density `|A||B|/2^{2n}` of a rectangle `A × B` of `n`-bit input pairs (§2, p.6). -/
noncomputable def rectangleDensity {n : ℕ} (A B : Finset (Fin n → Bool)) : ℝ :=
  (A.card : ℝ) * B.card / (2 : ℝ) ^ (2 * n)

/-- `A × B` is monochromatic for `f`: `f` takes one value (0 or 1) on all of it (§2, p.6). -/
def Monochromatic {n : ℕ} (f : (Fin n → Bool) → (Fin n → Bool) → Bool)
    (A B : Finset (Fin n → Bool)) : Prop :=
  ∃ color : Bool, ∀ x ∈ A, ∀ y ∈ B, f x y = color

/-- The largest tower level `j` with `2 r_j ≤ n` (§3, p.7); `0` if there is none. -/
def level (n : ℕ) : ℕ := ((Finset.range (n + 1)).filter fun j => 2 * radius j ≤ n).sup id

end IPEComm1531.Main


