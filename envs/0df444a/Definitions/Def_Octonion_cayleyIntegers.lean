-- Prove2me | Definitions.Def_Octonion_cayleyIntegers
-- name    : Octonion_cayleyIntegers
-- status  : Definition
-- author  : @jawneeboy
-- created : 2026-09-23T13:26:55.060482+00:00
-- url     : https://prove2.me/theorems/710d4e48-2188-45e7-9d5a-a710f6c28de0
-- title:
--   A chosen Cayley order over the rationals
-- statement:
--   Use the Cayley–Dickson model $\mathbb O_R=\mathbb H_R\times\mathbb H_R$, with $(a,b)(c,d)=(ac-\bar d b,da+b\bar c)$ and $\overline{(a,b)}=(\bar a,-b)$. Let $\mathcal C\subset\mathbb O_{\mathbb Q}$ be the chosen Cayley order: $x=a/2$ for $a\in\mathbb Z^8$, with the mask $\sum_{a_i\text{ odd}}2^i$ in $M=\{0,15,51,60,86,89,101,106,149,154,166,169,195,204,240,255\}$. The bundle establishes closure under addition, negation, multiplication, and contains zero and one. It does not assert maximality or an identification with a root lattice.
-- source:
--   Standard reference: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345. Relevant topics appear in Chapter 6 (composition algebras), Chapter 9 (octavian integers), and Section 10.1 (the 240 octavian units), as confirmed by the publisher's table of contents. Supporting exposition: John Baez, Integral Octonions (Part 6), September 17, 2013, https://math.ucr.edu/home/baez/octonions/integers/integers_6.html. These references concern the classical mathematics. This contribution supplies Lean definitions and machine-checked proofs in the stated coordinate convention; it does not claim new mathematical results or reproduce a particular proof from the book. The topic references do not assert that the exact Lean statement occurs there. Verification of the book references is limited to its table of contents, not a statement-by-statement comparison with the book; no page-specific or numbered theorem attribution is claimed. Local formalization: Basic/Def_Octonion_cayleyIntegers.lean; SHA-256 ceccf41515dcfb1e219490e7eb6a1778188ae38b21eedb51141c5b4f57f56346.

import Definitions.Def_Octonion_octonions
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# A chosen Cayley order over `ℚ`

This file defines `cayleyIntegers` by an explicit parity condition and proves closure
under addition, negation and the Cayley-Dickson product. Coordinates are ordered as
`(fst.re, fst.imI, fst.imJ, fst.imK, snd.re, snd.imI, snd.imJ, snd.imK)`.
An element has coordinates `a i / 2` for integers `a i`, and the odd entries of `a`
must be encoded by one of the sixteen masks in `cayleyMasks`. Bit `i` is the
coefficient of `2^i`, so mask `15` selects coordinates `0,1,2,3`.

The mask list fixes the chosen order and its basis convention. It corresponds to
swapping coordinates `0` and `1` in the Kirmse construction for this basis.
The proofs use the explicit masks, rather than a formalized Kirmse lattice.
The codewords have weight divisible by four, which yields integral squared norm
in `normSq_int`.

For background on Cayley orders, the coordinate-swap construction, maximality and
the rescaled E8 lattice, see John Baez, *Integral Octonions (Part 6)*,
https://math.ucr.edu/home/baez/octonions/integers/integers_6.html.
Maximality and an identification with E8 are not formalized here. See
`OCTONIONS.md` for the scope of the proved results and the coordinate conventions.
-/

open Quaternion BigOperators

namespace Octonion

/-- The eight rational coordinates of an octonion: the four quaternion coordinates of each
Cayley-Dickson slot. -/
def coord8 (x : octonions ℚ) (i : Fin 8) : ℚ :=
  if _ : (i : ℕ) = 0 then x.fst.re
  else if _ : (i : ℕ) = 1 then x.fst.imI
  else if _ : (i : ℕ) = 2 then x.fst.imJ
  else if _ : (i : ℕ) = 3 then x.fst.imK
  else if _ : (i : ℕ) = 4 then x.snd.re
  else if _ : (i : ℕ) = 5 then x.snd.imI
  else if _ : (i : ℕ) = 6 then x.snd.imJ
  else x.snd.imK

/-- Two octonions are equal if all eight coordinates agree. -/
theorem ext_coord8 {x y : octonions ℚ} (h : ∀ i : Fin 8, coord8 x i = coord8 y i) : x = y := by
  apply octonions.ext
  · apply Quaternion.ext
    · simpa [coord8] using h 0
    · simpa [coord8] using h 1
    · simpa [coord8] using h 2
    · simpa [coord8] using h 3
  · apply Quaternion.ext
    · simpa [coord8] using h 4
    · simpa [coord8] using h 5
    · simpa [coord8] using h 6
    · simpa [coord8] using h 7

/-- `halfOf a` is the octonion whose doubled coordinates are the integer vector `a`. -/
def halfOf (a : Fin 8 → ℤ) : octonions ℚ :=
  ⟨⟨a 0 / 2, a 1 / 2, a 2 / 2, a 3 / 2⟩, ⟨a 4 / 2, a 5 / 2, a 6 / 2, a 7 / 2⟩⟩

@[simp] theorem coord8_halfOf (a : Fin 8 → ℤ) (i : Fin 8) :
    coord8 (halfOf a) i = (a i : ℚ) / 2 := by
  fin_cases i <;> simp [coord8, halfOf]

@[simp] theorem coord8_zero (i : Fin 8) : coord8 (0 : octonions ℚ) i = 0 := by
  fin_cases i <;> simp [coord8]

theorem coord8_add (x y : octonions ℚ) (i : Fin 8) :
    coord8 (x + y) i = coord8 x i + coord8 y i := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  fin_cases i <;> rfl

theorem coord8_neg (x : octonions ℚ) (i : Fin 8) : coord8 (-x) i = -coord8 x i := by
  obtain ⟨a, b⟩ := x
  fin_cases i <;> rfl

theorem coord8_sub (x y : octonions ℚ) (i : Fin 8) :
    coord8 (x - y) i = coord8 x i - coord8 y i := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  fin_cases i <;> rfl

/-- Coordinates of octonion conjugation: the real coordinate is fixed, every imaginary coordinate
changes sign. Proved over properly typed quaternion variables: unfolding `halfOf` under `star`
leaves terms whose spelling (`ℍ[ℚ]` versus `ℍ[ℚ,-1,-1]`, as `Quaternion` is a def over
`QuaternionAlgebra`) blocks simp matching. -/
theorem coord8_conj (x : octonions ℚ) (i : Fin 8) :
    coord8 (conj x) i = if i = 0 then coord8 x i else -coord8 x i := by
  obtain ⟨a, b⟩ := x
  fin_cases i
  · exact Quaternion.re_star a
  · exact Quaternion.imI_star a
  · exact Quaternion.imJ_star a
  · exact Quaternion.imK_star a
  · exact Quaternion.re_neg b
  · exact Quaternion.imI_neg b
  · exact Quaternion.imJ_neg b
  · exact Quaternion.imK_neg b

/-- The sixteen parity masks of the extended Hamming `[8,4,4]` code: the coset space over `ℤ⁸`
of the Cayley order, written as bit masks with bit `i` recording half-integrality of coordinate
`i`. They are the Kirmse lattice cosets after the swap of coordinates `0` and `1`. -/
def cayleyMasks : Finset ℕ :=
  {0, 15, 51, 60, 86, 89, 101, 106, 149, 154, 166, 169, 195, 204, 240, 255}

/-- The parity pattern of a mask. -/
def patOfMask (m : ℕ) (i : Fin 8) : Bool := Nat.testBit m i.val

/-- The extended Hamming `[8,4,4]` code as the sixteen parity patterns of `cayleyMasks`. -/
def cayleyCode : Finset (Fin 8 → Bool) := cayleyMasks.image patOfMask

/-- The parity code condition: the odd/even pattern of `a` is a Hamming codeword. -/
def parCode (a : Fin 8 → ℤ) : Prop := ((fun i => decide (Odd (a i))) ∈ cayleyCode)

/-- An octonion over `ℚ` is a Cayley integer if its doubled coordinates are an integer vector
whose parity pattern lies in the extended Hamming code: all eight coordinates lie in `½ℤ` and
their half-integrality pattern is one of the sixteen masks. -/
def isCayley (x : octonions ℚ) : Prop := ∃ a : Fin 8 → ℤ, x = halfOf a ∧ parCode a

theorem patOfMask_zero : patOfMask 0 = fun _ => false := by
  ext i
  simp [patOfMask]

private theorem patOfMask_xor (m n : ℕ) :
    patOfMask (m ^^^ n) = fun i => (patOfMask m i).xor (patOfMask n i) := by
  ext i
  rw [patOfMask, Nat.testBit_xor, patOfMask, patOfMask]

/-- The mask set is closed under bitwise xor (the code is an `𝔽₂`-subspace). -/
private theorem cayleyMasks_xor {x y : ℕ} (hx : x ∈ cayleyMasks) (hy : y ∈ cayleyMasks) :
    (x ^^^ y) ∈ cayleyMasks := by
  have h : ∀ m ∈ cayleyMasks, ∀ n ∈ cayleyMasks, (m ^^^ n) ∈ cayleyMasks := by
    decide +kernel
  exact h x hx y hy

private theorem decide_odd_add (p q : ℤ) :
    decide (Odd (p + q)) = (decide (Odd p)).xor (decide (Odd q)) := by
  obtain hp : p % 2 = 0 ∨ p % 2 = 1 := by omega
  obtain hq : q % 2 = 0 ∨ q % 2 = 1 := by omega
  rcases hp with h | h <;> rcases hq with h' | h' <;> simp [h, h', Int.odd_iff, Int.add_emod]

theorem decide_odd_neg (p : ℤ) : decide (Odd (-p)) = decide (Odd p) := by
  have key : Odd (-p) ↔ Odd p :=
    ⟨fun ⟨k, hk⟩ => ⟨-k - 1, by omega⟩, fun ⟨k, hk⟩ => ⟨-k - 1, by omega⟩⟩
  by_cases h1 : Odd p
  · have h2 : Odd (-p) := key.mpr h1
    simp [h1, h2]
  · have h2 : ¬ Odd (-p) := fun hx => h1 (key.mp hx)
    simp [h1, h2]

/-- The sum of two Cayley integers is a Cayley integer: parity patterns xor and the code is an
`𝔽₂`-subspace. -/
theorem isCayley_add {x y : octonions ℚ} (hx : isCayley x) (hy : isCayley y) :
    isCayley (x + y) := by
  obtain ⟨a, rfl, pa⟩ := hx
  obtain ⟨b, rfl, pb⟩ := hy
  refine ⟨fun i => a i + b i, ext_coord8 fun i => ?_, ?_⟩
  · simp only [coord8_add, coord8_halfOf]
    push_cast
    field_simp
  · obtain ⟨m, hm, ham⟩ := Finset.mem_image.mp pa
    obtain ⟨n, hn, hbn⟩ := Finset.mem_image.mp pb
    refine Finset.mem_image.mpr ⟨m ^^^ n, cayleyMasks_xor hm hn, ?_⟩
    have key : (fun i => decide (Odd (a i + b i))) =
        fun i => (patOfMask m i).xor (patOfMask n i) := by
      funext i
      rw [decide_odd_add, ← congr_fun ham i, ← congr_fun hbn i]
    rw [key, patOfMask_xor]

/-- The negation of a Cayley integer is a Cayley integer: parity is sign-invariant. -/
theorem isCayley_neg {x : octonions ℚ} (hx : isCayley x) : isCayley (-x) := by
  obtain ⟨a, rfl, pa⟩ := hx
  refine ⟨fun i => -a i, ext_coord8 fun i => ?_, ?_⟩
  · simp only [coord8_neg, coord8_halfOf]
    push_cast
    field_simp
  · obtain ⟨m, hm, ham⟩ := Finset.mem_image.mp pa
    refine Finset.mem_image.mpr ⟨m, hm, ?_⟩
    have key : (fun i => decide (Odd (-a i))) = fun i => decide (Odd (a i)) := by
      funext i
      rw [decide_odd_neg]
    rw [key, ← ham]

/-- Zero is a Cayley integer. -/
theorem isCayley_zero : isCayley (0 : octonions ℚ) := by
  refine ⟨0, ext_coord8 fun i => ?_, Finset.mem_image.mpr ⟨0, by decide, ?_⟩⟩
  · rw [coord8_halfOf, coord8_zero]
    simp only [Pi.zero_apply]
    norm_num
  · rw [patOfMask_zero]
    ext i
    simp

/-- One is a Cayley integer. -/
theorem isCayley_one : isCayley (1 : octonions ℚ) := by
  refine ⟨fun i => if i = 0 then 2 else 0, ext_coord8 fun i => ?_,
    Finset.mem_image.mpr ⟨0, by decide, ?_⟩⟩
  · rw [coord8_halfOf]
    fin_cases i <;> simp [coord8, fst_one, snd_one]
  · rw [patOfMask_zero]
    ext i
    fin_cases i <;> rfl

/-- The octonions whose eight coordinates are integers: the Gravesian order. -/
private def inGraves (x : octonions ℚ) : Prop := ∀ i : Fin 8, ∃ n : ℤ, coord8 x i = n

private theorem isCayley_of_inGraves {x : octonions ℚ} (hx : inGraves x) : isCayley x := by
  choose a ha using hx
  refine ⟨fun i => 2 * a i, ext_coord8 fun i => ?_, Finset.mem_image.mpr ⟨0, by decide, ?_⟩⟩
  · rw [coord8_halfOf]
    have hz : ((2 * a i : ℤ) : ℚ) / 2 = (a i : ℚ) := by
      push_cast
      field_simp
    rw [hz]
    exact ha i
  · rw [patOfMask_zero]
    ext i
    have h2 : ¬ Odd (2 * a i) := fun h => by
      have := Int.odd_iff.mp h
      omega
    simp [h2]

/-- The Gravesian integers are closed under multiplication: each coordinate of the product is
the corresponding bilinear form in the coordinates, read off the Cayley-Dickson table. -/
private theorem inGraves_mul {x y : octonions ℚ} (hx : inGraves x) (hy : inGraves y) :
    inGraves (x * y) := by
  choose z hz using hx
  choose w hw using hy
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  have az0 : a.re = z 0 := by simpa [coord8] using hz 0
  have az1 : a.imI = z 1 := by simpa [coord8] using hz 1
  have az2 : a.imJ = z 2 := by simpa [coord8] using hz 2
  have az3 : a.imK = z 3 := by simpa [coord8] using hz 3
  have bz4 : b.re = z 4 := by simpa [coord8] using hz 4
  have bz5 : b.imI = z 5 := by simpa [coord8] using hz 5
  have bz6 : b.imJ = z 6 := by simpa [coord8] using hz 6
  have bz7 : b.imK = z 7 := by simpa [coord8] using hz 7
  have cw0 : c.re = w 0 := by simpa [coord8] using hw 0
  have cw1 : c.imI = w 1 := by simpa [coord8] using hw 1
  have cw2 : c.imJ = w 2 := by simpa [coord8] using hw 2
  have cw3 : c.imK = w 3 := by simpa [coord8] using hw 3
  have dw4 : d.re = w 4 := by simpa [coord8] using hw 4
  have dw5 : d.imI = w 5 := by simpa [coord8] using hw 5
  have dw6 : d.imJ = w 6 := by simpa [coord8] using hw 6
  have dw7 : d.imK = w 7 := by simpa [coord8] using hw 7
  intro k
  fin_cases k
  · refine ⟨z 0 * w 0 - z 1 * w 1 - z 2 * w 2 - z 3 * w 3 - z 4 * w 4 - z 5 * w 5 - z 6 * w 6 -
      z 7 * w 7, ?_⟩
    simp only [coord8, fst_mul, snd_mul, Quaternion.re_add, Quaternion.imI_add,
      Quaternion.imJ_add, Quaternion.imK_add, Quaternion.re_sub, Quaternion.imI_sub,
      Quaternion.imJ_sub, Quaternion.imK_sub, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star, az0, az1, az2, az3, bz4, bz5, bz6, bz7, cw0, cw1,
      cw2, cw3, dw4, dw5, dw6, dw7]
    push_cast
    ring
  · refine ⟨z 0 * w 1 + z 1 * w 0 + z 2 * w 3 - z 3 * w 2 + z 4 * w 5 - z 5 * w 4 - z 6 * w 7 +
      z 7 * w 6, ?_⟩
    simp only [coord8, fst_mul, snd_mul, Quaternion.re_add, Quaternion.imI_add,
      Quaternion.imJ_add, Quaternion.imK_add, Quaternion.re_sub, Quaternion.imI_sub,
      Quaternion.imJ_sub, Quaternion.imK_sub, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star, az0, az1, az2, az3, bz4, bz5, bz6, bz7, cw0, cw1,
      cw2, cw3, dw4, dw5, dw6, dw7]
    push_cast
    ring
  · refine ⟨z 0 * w 2 - z 1 * w 3 + z 2 * w 0 + z 3 * w 1 + z 4 * w 6 + z 5 * w 7 - z 6 * w 4 -
      z 7 * w 5, ?_⟩
    simp only [coord8, fst_mul, snd_mul, Quaternion.re_add, Quaternion.imI_add,
      Quaternion.imJ_add, Quaternion.imK_add, Quaternion.re_sub, Quaternion.imI_sub,
      Quaternion.imJ_sub, Quaternion.imK_sub, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star, az0, az1, az2, az3, bz4, bz5, bz6, bz7, cw0, cw1,
      cw2, cw3, dw4, dw5, dw6, dw7]
    push_cast
    ring
  · refine ⟨z 0 * w 3 + z 1 * w 2 - z 2 * w 1 + z 3 * w 0 + z 4 * w 7 - z 5 * w 6 + z 6 * w 5 -
      z 7 * w 4, ?_⟩
    simp only [coord8, fst_mul, snd_mul, Quaternion.re_add, Quaternion.imI_add,
      Quaternion.imJ_add, Quaternion.imK_add, Quaternion.re_sub, Quaternion.imI_sub,
      Quaternion.imJ_sub, Quaternion.imK_sub, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star, az0, az1, az2, az3, bz4, bz5, bz6, bz7, cw0, cw1,
      cw2, cw3, dw4, dw5, dw6, dw7]
    push_cast
    ring
  · refine ⟨z 0 * w 4 - z 1 * w 5 - z 2 * w 6 - z 3 * w 7 + z 4 * w 0 + z 5 * w 1 + z 6 * w 2 +
      z 7 * w 3, ?_⟩
    simp only [coord8, fst_mul, snd_mul, Quaternion.re_add, Quaternion.imI_add,
      Quaternion.imJ_add, Quaternion.imK_add, Quaternion.re_sub, Quaternion.imI_sub,
      Quaternion.imJ_sub, Quaternion.imK_sub, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star, az0, az1, az2, az3, bz4, bz5, bz6, bz7, cw0, cw1,
      cw2, cw3, dw4, dw5, dw6, dw7]
    push_cast
    ring
  · refine ⟨z 0 * w 5 + z 1 * w 4 - z 2 * w 7 + z 3 * w 6 - z 4 * w 1 + z 5 * w 0 - z 6 * w 3 +
      z 7 * w 2, ?_⟩
    simp only [coord8, fst_mul, snd_mul, Quaternion.re_add, Quaternion.imI_add,
      Quaternion.imJ_add, Quaternion.imK_add, Quaternion.re_sub, Quaternion.imI_sub,
      Quaternion.imJ_sub, Quaternion.imK_sub, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star, az0, az1, az2, az3, bz4, bz5, bz6, bz7, cw0, cw1,
      cw2, cw3, dw4, dw5, dw6, dw7]
    push_cast
    ring
  · refine ⟨z 0 * w 6 + z 1 * w 7 + z 2 * w 4 - z 3 * w 5 - z 4 * w 2 + z 5 * w 3 + z 6 * w 0 -
      z 7 * w 1, ?_⟩
    simp only [coord8, fst_mul, snd_mul, Quaternion.re_add, Quaternion.imI_add,
      Quaternion.imJ_add, Quaternion.imK_add, Quaternion.re_sub, Quaternion.imI_sub,
      Quaternion.imJ_sub, Quaternion.imK_sub, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star, az0, az1, az2, az3, bz4, bz5, bz6, bz7, cw0, cw1,
      cw2, cw3, dw4, dw5, dw6, dw7]
    push_cast
    ring
  · refine ⟨z 0 * w 7 - z 1 * w 6 + z 2 * w 5 + z 3 * w 4 - z 4 * w 3 - z 5 * w 2 + z 6 * w 1 +
      z 7 * w 0, ?_⟩
    simp only [coord8, fst_mul, snd_mul, Quaternion.re_add, Quaternion.imI_add,
      Quaternion.imJ_add, Quaternion.imK_add, Quaternion.re_sub, Quaternion.imI_sub,
      Quaternion.imJ_sub, Quaternion.imK_sub, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star, az0, az1, az2, az3, bz4, bz5, bz6, bz7, cw0, cw1,
      cw2, cw3, dw4, dw5, dw6, dw7]
    push_cast
    ring

/-- The `k`-th standard Gravesian basis vector. -/
def basisVec (k : Fin 8) : octonions ℚ := halfOf fun i => if i = k then 2 else 0

@[simp] theorem coord8_basisVec (k j : Fin 8) :
    coord8 (basisVec k) j = if k = j then 1 else 0 := by
  simp only [basisVec, coord8_halfOf]
  by_cases h : j = k
  · rw [if_pos h, if_pos h.symm]
    norm_num
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]
    norm_num

private theorem coord8_sum {α : Type*} [DecidableEq α] (s : Finset α) (f : α → octonions ℚ)
    (i : Fin 8) :
    coord8 (s.sum f) i = s.sum (fun a => coord8 (f a) i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has, coord8_add, ih]

private theorem coord8_zsmul (z : ℤ) (x : octonions ℚ) (i : Fin 8) :
    coord8 (z • x) i = z • coord8 x i := by
  obtain ⟨a, b⟩ := x
  fin_cases i <;> rfl

private theorem inGraves_decomp_eq {g : octonions ℚ} (_hg : inGraves g) (z : Fin 8 → ℤ)
    (hz : ∀ i, coord8 g i = z i) :
    g = ∑ k : Fin 8, (z k : ℤ) • basisVec k := by
  apply ext_coord8
  intro j
  rw [coord8_sum]
  have h1 : (Finset.univ : Finset (Fin 8)).sum (fun k => coord8 ((z k : ℤ) • basisVec k) j) =
      (Finset.univ : Finset (Fin 8)).sum
        (fun k => (z k : ℤ) • (if k = j then (1 : ℚ) else 0)) :=
    Finset.sum_congr rfl fun k _ => by rw [coord8_zsmul, coord8_basisVec]
  rw [h1]
  have hterm : ∀ k : Fin 8,
      ((z k : ℤ) • (if k = j then (1 : ℚ) else 0)) = if k = j then (↑(z k) : ℚ) else 0 := by
    intro k
    by_cases h : k = j <;> simp [h]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Finset.sum_ite, Finset.filter_eq', Finset.filter_ne']
  simp [hz j]

/-- Left multiplication commutes with natural scalars (bilinearity over `ℕ`). -/
private theorem mul_nsmul₂ : ∀ (n : ℕ) (x y : octonions ℚ), x * (n • y) = n • (x * y) := by
  intro n
  induction n with
  | zero => intro x y; simp only [zero_nsmul, mul_zero]
  | succ n ih => intro x y; simp only [Nat.add_one, succ_nsmul, mul_add, ih]

/-- Left multiplication commutes with integral scalars (bilinearity over `ℤ`). -/
private theorem mul_zsmul₂ (z : ℤ) (x y : octonions ℚ) : x * (z • y) = z • (x * y) := by
  have hpos : ∀ n : ℕ, x * ((n : ℤ) • y) = (n : ℤ) • (x * y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 by norm_cast]
      simp only [add_zsmul, one_zsmul, mul_add, ih]
  cases z with
  | ofNat n => exact hpos n
  | negSucc n =>
    show x * (-((n + 1 : ℕ) : ℤ) • y) = -(((n + 1 : ℕ) : ℤ)) • (x * y)
    rw [neg_zsmul, mul_neg, hpos (n + 1), ← neg_zsmul]

private theorem nsmul_mul₁ : ∀ (n : ℕ) (x y : octonions ℚ), (n • x) * y = n • (x * y) := by
  intro n
  induction n with
  | zero => intro x y; simp only [zero_nsmul, zero_mul]
  | succ n ih => intro x y; simp only [Nat.add_one, succ_nsmul, add_mul, ih]

private theorem zsmul_mul₁ (z : ℤ) (x y : octonions ℚ) : (z • x) * y = z • (x * y) := by
  have hpos : ∀ n : ℕ, ((n : ℤ) • x) * y = (n : ℤ) • (x * y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 by norm_cast]
      simp only [add_zsmul, one_zsmul, add_mul, ih]
  cases z with
  | ofNat n => exact hpos n
  | negSucc n =>
    show (-((n + 1 : ℕ) : ℤ) • x) * y = -(((n + 1 : ℕ) : ℤ)) • (x * y)
    rw [neg_zsmul, neg_mul, hpos (n + 1), ← neg_zsmul]

private theorem mul_sum (a : octonions ℚ) {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → octonions ℚ) :
    a * s.sum f = s.sum (fun x => a * f x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hbs ih => rw [Finset.sum_insert hbs, Finset.sum_insert hbs, mul_add, ih]

private theorem sum_mul (b : octonions ℚ) {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → octonions ℚ) :
    s.sum f * b = s.sum (fun x => f x * b) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih => rw [Finset.sum_insert has, Finset.sum_insert has, add_mul, ih]

/-- Integral multiples of Cayley integers are Cayley integers: multiplying the doubled
coordinate vector by an even scalar lands in the zero codeword, by an odd scalar preserves the
parity pattern. -/
private theorem isCayley_zsmul (z : ℤ) {x : octonions ℚ} (hx : isCayley x) : isCayley (z • x) := by
  obtain ⟨a, rfl, pa⟩ := hx
  refine ⟨fun i => z * a i, ext_coord8 fun i => ?_, ?_⟩
  · simp only [coord8_zsmul, coord8_halfOf, Int.cast_mul]
    rw [zsmul_eq_mul]
    field_simp
  · rcases Int.even_or_odd z with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · refine Finset.mem_image.mpr ⟨0, by decide, ?_⟩
      rw [patOfMask_zero]
      ext i
      have hnot : ¬ Odd ((t + t) * a i) := fun ho => by
        have hodd := Int.odd_iff.mp ho
        have heven : Even ((t + t) * a i) := ⟨t * a i, by ring⟩
        rw [Int.even_iff] at heven
        omega
      simp [hnot]
    · obtain ⟨m, hm, ham⟩ := Finset.mem_image.mp pa
      refine Finset.mem_image.mpr ⟨m, hm, ?_⟩
      have key : (fun i => decide (Odd ((2 * t + 1) * a i))) =
          fun i => decide (Odd (a i)) := by
        funext i
        by_cases h : Odd (a i)
        · have ho : Odd ((2 * t + 1) * a i) :=
            Int.odd_mul.mpr ⟨⟨t, by ring⟩, h⟩
          simp [h, ho]
        · have hn : ¬ Odd ((2 * t + 1) * a i) := fun hx => h (And.right (Int.odd_mul.mp hx))
          simp [h, hn]
      rw [key, ← ham]

private theorem isCayley_sum {α : Type*} [DecidableEq α] (s : Finset α) {f : α → octonions ℚ}
    (hf : ∀ a ∈ s, isCayley (f a)) : isCayley (s.sum f) := by
  induction s using Finset.induction_on with
  | empty => simp [Finset.sum_empty, isCayley_zero]
  | insert a s has ih =>
    rw [Finset.sum_insert has]
    refine isCayley_add (hf a (by simp)) (ih fun b hb => hf b (by simp [hb]))

/-- The Cayley representative of a mask: the half-characteristic vector of its pattern. -/
def cayleyRep (m : ℕ) : octonions ℚ := halfOf fun i => if Nat.testBit m i.val then 1 else 0

/-- Decidable surrogate for `isCayley`, used to discharge the finite tables below and the unit
enumeration in `cayleyUnits`. -/
def decMem (x : octonions ℚ) : Bool :=
  decide (∀ i : Fin 8, (coord8 x i).den ≤ 2) &&
    decide ((fun i => decide ((coord8 x i).den = 2)) ∈ cayleyCode)

/-- A rational with denominator at most `2` is an integer or an odd integer over `2`, and the
parity of that numerator detects the denominator. -/
private theorem rat_half_char (q : ℚ) (hq : q.den ≤ 2) :
    ∃ a : ℤ, q = a / 2 ∧ (Odd a ↔ q.den = 2) := by
  by_cases h2 : q.den = 2
  · refine ⟨q.num, ?_, ⟨fun _ => h2, fun hd => ?_⟩⟩
    · have e := Rat.num_div_den q
      rw [h2] at e
      exact_mod_cast e.symm
    · -- `den = 2` forces the numerator odd by reducedness
      have hc := q.reduced
      rw [hd] at hc
      obtain hp : q.num % 2 = 0 ∨ q.num % 2 = 1 := by omega
      rcases hp with h0 | h0
      · exfalso
        obtain ⟨k, hk⟩ : ∃ k : ℤ, q.num = 2 * k := ⟨q.num / 2, by omega⟩
        have h2abs : (2 : ℕ) ∣ q.num.natAbs := by
          rw [hk, Int.natAbs_mul]
          exact ⟨k.natAbs, by simp⟩
        obtain ⟨s, hs⟩ := h2abs
        have hg : q.num.natAbs.gcd 2 = 1 := by
          rw [← Nat.coprime_iff_gcd_eq_one]
          exact hc
        rw [hs] at hg
        have hdvd : (2 : ℕ) ∣ (2 * s).gcd 2 := Nat.dvd_gcd (by simp) (Nat.dvd_refl 2)
        rw [hg] at hdvd
        exact absurd hdvd (by decide)
      · exact Int.odd_iff.mpr h0
  · have hd : q.den = 1 := by
      have hpos := Rat.den_pos q
      omega
    have e2 : (q.num : ℚ) = q := by
      have e' := Rat.num_div_den q
      rw [hd] at e'
      simpa using e'
    refine ⟨2 * q.num, ?_, ?_⟩
    · calc q = (q.num : ℚ) := e2.symm
      _ = ((2 * q.num : ℤ) : ℚ) / 2 := by push_cast; field_simp
    · refine ⟨fun ho => ?_, fun hh => (h2 hh).elim⟩
      have heven : Even (2 * q.num) := ⟨q.num, by ring⟩
      rw [Int.even_iff] at heven
      have hodd := Int.odd_iff.mp ho
      omega

theorem isCayley_of_decMem {x : octonions ℚ} (h : decMem x = true) : isCayley x := by
  obtain ⟨hden, hmem⟩ : decide (∀ i : Fin 8, (coord8 x i).den ≤ 2) = true ∧
      decide ((fun i => decide ((coord8 x i).den = 2)) ∈ cayleyCode) = true := by
    unfold decMem at h
    cases h1 : decide (∀ i : Fin 8, (coord8 x i).den ≤ 2) <;>
      cases h2 : decide ((fun i => decide ((coord8 x i).den = 2)) ∈ cayleyCode) <;>
        simp_all
  obtain hall' := of_decide_eq_true hden
  obtain hmem' := of_decide_eq_true hmem
  choose a ha using fun i => rat_half_char (coord8 x i) (hall' i)
  refine ⟨a, ext_coord8 fun i => ?_, ?_⟩
  · exact (ha i).1.trans (coord8_halfOf a i).symm
  · show (fun i => decide (Odd (a i))) ∈ cayleyCode
    have key : (fun i => decide (Odd (a i))) = fun i => decide ((coord8 x i).den = 2) := by
      funext i
      by_cases hd : (coord8 x i).den = 2
      · have ho : Odd (a i) := (ha i).2.mpr hd
        simp [hd, ho]
      · have hno : ¬ Odd (a i) := fun hx => hd ((ha i).2.mp hx)
        simp [hd, hno]
    rw [key]
    exact hmem'

/-- Products of Cayley representatives are Cayley integers: `decide +kernel` over the 256 pairs
of masks, using the decidable surrogate. -/
private theorem cayleyRep_mul_cayleyRep {m n : ℕ} (hm : m ∈ cayleyMasks) (hn : n ∈ cayleyMasks) :
    isCayley (cayleyRep m * cayleyRep n) := by
  have h : ∀ p ∈ cayleyMasks ×ˢ cayleyMasks, decMem (cayleyRep p.1 * cayleyRep p.2) = true := by
    decide +kernel
  refine isCayley_of_decMem ?_
  exact h ⟨m, n⟩ (Finset.mem_product.mpr ⟨hm, hn⟩)

/-- Cross products of Cayley representatives with Gravesian basis vectors are Cayley integers:
`decide +kernel` over the 128 pairs in each direction. -/
private theorem cayleyRep_mul_basisVec {m : ℕ} (hm : m ∈ cayleyMasks) (k : Fin 8) :
    isCayley (cayleyRep m * basisVec k) ∧ isCayley (basisVec k * cayleyRep m) := by
  have h1 : ∀ p ∈ cayleyMasks ×ˢ (Finset.univ : Finset (Fin 8)),
      decMem (cayleyRep p.1 * basisVec p.2) = true := by
    decide +kernel
  have h2 : ∀ p ∈ cayleyMasks ×ˢ (Finset.univ : Finset (Fin 8)),
      decMem (basisVec p.2 * cayleyRep p.1) = true := by
    decide +kernel
  exact ⟨isCayley_of_decMem (h1 ⟨m, k⟩ (Finset.mem_product.mpr ⟨hm, Finset.mem_univ k⟩)),
    isCayley_of_decMem (h2 ⟨m, k⟩ (Finset.mem_product.mpr ⟨hm, Finset.mem_univ k⟩))⟩

private theorem cayleyRep_mul_inGraves {m : ℕ} (hm : m ∈ cayleyMasks) {g : octonions ℚ}
    (hg : inGraves g) : isCayley (cayleyRep m * g) := by
  have hgs : inGraves g := hg
  choose z hz using hgs
  have heq : cayleyRep m * g = ∑ k : Fin 8, (z k : ℤ) • (cayleyRep m * basisVec k) := by
    rw [inGraves_decomp_eq hg z hz, mul_sum (cayleyRep m)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_zsmul₂]
  rw [heq]
  refine isCayley_sum _ fun k _ => ?_
  exact isCayley_zsmul _ (cayleyRep_mul_basisVec hm k).1

private theorem inGraves_mul_cayleyRep {m : ℕ} (hm : m ∈ cayleyMasks) {g : octonions ℚ}
    (hg : inGraves g) : isCayley (g * cayleyRep m) := by
  have hgs : inGraves g := hg
  choose z hz using hgs
  have heq : g * cayleyRep m = ∑ k : Fin 8, (z k : ℤ) • (basisVec k * cayleyRep m) := by
    rw [inGraves_decomp_eq hg z hz, sum_mul (cayleyRep m)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [zsmul_mul₁]
  rw [heq]
  refine isCayley_sum _ fun k _ => ?_
  exact isCayley_zsmul _ (cayleyRep_mul_basisVec hm k).2

/-- If the parity pattern of `a` is the mask `m`, then `halfOf a − cayleyRep m` has integral
coordinates: subtracting the half-characteristic vector cancels exactly the odd entries. -/
private theorem halfOf_sub_rep_inGraves {a : Fin 8 → ℤ} {m : ℕ}
    (ham : patOfMask m = fun i => decide (Odd (a i))) : inGraves (halfOf a - cayleyRep m) := by
  intro k
  rcases Int.even_or_odd (a k) with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hnot : ¬ Odd (a k) := fun ho => by
      have hodd := Int.odd_iff.mp ho
      rw [ht] at hodd
      omega
    have hb : Nat.testBit m k.val = false := by
      have e := congr_fun ham k
      exact e.trans (decide_eq_false hnot)
    refine ⟨t, ?_⟩
    rw [coord8_sub, coord8_halfOf, cayleyRep, coord8_halfOf]
    simp only [hb]
    rw [ht]
    push_cast
    field_simp
    ring
  · have hb : Nat.testBit m k.val = true := by
      have ho : Odd (a k) := ⟨t, ht⟩
      have e := congr_fun ham k
      exact e.trans (decide_eq_true ho)
    refine ⟨t, ?_⟩
    rw [coord8_sub, coord8_halfOf, cayleyRep, coord8_halfOf]
    simp only [hb]
    rw [ht]
    push_cast
    field_simp
    ring

/-- The product of two Cayley integers is a Cayley integer: decompose each into its mask
representative plus a Gravesian error, expand the product, and close term by term. -/
theorem isCayley_mul {x y : octonions ℚ} (hx : isCayley x) (hy : isCayley y) :
    isCayley (x * y) := by
  obtain ⟨a, rfl, pa⟩ := hx
  obtain ⟨b, rfl, pb⟩ := hy
  obtain ⟨m, hm, ham⟩ := Finset.mem_image.mp pa
  obtain ⟨n, hn, hbn⟩ := Finset.mem_image.mp pb
  set g₁ : octonions ℚ := halfOf a - cayleyRep m
  set g₂ : octonions ℚ := halfOf b - cayleyRep n
  have hg₁ : inGraves g₁ := halfOf_sub_rep_inGraves ham
  have hg₂ : inGraves g₂ := halfOf_sub_rep_inGraves hbn
  have hx' : halfOf a = cayleyRep m + g₁ := by
    show halfOf a = cayleyRep m + (halfOf a - cayleyRep m)
    rw [add_comm, sub_add_cancel]
  have hy' : halfOf b = cayleyRep n + g₂ := by
    show halfOf b = cayleyRep n + (halfOf b - cayleyRep n)
    rw [add_comm, sub_add_cancel]
  have hA : isCayley (cayleyRep m * cayleyRep n) := cayleyRep_mul_cayleyRep hm hn
  have hB : isCayley (cayleyRep m * g₂) := cayleyRep_mul_inGraves hm hg₂
  have hC : isCayley (g₁ * cayleyRep n) := inGraves_mul_cayleyRep hn hg₁
  have hD : isCayley (g₁ * g₂) := isCayley_of_inGraves (inGraves_mul hg₁ hg₂)
  rw [hx', hy']
  simp only [mul_add, add_mul]
  repeat first
    | exact hA | exact hB | exact hC | exact hD | refine isCayley_add ?_ ?_

/-- The chosen Cayley order, bundled as a `Subring` of the nonassociative ring
`octonions ℚ`. Its carrier is exactly `isCayley`. -/
def cayleyIntegers : Subring (octonions ℚ) where
  carrier := {x | isCayley x}
  zero_mem' := isCayley_zero
  one_mem' := isCayley_one
  add_mem' := fun hx hy => isCayley_add hx hy
  neg_mem' := fun hx => isCayley_neg hx
  mul_mem' := fun hx hy => isCayley_mul hx hy

end Octonion


