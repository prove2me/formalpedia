-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Time_Accuracy
-- name    : BCFGJPSSV26_Stable_Time_Accuracy
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:13:11.565605+00:00
-- url     : https://prove2.me/theorems/8fe5cb28-6da6-49d5-aa28-c6b6031d8fd1
-- title:
--   BCFGJPSSV26.Stable.Time.Accuracy — The accuracy as an input
-- statement:
--   This is module `BCFGJPSSV26.Stable.Time.Accuracy` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The algorithm of Theorem 1.3 reads the accuracy `ε = p/q` (in lowest terms, `q ≥ 1`) in binary,
--   and runs with the parameter `N = 2^(g + 8)` (`BCFGJPSSV26.Stable.accN`), where
--   `g = size q - (size p + 1)` (truncated) for `p ≥ 0` and `g = 0` for `p < 0`, with `size` the
--   number of binary digits:
--
--   * `N ≥ 256` (`BCFGJPSSV26.Stable.le_accN`);
--   * `1/ε < N` for `ε > 0` (`BCFGJPSSV26.Stable.inv_lt_accN`), since `q < 2^(size q)` and
--     `2^(size p) ≤ 2 p`;
--   * `N ≤ 256 (⌈1/ε⌉ + 1)` for every `ε` (`BCFGJPSSV26.Stable.accN_le`), since
--     `2^(size q - 1) ≤ q` and `p < 2^(size p)`.
--
--   Only the numbers of binary digits enter, so `N` is computed in time linear in the encoding of `ε`
--   plus a polynomial in `N` (`BCFGJPSSV26.Stable.exists_accN_inO`): the sign of `p` is the first bit
--   of its encoding, the length of that encoding is computed in unary, and the digits of `q` beyond
--   that length are a suffix (`Turing.MultiTapeTM.ComputableInO.drop'`), all in linear time; their
--   number `g` and `2^(g + 8)` in unary take time polynomial in `N`. The encoding of `ε` may be long
--   while `1/ε` is small, and the time bound allows only time linear in it there
--   (`BCFGJPSSV26.RunsInTime`); `⌈1/ε⌉` itself would need a division.
--
--   Also the arithmetic of composing machines: polynomial-time certificates within `c (|a| + 1)^d`
--   (`BCFGJPSSV26.Stable.exists_inO_pow`), composed on inputs of length `O(W)` into a bound `Φ ≥ W^E`
--   (`BCFGJPSSV26.Stable.comp_pow`).
--
--   **Contents.** The module is published as a whole: 16 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.exists_accN_inO` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Time_Accuracy`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Time/Accuracy.lean

module

public import Definitions.Def_BuhaiPapers_Background_BlackBox
public import Definitions.Def_BuhaiPapers_Background_Encoding
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Rat.Floor

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Time.Accuracy` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The accuracy as an input

The algorithm of Theorem 1.3 reads the accuracy `ε = p/q` (in lowest terms, `q ≥ 1`) in binary,
and runs with the parameter `N = 2^(g + 8)` (`BCFGJPSSV26.Stable.accN`), where
`g = size q - (size p + 1)` (truncated) for `p ≥ 0` and `g = 0` for `p < 0`, with `size` the
number of binary digits:

* `N ≥ 256` (`BCFGJPSSV26.Stable.le_accN`);
* `1/ε < N` for `ε > 0` (`BCFGJPSSV26.Stable.inv_lt_accN`), since `q < 2^(size q)` and
  `2^(size p) ≤ 2 p`;
* `N ≤ 256 (⌈1/ε⌉ + 1)` for every `ε` (`BCFGJPSSV26.Stable.accN_le`), since
  `2^(size q - 1) ≤ q` and `p < 2^(size p)`.

Only the numbers of binary digits enter, so `N` is computed in time linear in the encoding of `ε`
plus a polynomial in `N` (`BCFGJPSSV26.Stable.exists_accN_inO`): the sign of `p` is the first bit
of its encoding, the length of that encoding is computed in unary, and the digits of `q` beyond
that length are a suffix (`Turing.MultiTapeTM.ComputableInO.drop'`), all in linear time; their
number `g` and `2^(g + 8)` in unary take time polynomial in `N`. The encoding of `ε` may be long
while `1/ε` is small, and the time bound allows only time linear in it there
(`BCFGJPSSV26.RunsInTime`); `⌈1/ε⌉` itself would need a division.

Also the arithmetic of composing machines: polynomial-time certificates within `c (|a| + 1)^d`
(`BCFGJPSSV26.Stable.exists_inO_pow`), composed on inputs of length `O(W)` into a bound `Φ ≥ W^E`
(`BCFGJPSSV26.Stable.comp_pow`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Turing.MultiTapeTM
open Encoding (encRat)

/-! ### Certificates within powers -/

theorem exists_le_pow' {β : Type} {size u : β → ℕ} (h : PolyBounded size u) :
    ∃ c d, ∀ a, u a ≤ c * (size a + 1) ^ d := by
  obtain ⟨bound, hb, hu⟩ := h
  obtain ⟨c, d, hcd⟩ := Cslib.polynomiallyBounded_iff_le.1 hb
  exact ⟨c, d, fun a ↦ (hu a).trans (hcd _)⟩

/-- A polynomial-time certificate, within `c (|a| + 1)^d` time and space. -/
theorem exists_inO_pow {α β : Type} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} (h : ComputableInPolyTime f encIn encOut) :
    ∃ c d : ℕ, ComputableInO f encIn encOut (fun a ↦ c * ((encIn a).length + 1) ^ d)
      (fun a ↦ c * ((encIn a).length + 1) ^ d) := by
  obtain ⟨T, S, hT, hS, hO⟩ := h.exists_computableInO
  obtain ⟨cT, dT, hT'⟩ := exists_le_pow' hT
  obtain ⟨cS, dS, hS'⟩ := exists_le_pow' hS
  have hp : ∀ a, ∀ c d, c * ((encIn a).length + 1) ^ d ≤
      (cT + cS + c) * ((encIn a).length + 1) ^ (dT + dS + d) := fun a c d ↦
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  refine ⟨cT + cS, dT + dS, hO.mono_le (fun a ↦ (hT' a).trans ?_) (fun a ↦ (hS' a).trans ?_)⟩
  · exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  · exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))

/-- **Composing with a polynomial-time certificate**: on inputs of length `O(W)`, it adds
`O(W^d) ≤ O(Φ)` when `W^E ≤ Φ` and `d ≤ E`. -/
theorem comp_pow {α β γ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {f : β → γ} {g : α → β} {c d E k : ℕ} {W Φ : α → ℕ}
    (hf : ComputableInO f encMid encOut (fun b ↦ c * ((encMid b).length + 1) ^ d)
      (fun b ↦ c * ((encMid b).length + 1) ^ d))
    (hg : ComputableInO g encIn encMid Φ Φ) (hd : d ≤ E) (hW : ∀ a, 1 ≤ W a)
    (hlen : ∀ a, (encMid (g a)).length + 1 ≤ k * W a) (hΦ : ∀ a, W a ^ E ≤ Φ a) :
    ComputableInO (fun a ↦ f (g a)) encIn encOut Φ Φ := by
  have hb : ∀ a, Φ a + c * ((encMid (g a)).length + 1) ^ d ≤ (1 + c * k ^ d) * (Φ a + 1) := by
    intro a
    have h1 : ((encMid (g a)).length + 1) ^ d ≤ k ^ d * Φ a :=
      calc ((encMid (g a)).length + 1) ^ d ≤ (k * W a) ^ d := Nat.pow_le_pow_left (hlen a) _
        _ = k ^ d * W a ^ d := mul_pow _ _ _
        _ ≤ k ^ d * Φ a :=
          Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (hW a) hd).trans (hΦ a))
    have h2 := Nat.mul_le_mul_left c h1
    have e : (1 + c * k ^ d) * (Φ a + 1) = Φ a + 1 + c * k ^ d * Φ a + c * k ^ d := by ring
    have : c * (k ^ d * Φ a) = c * k ^ d * Φ a := by ring
    linarith [Nat.zero_le (c * k ^ d)]
  exact (hf.comp' hg).mono _ hb hb

/-! ### The parameter -/

/-- The sign bit of the numerator of `ε`, as a number: `1` if `ε < 0`, else `0`. -/
def sgnBit (ε : ℚ) : ℕ := ((Encoding.encInt ε.num).map Universal.eBit).headD 0

/-- The digits of the denominator of `ε` beyond the length of the encoding of its numerator, as
numbers `0, 1`; none if `ε < 0`. -/
def gapList (ε : ℚ) : List ℕ :=
  if sgnBit ε = 0 then ((encNat ε.den).map Universal.eBit).drop (Encoding.encInt ε.num).length
  else []

/-- **The parameter `N = 2^(g + 8)` for the accuracy `ε`**, with `g` the length of
`BCFGJPSSV26.Stable.gapList`. -/
def accN (ε : ℚ) : ℕ := 2 ^ ((gapList ε).length + 8)

theorem sgnBit_eq_zero (ε : ℚ) : sgnBit ε = 0 ↔ 0 ≤ ε.num := by
  unfold sgnBit
  change ((decide (ε.num < 0) :: encNat ε.num.natAbs).map Universal.eBit).headD 0 = 0 ↔ _
  rw [List.map_cons, List.headD_cons]
  by_cases h : ε.num < 0
  · simp only [h, decide_true]
    change Bool.toNat true = 0 ↔ _
    simp only [Bool.toNat_true, one_ne_zero, false_iff, not_le]
    exact h
  · simp only [h, decide_false]
    change Bool.toNat false = 0 ↔ _
    simp only [Bool.toNat_false, true_iff]
    omega

theorem length_encNat (n : ℕ) : (encNat n).length = n.size := Nat.size_eq_bits_len n

theorem length_encInt (z : ℤ) : (Encoding.encInt z).length = z.natAbs.size + 1 := by
  change (decide (z < 0) :: encNat z.natAbs).length = _
  rw [List.length_cons, length_encNat]

/-- The length `g` of `BCFGJPSSV26.Stable.gapList` for `ε ≥ 0`. -/
theorem length_gapList {ε : ℚ} (h : 0 ≤ ε.num) :
    (gapList ε).length = ε.den.size - (ε.num.natAbs.size + 1) := by
  unfold gapList
  rw [if_pos ((sgnBit_eq_zero ε).2 h), List.length_drop, List.length_map, length_encNat,
    length_encInt]

theorem gapList_le_one (ε : ℚ) : ∀ c ∈ gapList ε, c ≤ 1 := by
  intro c hc
  unfold gapList at hc
  split_ifs at hc
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop hc)
    exact eBit_le_one b
  · simp at hc

theorem le_accN (ε : ℚ) : 256 ≤ accN ε := by
  unfold accN
  rw [pow_add]
  exact Nat.le_mul_of_pos_left _ (by positivity)

theorem two_pow_size_le_two_mul {p : ℕ} (hp : 0 < p) : 2 ^ p.size ≤ 2 * p := by
  have hs : 0 < p.size := Nat.size_pos.2 hp
  have h : 2 ^ (p.size - 1) ≤ p := Nat.lt_size.1 (by omega)
  have : 2 ^ p.size = 2 * 2 ^ (p.size - 1) := by rw [← pow_succ', Nat.sub_add_cancel hs]
  omega

/-- `1/ε = q/p` for `ε = p/q > 0`. -/
theorem one_div_eq {ε : ℚ} (hε : 0 < ε) :
    1 / ε = (ε.den : ℚ) / (ε.num.natAbs : ℚ) := by
  have hnum : 0 < ε.num := Rat.num_pos.2 hε
  have hp : ((ε.num.natAbs : ℕ) : ℚ) = (ε.num : ℚ) := by
    rw [Nat.cast_natAbs, abs_of_pos hnum]
  rw [hp]
  conv_lhs => rw [← Rat.num_div_den ε]
  rw [one_div_div]

/-- **`1/ε < N`** for `ε > 0`. -/
theorem inv_lt_accN {ε : ℚ} (hε : 0 < ε) : 1 / ε < accN ε := by
  have hnum : 0 < ε.num := Rat.num_pos.2 hε
  set p := ε.num.natAbs with hpdef
  set q := ε.den
  have hp : 0 < p := Int.natAbs_pos.2 hnum.ne'
  set g := (gapList ε).length with hg
  have hgq : g = q.size - (p.size + 1) := length_gapList hnum.le
  have hq : q < 2 ^ (g + 3) * p := by
    have h1 : q < 2 ^ q.size := Nat.lt_size_self q
    have h2 : 2 ^ q.size ≤ 2 ^ (g + 1) * 2 ^ p.size := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 := two_pow_size_le_two_mul hp
    have h4 : 2 ^ (g + 1) * 2 ^ p.size ≤ 2 ^ (g + 1) * (2 * p) := Nat.mul_le_mul_left _ h3
    have h5 : 2 ^ (g + 1) * (2 * p) ≤ 2 ^ (g + 3) * p :=
      calc 2 ^ (g + 1) * (2 * p) ≤ 2 ^ (g + 1) * (4 * p) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 ^ (g + 3) * p := by ring
    omega
  have hq' : q < accN ε * p := by
    unfold accN
    rw [← hg]
    calc q < 2 ^ (g + 3) * p := hq
      _ ≤ 2 ^ (g + 8) * p := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [one_div_eq hε, div_lt_iff₀ (by exact_mod_cast hp)]
  exact_mod_cast hq'

/-- **`N ≤ 256 (⌈1/ε⌉ + 1)`.** -/
theorem accN_le (ε : ℚ) : accN ε ≤ 256 * (⌈1 / ε⌉₊ + 1) := by
  unfold accN
  rw [pow_add, mul_comm]
  refine Nat.mul_le_mul (by norm_num) ?_
  set g := (gapList ε).length with hg
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · rw [h0]
    omega
  have hnum : 0 ≤ ε.num := by
    by_contra h
    have : gapList ε = [] := by
      unfold gapList
      rw [if_neg (fun h' ↦ h ((sgnBit_eq_zero ε).1 h'))]
    rw [hg, this] at hpos
    simp at hpos
  have hgq : g = ε.den.size - (ε.num.natAbs.size + 1) := length_gapList hnum
  have hε : 0 < ε := by
    rcases hnum.lt_or_eq with h | h
    · exact Rat.num_pos.1 h
    · exfalso
      have h0 : ε = 0 := Rat.num_eq_zero.1 h.symm
      subst h0
      simp at hgq
      omega
  have hp : 0 < ε.num.natAbs := Int.natAbs_pos.2 (Rat.num_pos.2 hε).ne'
  set p := ε.num.natAbs
  set q := ε.den
  have hq : 2 ^ g * p < q := by
    have h1 : 2 ^ (q.size - 1) ≤ q := Nat.lt_size.1 (by omega)
    have h2 : p < 2 ^ p.size := Nat.lt_size_self p
    calc 2 ^ g * p < 2 ^ g * 2 ^ p.size := Nat.mul_lt_mul_of_pos_left h2 (by positivity)
      _ = 2 ^ (g + p.size) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (q.size - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ q := h1
  have hlt : ((2 ^ g : ℕ) : ℚ) < 1 / ε := by
    rw [one_div_eq hε, lt_div_iff₀ (by exact_mod_cast hp)]
    exact_mod_cast hq
  have hc : ((2 ^ g : ℕ) : ℚ) < ⌈1 / ε⌉₊ := hlt.trans_le (Nat.le_ceil _)
  have : 2 ^ g < ⌈1 / ε⌉₊ := by exact_mod_cast hc
  omega

/-! ### Computing the parameter -/

end BCFGJPSSV26.Stable


