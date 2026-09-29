-- Prove2me | Definitions.Def_HahnSeries_RamificationBound
-- name    : HahnSeries_RamificationBound
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/46a98065-ba27-5e49-92c5-717ae9810d43
-- title:
--   Ramification bounds and e-ramified Puiseux subfields of Hahn series
-- statement:
--   Over a field $K$, the Hahn series field $\mathrm{HahnSeries}\ \mathbb{Q}\ K$ plays the role of the field of Puiseux series $K((t^{\mathbb Q}))$, and this module records the apparatus for exponents with denominator dividing a fixed natural number $e$. First, `ramScale e` is the additive monoid homomorphism $\mathbb Z \to \mathbb Q$ given by $k \mapsto k/e$ (so, by the convention $k/0 = 0$, it is the zero map when $e = 0$); `ramScale_apply` records its value, `ramScale_injective` states that it is injective when $e > 0$, and `ramScale_le_iff` states that for $e > 0$ it reflects and preserves the order, $k/e \le l/e \iff k \le l$. Using these two facts, `puiseuxRamEmb` is the ring homomorphism $\mathrm{HahnSeries}\ \mathbb Z\ K \to \mathrm{HahnSeries}\ \mathbb Q\ K$ obtained by reindexing the exponent group along $k \mapsto k/e$, that is, the embedding $K((s)) \hookrightarrow K((t^{\mathbb Q}))$ sending $s$ to $t^{1/e}$.
--
--   Second, `HasRamBound e y` is the predicate on a Hahn series $y$ with rational exponents asserting that its support is contained in the image of $k \mapsto k/e$, i.e. that all exponents occurring in $y$ lie in $\tfrac1e\mathbb Z$; for $e = 0$ this reads as support contained in $\{0\}$. Third, for $e > 0$, `puiseuxRamSubfield K he` is the subfield of $\mathrm{HahnSeries}\ \mathbb Q\ K$ given by the field range of `puiseuxRamEmb`, i.e. $K((t^{1/e}))$ realised inside $K((t^{\mathbb Q}))$. The definition is by image, not by the support condition: the identification of this subfield with the set of series satisfying `HasRamBound e` is a separate assertion and is not built into the definitions here.
--
--   **Relation to Mathlib.** The ambient objects are Mathlib's `HahnSeries` and its exponent-reindexing ring homomorphism `HahnSeries.embDomainRingHom`; the scaling map `ramScale`, the ramification-bound predicate and the $e$-ramified subfield are the project's own notions.
--
--   **Where it is used.** These definitions provide the series-theoretic language for Puiseux expansions of bounded ramification index, used in the treatment of the $j$-line covering by modular curves, where local branches have ramification index dividing $3$ above $j=0$, dividing $2$ above $j=1728$, and $1$ elsewhere.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HahnSeries_RamificationBound.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace HahnSeries

variable {K : Type*} [Field K]

def ramScale (e : ℕ) : ℤ →+ ℚ where
  toFun k := (k : ℚ) / e
  map_zero' := by simp
  map_add' a b := by simp only [Int.cast_add]; rw [add_div]

@[simp] theorem ramScale_apply (e : ℕ) (k : ℤ) : ramScale e k = (k : ℚ) / e := rfl

theorem ramScale_injective {e : ℕ} (he : 0 < e) : Function.Injective (ramScale e) := by
  intro a b hab
  have he' : (e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  simp only [ramScale_apply, div_eq_div_iff he' he'] at hab
  exact_mod_cast mul_right_cancel₀ he' hab

theorem ramScale_le_iff {e : ℕ} (he : 0 < e) (a b : ℤ) :
    ramScale e a ≤ ramScale e b ↔ a ≤ b := by
  have he' : (0 : ℚ) < e := Nat.cast_pos.mpr he
  simp only [ramScale_apply, div_le_div_iff_of_pos_right he', Int.cast_le]

def puiseuxRamEmb {e : ℕ} (he : 0 < e) : HahnSeries ℤ K →+* HahnSeries ℚ K :=
  HahnSeries.embDomainRingHom (ramScale e) (ramScale_injective he) (ramScale_le_iff he)

def HasRamBound (e : ℕ) (y : HahnSeries ℚ K) : Prop :=
  y.support ⊆ Set.range (fun k : ℤ => (k : ℚ) / e)

variable (K) in

def puiseuxRamSubfield {e : ℕ} (he : 0 < e) : Subfield (HahnSeries ℚ K) :=
  (puiseuxRamEmb (K := K) he).fieldRange

end HahnSeries

end


