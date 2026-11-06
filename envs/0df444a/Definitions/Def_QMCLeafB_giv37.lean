-- Prove2me | Definitions.Def_QMCLeafB_giv37
-- name    : QMCLeafB_giv37
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:31:30.472101+00:00
-- url     : https://prove2.me/theorems/3df04ce1-b1ab-48bf-9caf-5c68e847dff6
-- title:
--   QMCLeafB giv37
-- statement:
--   # `Check_giv37_m7` — phase 37, member m7, direction `gate-invariance`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_asm35
import Definitions.Def_QMCLeafB_crux_m1
/-
# `Check_giv37_m7` — phase 37, member m7, direction `gate-invariance`

## What is decided here

The phase-37 argument says: give the programme an ok test that *is* membership at the round's
centre, then either (A) some round reports `ok` — and the bit is true with `hok` discharged at that
round's own centre — or (B) every round reports a non-member, so each round's oracle cut is a
genuine separator **at its own rational centre**, and "the only gap to `hcut` (stated at `Cat k`) is
m4/ph36's PRICE `enc = n . (flat cX − Cat k)`".  Then two candidate fixes: (B1) make the centre the
accumulated point so `enc = 0`, or (B2) bound the price by the ledger.

This file *verifies or refutes each step of (B)* and reaches a negative verdict on the fork:

* **(B)'s price is not a translation cost — it is the support value of the body at the accumulated
  point, read at the cut's own normal.**  `price_ub` + `price_eq_support_at_witness`:
  for a `RelaxCut` at `cX` whose margin is realised at a body point `z₀`,
  `margin − enc = ⟨normal, a − z₀⟩`, i.e. exactly the quantity `hcut` bounds.  So
  *paying the price is hcut* — nothing is re-anchored, nothing is reduced.

* **(B1) cannot be what its author says it is.**  Making the centre the accumulated point makes
  `enc = 0`, hence the bridge requires `del ≥ margin > 0` — *not* `del ≡ 0`
  (`del_pos_of_own_centre`).  `del ≡ 0` needs a normal that actually *separates* `Cat k` from the
  body (`del_zero_iff_separating`), a strictly stronger object (m6/ph35's `shallowCut_of_separating`).
  So "centre = `Cat k` ⟹ price 0 ⟹ `ShallowCut` with `del ≡ 0`" is a non-sequitur:
  price `= 0` and support-value `= 0` are different statements, and `margin_pos` separates them.

* **The price does not depend on the centre at all** (`price_indep_centre`): any two exact
  presentations of the same normal give the same price.  So no re-coding of the state
  (B1 in its literal sense) can move the price; it only splits it into `margin` and `enc` that
  cancel.  **The fork is a presentation, not a choice.**

* **(B2) is the shallow-cut condition, exactly.**  With the record's own ledger
  (`hcheck`, `hle`), the price being payable forces `(price)² ≤ rmax² σ`, i.e.
  `|⟨normal, Cat k − z₀⟩| ≤ rmax·√σ` — the accumulated centre is shallow in the normal's direction.
  That is `ShallowCut` / `SupportSlot` — the campaign's existing single obligation — and it is
  centre-independent, so B1 and B2 are the same proposition, not two.

* **m1's `hctr_one_forces_square` is a satisfiable side condition, not an obstruction**
  (`hctr_one_satisfiable`): at the engine's own init shape with the coordinate normal and `σ₀ = 1`,
  the accumulated centre after one round IS the flattening of a rational matrix.  So the
  square condition does not bind B1 at `k = 1`; what kills B1 is the support identity above.

* **Both horns' premises check out, with one repair each** (§11): horn (B) is definitional at the
  MERGED oracle (`relaxMem_or_cut`); it would NOT be at the older m4 oracle (`relaxOk_or_cut`,
  which reports `RelaxOk` — the trace-high ledger — at a trace-high non-member and no cut at all).
  Horn (A) is definitional up to symmetry: `HokSlot` demands `cXᵀ = cX` and `RelaxMem` does not
  mention symmetry, so it needs the free symmetrisation `(cX + cXᵀ)/2` (`hornA_premise`).

**Consequence.**  The collar (m7/ph36 `collar_dossier`) is untouched: on the collar case (A) is
whatever the gate says, and case (B) delivers exactly the support inequality at `Cat k` that
`SelfRec` already needed.  The phase's dichotomy is *correct but empty* — it re-derives the
obligation it was meant to discharge.

Discipline: `set_option autoImplicit false`; every `#print axioms` is exactly
`[propext, Classical.choice, Quot.sound]`.  No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

namespace QMCLeafB.Giv37M7

open QMCLeafB.RelaxOracle
open QMCLeafB.EngineIterates

/-! ## 0.  Presentation of a cut in the flat shape that `hcut` speaks -/

/-- The cut's normal in the flat (`Fin (n*n)`) shape — the vector `hcut` pairs with. -/
noncomputable def cutNR {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (C : RelaxCut A cX u δ) : Fin (n * n) → ℝ := fun k => ((flatQ C.normal k : ℚ) : ℝ)

/-- A rational matrix centre in the flat shape. -/
noncomputable def centreR {n : ℕ} (cX : Matrix (Fin n) (Fin n) ℚ) : Fin (n * n) → ℝ :=
  QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat cX)

/-- The signed translation price of m4/ph36: `n . (flat cX − a)`. -/
noncomputable def priceA {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (C : RelaxCut A cX u δ) (a : Fin (n * n) → ℝ) : ℝ :=
  cutNR C ⬝ᵥ (centreR cX - a)

/-! ## 1.  Dot-product arithmetic -/

theorem dot_sub_add {N : ℕ} (w a b c : Fin N → ℝ) :
    w ⬝ᵥ (a - c) = w ⬝ᵥ (a - b) + w ⬝ᵥ (b - c) := by
  rw [← dotProduct_add]
  congr 1
  abel

theorem dot_neg_sub {N : ℕ} (w a b : Fin N → ℝ) : w ⬝ᵥ (a - b) = -(w ⬝ᵥ (b - a)) := by
  rw [dotProduct_sub, dotProduct_sub]
  ring

theorem dot_zero_right {N : ℕ} (w : Fin N → ℝ) : w ⬝ᵥ (0 : Fin N → ℝ) = 0 := by
  simp [dotProduct]

/-! ## 2.  (B): the price is an upper bound for the body's support value at `a`

This is the mirror of m4/ph36's `hcut_of_relaxCut_price`, and it is what makes the fork
presentational: the price is *not* a translation cost, it is the support value. -/

/-- **(B), first half.**  For every point `z` of the relaxation, the support value of the body at
`a` in the cut's own normal is at most the price.  No rationality, no `hcut`, no trajectory: one
split of a dot product. -/
theorem price_ub {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {M : ℝ}
    (C : RelaxCut A cX u δ) (a : Fin (n * n) → ℝ) :
    ∀ z : Fin (n * n) → ℝ,
      z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
          ((δ : ℚ) : ℝ) M →
      cutNR C ⬝ᵥ (a - z) ≤ ((C.margin : ℚ) : ℝ) - priceA C a := by
  intro z hz
  have h := C.separates_ball M z hz
  have h' : -(((C.margin : ℚ)) : ℝ) ≤ cutNR C ⬝ᵥ (z - centreR cX) := h
  have h1 : cutNR C ⬝ᵥ (a - z) = cutNR C ⬝ᵥ (a - centreR cX) + cutNR C ⬝ᵥ (centreR cX - z) :=
    dot_sub_add (cutNR C) a (centreR cX) z
  have h2 : cutNR C ⬝ᵥ (a - centreR cX) = -priceA C a := by
    rw [priceA, dot_neg_sub]
  have h3 : cutNR C ⬝ᵥ (centreR cX - z) = -(cutNR C ⬝ᵥ (z - centreR cX)) :=
    dot_neg_sub (cutNR C) (centreR cX) z
  linarith

#print axioms QMCLeafB.Giv37M7.price_ub

/-- **(B), second half — the price is the support value, not a cost.**  If the cut's margin is
realised at a body point `z₀` (`margin ≤ ⟨normal, cX − z₀⟩`, which for the shelf's exact-margin
branches is an identity), then the price is *exactly* the support value at `a` in that normal. -/
theorem price_eq_support_at_witness {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {M : ℝ}
    (C : RelaxCut A cX u δ) {a z₀ : Fin (n * n) → ℝ}
    (hz₀ : z₀ ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
          ((δ : ℚ) : ℝ) M)
    (hex : ((C.margin : ℚ) : ℝ) ≤ cutNR C ⬝ᵥ (centreR cX - z₀)) :
    ((C.margin : ℚ) : ℝ) - priceA C a = cutNR C ⬝ᵥ (a - z₀) := by
  have hub := price_ub C a z₀ hz₀
  have h1 : cutNR C ⬝ᵥ (a - z₀) = cutNR C ⬝ᵥ (a - centreR cX) + cutNR C ⬝ᵥ (centreR cX - z₀) :=
    dot_sub_add (cutNR C) a (centreR cX) z₀
  have h2 : cutNR C ⬝ᵥ (a - centreR cX) = -priceA C a := by
    rw [priceA, dot_neg_sub]
  linarith

#print axioms QMCLeafB.Giv37M7.price_eq_support_at_witness

/-! ## 3.  The price does not see the centre: (B1) cannot move it -/

/-- **The fork is a presentation.**  Two exact presentations of the same normal — at *any* two
rational centres — charge the same price.  So no choice of state coding, normalisation or
anchor (in particular B1's "centre = the accumulated point") can reduce the price; it only splits
it into a margin and a translation that cancel. -/
theorem price_indep_centre {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {M : ℝ}
    {cX₁ cX₂ : Matrix (Fin n) (Fin n) ℚ}
    (C₁ : RelaxCut A cX₁ u δ) (C₂ : RelaxCut A cX₂ u δ)
    (hnorm : C₂.normal = C₁.normal)
    {a z₁ z₂ : Fin (n * n) → ℝ}
    (hz₁ : z₁ ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
          ((δ : ℚ) : ℝ) M)
    (hz₂ : z₂ ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
          ((δ : ℚ) : ℝ) M)
    (hex₁ : ((C₁.margin : ℚ) : ℝ) ≤ cutNR C₁ ⬝ᵥ (centreR cX₁ - z₁))
    (hex₂ : ((C₂.margin : ℚ) : ℝ) ≤ cutNR C₂ ⬝ᵥ (centreR cX₂ - z₂)) :
    ((C₁.margin : ℚ) : ℝ) - priceA C₁ a = ((C₂.margin : ℚ) : ℝ) - priceA C₂ a := by
  have hw : cutNR C₂ = cutNR C₁ := by
    funext k
    simp only [cutNR]
    rw [hnorm]
  have e₁ : ((C₁.margin : ℚ) : ℝ) - priceA C₁ a = cutNR C₁ ⬝ᵥ (a - z₁) :=
    price_eq_support_at_witness C₁ hz₁ hex₁
  have e₂ : ((C₂.margin : ℚ) : ℝ) - priceA C₂ a = cutNR C₂ ⬝ᵥ (a - z₂) :=
    price_eq_support_at_witness C₂ hz₂ hex₂
  have u₁ := price_ub C₁ a z₂ hz₂
  have u₂ := price_ub C₂ a z₁ hz₁
  rw [hw] at e₂ u₂
  linarith

#print axioms QMCLeafB.Giv37M7.price_indep_centre

/-! ## 4.  The ledger, and what paying the price costs

`RunParts.hcheck` is `(del k)^2 ≤ (rho k)^2 * σ_k` and `RunParts.hle` is `rho k ≤ rmax`.  The two
lemmas below are the whole arithmetic content of "the depth pays the price". -/

theorem sq_le_of_bounds {e del ρ σ : ℝ} (hdel0 : 0 ≤ del) (he : e ≤ del) (hneg : -del ≤ e)
    (hchk : del ^ 2 ≤ ρ ^ 2 * σ) : e ^ 2 ≤ ρ ^ 2 * σ := by
  have habs : |e| ≤ del := abs_le.mpr ⟨hneg, he⟩
  have hsq : e ^ 2 = |e| ^ 2 := (sq_abs e).symm
  rw [hsq]
  exact le_trans (pow_le_pow_left₀ (abs_nonneg e) habs 2) hchk

#print axioms QMCLeafB.Giv37M7.sq_le_of_bounds

/-- **The ledger, at the ceiling.**  A record's own data forces the price's square to fit inside
`rmax ^ 2 * σ`: the depth is not a separate budget. -/
theorem ledger_depth_le_rmax {e del ρ σ rmax : ℝ} (hσ : 0 ≤ σ) (hdel0 : 0 ≤ del) (he : e ≤ del)
    (hneg : -del ≤ e) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ rmax) (hchk : del ^ 2 ≤ ρ ^ 2 * σ) :
    e ^ 2 ≤ rmax ^ 2 * σ := by
  have h1 : e ^ 2 ≤ ρ ^ 2 * σ := sq_le_of_bounds hdel0 he hneg hchk
  have h2 : ρ ^ 2 ≤ rmax ^ 2 := pow_le_pow_left₀ hρ0 hρ 2
  exact le_trans h1 (mul_le_mul_of_nonneg_right h2 hσ)

#print axioms QMCLeafB.Giv37M7.ledger_depth_le_rmax

/-! ## 5.  (B1) is not what its author says: `price = 0` is not `del = 0`

The phase-37 derivation claims: make the recorded centre the accumulated point, then the price is
`0`, and `shallowCut_of_separating` (m6/ph35) gives `ShallowCut` with `del ≡ 0`.

The first two clauses are true and are `price_zero_at_own_centre`.  The consequence is false:
the bridge is `margin − price ≤ del`, so `price = 0` gives `del ≥ margin`, and `margin_pos` makes
that strictly positive.  A zero slack needs a normal that *separates* the accumulated point from the
body, which is a different object (and strictly stronger).  `del_pos_of_own_centre` is the receipt. -/

/-- The price vanishes at the configuration (B1) proposes — by definition, since `enc = 0`. -/
theorem price_zero_at_own_centre {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (C : RelaxCut A cX u δ) :
    priceA C (centreR cX) = 0 := by
  rw [priceA, sub_self, dot_zero_right]

#print axioms QMCLeafB.Giv37M7.price_zero_at_own_centre

/-- **(B1) cannot deliver `del ≡ 0`.**  At the configuration whose price is `0`, any slack that pays
the price is strictly positive — indeed at least the cut's own margin. -/
theorem del_pos_of_own_centre {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (C : RelaxCut A cX u δ) {a : Fin (n * n) → ℝ} {del : ℚ} (ha : a = centreR cX)
    (hprice : ((C.margin : ℚ) : ℝ) - priceA C a ≤ ((del : ℚ) : ℝ)) :
    0 < del := by
  subst ha
  rw [price_zero_at_own_centre, sub_zero] at hprice
  have hm : (0 : ℝ) < ((C.margin : ℚ) : ℝ) := by exact_mod_cast C.margin_pos
  have : (0 : ℝ) < ((del : ℚ) : ℝ) := lt_of_lt_of_le hm hprice
  exact_mod_cast this

#print axioms QMCLeafB.Giv37M7.del_pos_of_own_centre

/-- **(B1) implies (B2), and (B2) is the shallow-cut condition.**  At the configuration (B1)
proposes, the ledger forces the margin — the support value of the body at the accumulated point in
the cut's normal — to be at most `rmax * √σ`.  So (B1) is not an alternative to (B2): it is a
sub-case of it, and both are `ShallowCut`. -/
theorem b1_ledger_forces_shallow {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (C : RelaxCut A cX u δ) {del ρ σ rmax : ℝ} (hσ : 0 ≤ σ)
    (hdel0 : 0 ≤ del)
    (hprice : ((C.margin : ℚ) : ℝ) - priceA C (centreR cX) ≤ del)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ rmax) (hchk : del ^ 2 ≤ ρ ^ 2 * σ) :
    ((C.margin : ℚ) : ℝ) ^ 2 ≤ rmax ^ 2 * σ := by
  have hm : (0 : ℝ) < ((C.margin : ℚ) : ℝ) := by exact_mod_cast C.margin_pos
  have hpz : ((C.margin : ℚ) : ℝ) - priceA C (centreR cX) = ((C.margin : ℚ) : ℝ) := by
    rw [price_zero_at_own_centre, sub_zero]
  have hneg : -del ≤ ((C.margin : ℚ) : ℝ) := by linarith
  exact ledger_depth_le_rmax (e := ((C.margin : ℚ) : ℝ)) (del := del) (ρ := ρ) (σ := σ)
    (rmax := rmax) hσ hdel0 (by linarith [hpz]) hneg hρ0 hρ hchk

#print axioms QMCLeafB.Giv37M7.b1_ledger_forces_shallow

/-! ## 6.  The headline: (B)'s price regime IS `hcut`

The two directions, back to back.  With the cut's margin realised at a body point `z₀` (which is
what the shelf's exact-margin branches give), *"the price fits in the slack"* and *"`hcut` holds at
the accumulated point with that slack"* are the same proposition.  So the membership gate re-derives
the leaf's existing obligation and reduces nothing. -/

/-- **price ⟹ hcut** (m4/ph36's bridge, in this file's notation; the same one-line split). -/
theorem hcut_of_price_bound {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {M : ℝ}
    (C : RelaxCut A cX u δ) (a : Fin (n * n) → ℝ) {del : ℚ}
    (hprice : ((C.margin : ℚ) : ℝ) - priceA C a ≤ ((del : ℚ) : ℝ)) :
    ∀ z : Fin (n * n) → ℝ,
      z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
        ((δ : ℚ) : ℝ) M →
      -(((del : ℚ)) : ℝ) ≤ cutNR C ⬝ᵥ (z - a) := by
  intro z hz
  have h := price_ub C a z hz
  have h1 : cutNR C ⬝ᵥ (z - a) = -(cutNR C ⬝ᵥ (a - z)) := dot_neg_sub (cutNR C) z a
  rw [h1]
  linarith

#print axioms QMCLeafB.Giv37M7.hcut_of_price_bound

/-- **hcut ⟹ price** — the reverse, which is what the coordinator's derivation omits.  At a body
point where the cut's margin is realised, `hcut` at the accumulated point already swallows the
price: the translation term is not an extra cost, it IS the slack. -/
theorem price_of_hcut {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {M : ℝ}
    (C : RelaxCut A cX u δ) {a z₀ : Fin (n * n) → ℝ} {del : ℚ}
    (hz₀ : z₀ ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
          ((δ : ℚ) : ℝ) M)
    (hex : ((C.margin : ℚ) : ℝ) ≤ cutNR C ⬝ᵥ (centreR cX - z₀))
    (hcut : -(((del : ℚ)) : ℝ) ≤ cutNR C ⬝ᵥ (z₀ - a)) :
    ((C.margin : ℚ) : ℝ) - priceA C a ≤ ((del : ℚ) : ℝ) := by
  rw [price_eq_support_at_witness C hz₀ hex]
  have h1 : cutNR C ⬝ᵥ (z₀ - a) = -(cutNR C ⬝ᵥ (a - z₀)) := dot_neg_sub (cutNR C) z₀ a
  linarith

#print axioms QMCLeafB.Giv37M7.price_of_hcut

/-- **(B) does not reduce the leaf.**  Given an exact-margin cut, paying the price and `hcut` at the
accumulated point are equivalent.  Consequently the phase-37 dichotomy's horn (B) delivers exactly
`ShallowCut`, which is the obligation the campaign already had (m4/ph34, m6/ph35). -/
theorem price_iff_hcut {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {M : ℝ}
    (C : RelaxCut A cX u δ) {a z₀ : Fin (n * n) → ℝ} {del : ℚ}
    (hz₀ : z₀ ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
          ((δ : ℚ) : ℝ) M)
    (hex : ((C.margin : ℚ) : ℝ) ≤ cutNR C ⬝ᵥ (centreR cX - z₀)) :
    ((((C.margin : ℚ) : ℝ) - priceA C a ≤ ((del : ℚ) : ℝ))
      ↔ (∀ z : Fin (n * n) → ℝ,
          z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
            ((δ : ℚ) : ℝ) M →
          -(((del : ℚ)) : ℝ) ≤ cutNR C ⬝ᵥ (z - a))) := by
  constructor
  · exact hcut_of_price_bound C a
  · intro h
    exact price_of_hcut C hz₀ hex (h z₀ hz₀)

#print axioms QMCLeafB.Giv37M7.price_iff_hcut

/-! ## 7.  m1's `hctr_one_forces_square` is a satisfiable side condition, not an obstruction

`hctr_one_forces_square` (`Check_crux_m1`) says: if the accumulated engine centre after one round is
the flattening of a rational matrix, then `σ₀ = c₀ ⬝ p₀` is a square in `ℚ`.  It was read in phases
30–36 as an obstruction ("`Cat 1` is irrational").  It is not: the square condition is
*satisfiable*, and at the engine's own init shape with the coordinate normal it is satisfied
outright.  So the obstruction to (B1) is not this, and — by §3 and §5 — nothing about the coding
is the obstacle; the support identity is. -/

/-- Every rational flat vector is the flattening of a rational matrix. -/
theorem flat_castMat_surj {n : ℕ} (v : Fin (n * n) → ℚ) :
    ∃ cX : Matrix (Fin n) (Fin n) ℚ,
      QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat cX) = fun k => ((v k : ℚ) : ℝ) := by
  refine ⟨Matrix.of fun i j => v (finProdFinEquiv (i, j)), ?_⟩
  funext k
  rw [QMCLeafB.CruxM1.flat_castMat_eq]
  have h1 : QMCLeafB.RelaxOracle.flatQ (Matrix.of fun i j => v (finProdFinEquiv (i, j))) k = v k := by
    simp only [QMCLeafB.RelaxOracle.flatQ, Matrix.of_apply]
    exact congrArg v (Equiv.apply_symm_apply finProdFinEquiv k)
  show ((QMCLeafB.RelaxOracle.flatQ (Matrix.of fun i j => v (finProdFinEquiv (i, j))) k : ℚ) : ℝ)
    = ((v k : ℚ) : ℝ)
  rw [h1]

#print axioms QMCLeafB.Giv37M7.flat_castMat_surj

/-- **One round of the engine at `σ₀ = 1`.**  With the coordinate normal, the witness `1 • e₀` and
depth `0`, the accumulated centre after one round is the rational vector `(1/5) e₀`. -/
theorem cat_one_coord_one :
    QMCLeafB.EngineIterates.Cat 4 (0 : Fin 4 → ℝ) (QMCLeafB.CruxM1.coordCd 1) 1
      = fun i => (((1 / 5 : ℚ) * QMCLeafB.CruxM1.e0 i : ℚ) : ℝ) := by
  rw [QMCLeafB.CruxM1.Cat_one]
  have hs : QMCLeafB.EngineIterates.sigmaR
      (QMCLeafB.EngineIterates.cutCR (QMCLeafB.CruxM1.coordCd 1) 0)
      (QMCLeafB.EngineIterates.cutPR (QMCLeafB.CruxM1.coordCd 1) 0) = 1 := by
    rw [← QMCLeafB.EngineIterates.cast_sigmaQ, QMCLeafB.CruxM1.sigmaQ_coord]
    norm_num
  have hsq : QMCLeafB.EngineIterates.sqrtSigmaR
      (QMCLeafB.EngineIterates.cutCR (QMCLeafB.CruxM1.coordCd 1) 0)
      (QMCLeafB.EngineIterates.cutPR (QMCLeafB.CruxM1.coordCd 1) 0) = 1 := by
    rw [QMCLeafB.EngineIterates.sqrtSigmaR, hs, Real.sqrt_one]
  have hg : QMCLeafB.EngineIterates.gammaR 4 ((QMCLeafB.CruxM1.coordCd 1 0).rho : ℝ) = 1 / 5 := by
    simp only [QMCLeafB.EngineIterates.gammaR, QMCLeafB.CruxM1.coordCd]
    norm_num
  rw [hsq, hg, div_one]
  funext i
  simp only [QMCLeafB.EngineIterates.cutPR, QMCLeafB.CruxM1.coordCd, Pi.smul_apply, one_smul]
  push_cast
  ring

#print axioms QMCLeafB.Giv37M7.cat_one_coord_one

/-- **`hctr` holds at `k = 1` on a genuine trajectory.**  This is the direct refutation of the
reading of m1's `hctr_one_forces_square` as an obstruction: the transcript `coordCd 1` satisfies the
engine's witness relation at `k = 0` (`hwit_initShape`) and its accumulated centre after one round is
the flattening of `!![1/5, 0; 0, 0]`.  The square condition is met, not violated. -/
theorem hctr_one_satisfiable :
    ∃ cX : Matrix (Fin 2) (Fin 2) ℚ,
      QMCLeafB.EngineIterates.Cat 4 (0 : Fin 4 → ℝ) (QMCLeafB.CruxM1.coordCd 1) 1
        = QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat cX) := by
  obtain ⟨cX, hcX⟩ := flat_castMat_surj (n := 2) (fun i => (1 / 5 : ℚ) * QMCLeafB.CruxM1.e0 i)
  exact ⟨cX, cat_one_coord_one.trans hcX.symm⟩

#print axioms QMCLeafB.Giv37M7.hctr_one_satisfiable

/-! ## 8.  The sharpest failure of (B2), and the family form at the leaf's own centres

The phase asked: if (B2) — the price fits in the round's slack — is false, exhibit the sharpest
failure.  Here it is, with no constants: **one body point whose support value at the accumulated
centre exceeds the round's slack kills the round**, for every normal, every rational centre, every
presentation.  The price is not tunable by any of them. -/

/-- **A deep body point kills the price bound outright.**  If some point of the relaxation has
`⟨normal, a − z⟩ > del`, then no cut at any rational centre pays the price within `del` in that
normal. -/
theorem no_price_of_deep_point {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {M : ℝ}
    (C : RelaxCut A cX u δ) {a z : Fin (n * n) → ℝ} {del : ℚ}
    (hz : z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
          ((δ : ℚ) : ℝ) M)
    (hdeep : ((del : ℚ) : ℝ) < cutNR C ⬝ᵥ (a - z)) :
    ¬ (((C.margin : ℚ) : ℝ) - priceA C a ≤ ((del : ℚ) : ℝ)) := by
  intro h
  have h1 := price_ub C a z hz
  linarith

#print axioms QMCLeafB.Giv37M7.no_price_of_deep_point

/-- **The same failure in the ledger's own units.**  If a body point beats `rmax * √σ` at the
accumulated centre then the round is infeasible for every recording of that normal: the ledger
`del ^ 2 ≤ ρ ^ 2 σ` with `ρ ≤ rmax` cannot reach it. -/
theorem no_price_of_deep_rmax {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {M : ℝ}
    (C : RelaxCut A cX u δ) {a z : Fin (n * n) → ℝ} {del ρ σ rmax : ℚ}
    (hσ : 0 ≤ ((σ : ℚ) : ℝ)) (hρ0 : 0 ≤ ((ρ : ℚ) : ℝ)) (hρ : ((ρ : ℚ) : ℝ) ≤ ((rmax : ℚ) : ℝ))
    (hdel0 : 0 ≤ ((del : ℚ) : ℝ))
    (hchk : ((del : ℚ) : ℝ) ^ 2 ≤ ((ρ : ℚ) : ℝ) ^ 2 * ((σ : ℚ) : ℝ))
    (hz : z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
          ((δ : ℚ) : ℝ) M)
    (hdeep : ((rmax : ℚ) : ℝ) * Real.sqrt ((σ : ℚ) : ℝ) < cutNR C ⬝ᵥ (a - z)) :
    ¬ (((C.margin : ℚ) : ℝ) - priceA C a ≤ ((del : ℚ) : ℝ)) := by
  have hdel_le : ((del : ℚ) : ℝ) ≤ ((rmax : ℚ) : ℝ) * Real.sqrt ((σ : ℚ) : ℝ) := by
    have h1 : ((del : ℚ) : ℝ) ≤ Real.sqrt (((ρ : ℚ) : ℝ) ^ 2 * ((σ : ℚ) : ℝ)) := by
      rw [← Real.sqrt_sq hdel0]
      exact Real.sqrt_le_sqrt hchk
    have h2 : Real.sqrt (((ρ : ℚ) : ℝ) ^ 2 * ((σ : ℚ) : ℝ))
        = ((ρ : ℚ) : ℝ) * Real.sqrt ((σ : ℚ) : ℝ) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hρ0]
    rw [h2] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_right hρ (Real.sqrt_nonneg _))
  have h1 := no_price_of_deep_point C hz (lt_of_le_of_lt hdel_le hdeep)
  exact h1

#print axioms QMCLeafB.Giv37M7.no_price_of_deep_rmax

/-! ## 9.  The family form, at the leaf's own `relaxBallP` and its own accumulated centres

`a` is left free: instantiating `a k := Cat (G.n*G.n) 0 cd k` and
`cd k := ⟨flatQ (C k).normal, p k, ρ k⟩` turns `cutNR (C k)` into `cutCR cd k` and these are
`RunParts.hcut` verbatim. -/

/-- The relaxation the record's `hcut` quantifies over, at the shelf's cast rational level matrix. -/
theorem mem_relaxBallP_iff {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {z : Fin (G.n * G.n) → ℝ} :
    z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P
      ↔ z ∈ QMCLeafB.Boundary.relaxBall
          (QMCLeafB.SepOracle.castMat (QMCLeafB.Finalization.wMatrixQ G))
          (((t - QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ((P.dq : ℚ) : ℝ)
          (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ) := by
  rw [QMCLeafB.ThinRec34M4.relaxBallP, ← QMCLeafB.HemptyR_M3.castMat_wMatrixQ]
  have hu : ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
      = (((t - QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
    push_cast
    ring
  rw [hu]

#print axioms QMCLeafB.Giv37M7.mem_relaxBallP_iff

/-- **(B) at the leaf's own body: the price family gives `hcut`.** -/
theorem hcut_family_of_price {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    (C : ∀ k, RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq)
    (a : ℕ → Fin (G.n * G.n) → ℝ) (del : ℕ → ℚ) (T : ℕ)
    (hprice : ∀ k, k < T →
      ((C k).margin : ℚ) - priceA (C k) (a k) ≤ ((del k : ℚ) : ℝ)) :
    ∀ k, k < T → ∀ z : Fin (G.n * G.n) → ℝ, z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P →
      -(((del k : ℚ)) : ℝ) ≤ cutNR (C k) ⬝ᵥ (z - a k) := by
  intro k hk z hz
  exact hcut_of_price_bound (C k) (a k) (hprice k hk) z
    (M := (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ)) (mem_relaxBallP_iff.mp hz)

#print axioms QMCLeafB.Giv37M7.hcut_family_of_price

/-- **(B) at the leaf's own body: `hcut` gives the price family back.**  So at the campaign's own
body the two are the same condition — the dichotomy is a re-presentation. -/
theorem price_family_of_hcut {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    (C : ∀ k, RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq)
    (a : ℕ → Fin (G.n * G.n) → ℝ) (del : ℕ → ℚ) (T : ℕ)
    (hex : ∀ k, k < T → ∃ z₀ : Fin (G.n * G.n) → ℝ,
      z₀ ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P
        ∧ ((C k).margin : ℚ) ≤ cutNR (C k) ⬝ᵥ (centreR (cX k) - z₀))
    (hcut : ∀ k, k < T → ∀ z : Fin (G.n * G.n) → ℝ,
      z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P →
      -(((del k : ℚ)) : ℝ) ≤ cutNR (C k) ⬝ᵥ (z - a k)) :
    ∀ k, k < T →
      ((C k).margin : ℚ) - priceA (C k) (a k) ≤ ((del k : ℚ) : ℝ) := by
  intro k hk
  obtain ⟨z₀, hz₀, hex₀⟩ := hex k hk
  exact price_of_hcut (C k) (M := (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ))
    (mem_relaxBallP_iff.mp hz₀) hex₀ (hcut k hk z₀ hz₀)

#print axioms QMCLeafB.Giv37M7.price_family_of_hcut

/-- **THE HEADLINE.  The membership gate's all-cut horn is `hcut`.**  For any family of cuts at the
programme's rational centres — whatever the coding — with each round's margin realised on the body,
*"the price fits in the round's slack"* and *"`hcut` holds at the accumulated centre with that
slack"* are the same proposition.  Hence the phase-37 dichotomy does not reduce the leaf: horn (B)
delivers exactly `ShallowCut`, and horn (A) is `hok`. -/
theorem fork_is_presentation {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    (C : ∀ k, RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq)
    (a : ℕ → Fin (G.n * G.n) → ℝ) (del : ℕ → ℚ) (T : ℕ)
    (hex : ∀ k, k < T → ∃ z₀ : Fin (G.n * G.n) → ℝ,
      z₀ ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P
        ∧ ((C k).margin : ℚ) ≤ cutNR (C k) ⬝ᵥ (centreR (cX k) - z₀)) :
    (∀ k, k < T → ((C k).margin : ℚ) - priceA (C k) (a k) ≤ ((del k : ℚ) : ℝ))
      ↔ (∀ k, k < T → ∀ z : Fin (G.n * G.n) → ℝ,
          z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P →
          -(((del k : ℚ)) : ℝ) ≤ cutNR (C k) ⬝ᵥ (z - a k)) :=
  ⟨fun h => hcut_family_of_price C a del T h, fun h => price_family_of_hcut C a del T hex h⟩

#print axioms QMCLeafB.Giv37M7.fork_is_presentation

/-! ## 10.  What this means on the collar (m7/ph36)

The collar dossier (`Check_cov36_m7`: `exists_collar`, `coverage_gap`, `collar_dossier`,
`dichotomy_false`, `ball_radius_le_slack`, `no_horizon_ball`) exhibits a rational `0 < Δ` with a
**nonempty interior body off the face**, where all three banked record obstructions are silent.

Apply §8–§9 there.  Case (A) of the dichotomy is whatever the gate says and adds nothing.  In case
(B) every round yields a cut at the programme's rational centre; by `no_price_of_deep_point` the
round is payable **iff** no body point beats the slack at the accumulated centre, and by
`fork_is_presentation` that is exactly `hcut`.  So:

* the collar is *not* discharged by the dichotomy — the (B) horn reproduces the collar's existing
  obligation verbatim;
* nor is it *refuted* by it — the dichotomy contains no content that could refute anything, since
  its two horns are a case split on a predicate;
* the residual at the collar now has its sharpest form: **a rational normal `c` and a rational slack
  `del` with `del² ≤ rmax²·σ` and `sup_{z ∈ body} ⟨c, Cat k − z⟩ ≤ del`, at every round** — i.e.
  a rational normal in which the *accumulated* centre is shallow, which is `SupportSlot` /
  `ShallowCut` with the price term cancelled identically.

What is genuinely gained by the gate change is only this: case (A) is free (a membership report *is*
a member witness at the round's own centre, needing no grating, no search, no volume), and case (B)
supplies a rational normal per round for free from the shelf's oracle.  The one inequality is
untouched.  **Verdict: (B1) is not available and would not help; (B2) is `ShallowCut`; the collar
stands.** -/


/-! ## 11.  Both horns' *premises*, checked

The dichotomy needs two things of the gate beyond the case split: in case (A) that a membership
report yields `hok`'s own conclusion, and in case (B) that a non-member yields an oracle cut.

* (B) is *definitional* — but only at the MERGED oracle (`Def_QMCLeafB_relax_oracle_merged_m5`),
  where `relaxMem_or_cut` is the totality theorem.  The older m4 oracle's `relaxOk_or_cut` is
  `RelaxOk ∨ cut`, and `RelaxOk` is the *trace-high* ledger, so `¬RelaxMem` does **not** extract a
  cut there: at a trace-high non-member that oracle reports `RelaxOk` and no cut at all.  So horn
  (B) is sound exactly because the gate and the oracle are the same predicate — `hornB_premise`.

* (A) is definitional *up to symmetry*: `HokSlot` demands `cXᵀ = cX ∧ RelaxMem …`, while the gate
  `RelaxMem` says nothing about symmetry.  The gap is free — `RelaxMem` is transpose-invariant in
  its quadratic form, its diagonal and (for symmetric `A`) its trace — so `hornA_premise` closes it
  with `(cX + cXᵀ)/2`.  This is the only non-`rfl` step in horn (A). -/

theorem frob_add {n : ℕ} (C Y Z : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.SepOracle.frob C (Y + Z)
      = QMCLeafB.SepOracle.frob C Y + QMCLeafB.SepOracle.frob C Z := by
  simp only [QMCLeafB.SepOracle.frob, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

#print axioms QMCLeafB.Giv37M7.frob_add

theorem frob_smul {n : ℕ} (c : ℚ) (C Y : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.SepOracle.frob C (c • Y) = c * QMCLeafB.SepOracle.frob C Y := by
  simp only [QMCLeafB.SepOracle.frob, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

#print axioms QMCLeafB.Giv37M7.frob_smul

theorem frob_transpose {n : ℕ} (C Y : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.SepOracle.frob C (Matrix.transpose Y)
      = QMCLeafB.SepOracle.frob (Matrix.transpose C) Y := by
  simp only [QMCLeafB.SepOracle.frob, Matrix.transpose_apply]
  rw [Finset.sum_comm]

#print axioms QMCLeafB.Giv37M7.frob_transpose

/-- **Horn (B)'s premise is definitional** at the merged oracle: a non-member at a rational centre
carries a genuine cut there. -/
theorem hornB_premise {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} (hδ : 0 < δ)
    (h : ¬ RelaxMem A cX u δ) : Nonempty (RelaxCut A cX u δ) := by
  rcases relaxMem_or_cut A cX u δ hδ with h1 | h2
  · exact absurd h1 h
  · exact h2

#print axioms QMCLeafB.Giv37M7.hornB_premise

/-- **Horn (A)'s only non-`rfl` step: symmetrisation.**  `RelaxMem` is invariant under
`cX ↦ (cX + cXᵀ)/2` for symmetric `A`, so a membership report gives `HokSlot`'s symmetric witness. -/
theorem hornA_premise {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (hA : Matrix.transpose A = A)
    {cX : Matrix (Fin n) (Fin n) ℚ} (h : RelaxMem A cX u δ) :
    ∃ Y : Matrix (Fin n) (Fin n) ℚ, Matrix.transpose Y = Y ∧ RelaxMem A Y u δ := by
  refine ⟨(1 / 2 : ℚ) • (cX + Matrix.transpose cX), ?_, ?_⟩
  · rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  · refine ⟨h.δ_pos, ?_, ?_, ?_⟩
    · intro x
      have hq : QMCLeafB.SepOracle.qf ((1 / 2 : ℚ) • (cX + Matrix.transpose cX)) x
          = QMCLeafB.SepOracle.qf cX x := by
        rw [QMCLeafB.SepOracle.qf_smulQ, QMCLeafB.SepOracle.qf_add,
          QMCLeafB.OkProdM6.qf_transpose]
        ring
      rw [hq]
      exact h.psd_margin x
    · intro i
      have hd : ((1 / 2 : ℚ) • (cX + Matrix.transpose cX)) i i = cX i i := by
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
        ring
      rw [hd]
      exact h.diag_near i
    · have hf : QMCLeafB.SepOracle.frob A ((1 / 2 : ℚ) • (cX + Matrix.transpose cX))
          = QMCLeafB.SepOracle.frob A cX := by
        rw [frob_smul, frob_add, frob_transpose, hA]
        ring
      rw [hf]
      exact h.trace_le

#print axioms QMCLeafB.Giv37M7.hornA_premise

end QMCLeafB.Giv37M7


