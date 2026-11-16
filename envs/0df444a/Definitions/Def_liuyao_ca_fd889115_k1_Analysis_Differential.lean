-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Differential
-- name    : liuyao_ca_fd889115_k1_Analysis_Differential
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:53:29.344904+00:00
-- url     : https://prove2.me/theorems/162d44ff-6751-4b6b-bbe1-01e544ac6bd4
-- title:
--   Computable analysis · Differential · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/Differential.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Calculus

set_option autoImplicit true

/-!
# Constructive differential calculus

This file contains the small derivative vocabulary needed before proving
calculus identities for the elementary representations.  It is intentionally
interval-valued and rational-only.
-/

namespace ComputableAnalysis

/-- Equality of real-valued functions on rational inputs.

This is the function-level equality notion we use in the project: for every
rational input in the common domain, the two output `RealCompute`s are equivalent
by interval overlap at every precision. -/
def RealFunRaw.EquivalentWith (f g : RealFunRaw)
    (hf : f.Valid) (hg : g.Valid) : Prop :=
  forall x (hfx : f.domain x) (hgx : g.domain x),
    (f.apply hf x hfx).Equiv (g.apply hg x hgx)

def RealFunRaw.Equivalent (f g : RealFunRaw) : Prop :=
  Exists fun hf : f.Valid => Exists fun hg : g.Valid =>
    f.EquivalentWith g hf hg

namespace RealFunRaw

/-! The same representation-graph laws are available for the stable
`x,n ↦ QInterval` function layer.  Transitivity explicitly asks that the
middle evaluator be defined wherever the two outer evaluators are defined;
unlike `FunctionOnInterval`, arbitrary `RealFunRaw`s need not share a domain. -/

theorem equivalentWith_refl (f : RealFunRaw) (hf : f.Valid) :
    f.EquivalentWith f hf hf := by
  intro x hfx hfx'
  exact RealCompute.equiv_refl (f.apply hf x hfx) (hf x hfx)

theorem equivalentWith_symm
    {f g : RealFunRaw} {hf : f.Valid} {hg : g.Valid}
    (h : f.EquivalentWith g hf hg) :
    g.EquivalentWith f hg hf := by
  intro x hgx hfx
  exact RealCompute.equiv_symm (h x hfx hgx)

theorem equivalentWith_trans
    {f g h : RealFunRaw}
    {hf : f.Valid} {hg : g.Valid} {hh : h.Valid}
    (hdom : forall x, f.domain x -> h.domain x -> g.domain x)
    (hfg : f.EquivalentWith g hf hg)
    (hgh : g.EquivalentWith h hg hh) :
    f.EquivalentWith h hf hh := by
  intro x hfx hhx
  have hgx := hdom x hfx hhx
  have hFvalid : (f.apply hf x hfx).Valid := by
    change RealCompute.ValidCompute (f.applyCompute x)
    exact hf x hfx
  have hGvalid : (g.apply hg x hgx).Valid := by
    change RealCompute.ValidCompute (g.applyCompute x)
    exact hg x hgx
  have hHvalid : (h.apply hh x hhx).Valid := by
    change RealCompute.ValidCompute (h.applyCompute x)
    exact hh x hhx
  exact RealCompute.equiv_trans hFvalid hGvalid hHvalid
    (hfg x hfx hgx) (hgh x hgx hhx)

theorem equivalent_refl {f : RealFunRaw} (hf : f.Valid) :
    f.Equivalent f :=
  ⟨hf, ⟨hf, equivalentWith_refl f hf⟩⟩

theorem equivalent_symm {f g : RealFunRaw}
    (h : f.Equivalent g) : g.Equivalent f := by
  rcases h with ⟨hf, hg, hfg⟩
  exact ⟨hg, ⟨hf, equivalentWith_symm hfg⟩⟩

theorem equivalent_trans {f g h : RealFunRaw}
    (hdom : forall x, f.domain x -> h.domain x -> g.domain x)
    (hfg : f.Equivalent g) (hgh : g.Equivalent h) :
    f.Equivalent h := by
  rcases hfg with ⟨hf, hg, hfg⟩
  rcases hgh with ⟨hg', hh, hgh⟩
  have hproof : hg = hg' := Subsingleton.elim _ _
  cases hproof
  exact ⟨hf, ⟨hh, equivalentWith_trans hdom hfg hgh⟩⟩

end RealFunRaw

def derivativeCheckExact (f g : Rat -> Rat) (x h tolerance : Rat) : Bool :=
  if h = 0 then
    false
  else
    decide (qabs (((f (x + h) - f x) / h) - g x) <= tolerance)

namespace ExactFunction

private theorem one_div_den_succ_le_of_pos {q : Rat} (hq : 0 < q) :
    1 / (((q.den + 1 : Nat) : Rat)) <= q := by
  let d : Rat := ((q.den + 1 : Nat) : Rat)
  have hdpos : 0 < d := by
    dsimp [d]
    exact (Rat.natCast_pos).2 (Nat.succ_pos q.den)
  have hnumpos : 0 < q.num := rat_num_pos_of_pos hq
  have hnumgeInt : (1 : Int) <= q.num := by omega
  have hnumge : (1 : Rat) <= (q.num : Rat) := by
    exact_mod_cast hnumgeInt
  have hqd : q * d = (q.num : Rat) + q := by
    dsimp [d]
    have hden := rat_den_mul_self q
    grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]
  have hqd_ge_one : 1 <= q * d := by
    rw [hqd]
    grind [Rat.le_of_lt hq]
  apply Rat.le_of_mul_le_mul_right (c := d)
  · calc
      (1 / d) * d = 1 := by
        rw [Rat.div_def]
        have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= q * d := hqd_ge_one
  · exact hdpos

def affine (m c : Rat) (x : Rat) : Rat := m * x + c
def constant (m : Rat) (_x : Rat) : Rat := m
def square (x : Rat) : Rat := x * x
def cube (x : Rat) : Rat := x ^ 3
def doubleId (x : Rat) : Rat := 2 * x

/-- Effective derivative of an affine function:
the finite-difference quotient is exactly the constant slope. -/
def affineDerivative (m c : Rat) :
    EffectiveDerivativeExact (affine m c) (constant m) where
  stepRadius := fun eps => eps
  good := by
    intro x h eps hhpos _hhle
    unfold affine constant qabs
    have hcalc :
        (((m * (x + h) + c - (m * x + c)) / h) - m) = 0 := by
      rw [Rat.div_def]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    rw [hcalc]
    simp
    exact Rat.le_of_lt eps.property

/-! First complete FTC instance.  The derivative of an affine rational
function is constant, so the one-cell rectangle computation is already exact.
This is the finite prototype for later polynomial and special-function FTC
certificates. -/
def affineFTCExact (m c a b : Rat) :
    EffectiveFTCExact (affine m c) (constant m) a b where
  derivative := affineDerivative m c
  chooseN := fun _ => 1
  good := by
    intro eps
    unfold ftcErrorExact
    change qabs
      (riemannLeftExact (fun _ => m) a b 1 -
        (affine m c b - affine m c a)) <= eps.val
    rw [riemannLeftExact_constant_one]
    unfold affine
    simp [qabs]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm]

/-! The first nonlinear finite FTC error is the nonnegative missing strip.
This form is convenient for choosing a stage from a rational error budget:
the analytic-looking estimate has become the explicit square of the cell
width divided by the number of cells. -/
theorem ftcErrorExact_square_doubleId_of_pos
    {a b : Rat} (hab : a <= b) {n : Nat} (hn : 0 < n) :
    ftcErrorExact square doubleId a b n =
      (b - a) ^ 2 / (n : Rat) := by
  unfold ftcErrorExact doubleId square
  rw [riemannLeftExact_doubleId_of_pos hn]
  have hwidth : 0 <= (b - a) ^ 2 := by
    have hpow : (b - a) ^ 2 = (b - a) * (b - a) := by
      grind [Rat.pow_succ]
    rw [hpow]
    by_cases h : 0 <= b - a
    · exact Rat.mul_nonneg h h
    · have hneg : 0 <= -(b - a) := by grind
      have hsq := Rat.mul_nonneg hneg hneg
      simpa [Rat.mul_neg, Rat.neg_mul, Rat.neg_neg] using hsq
  have hden : 0 < (n : Rat) := (Rat.natCast_pos).2 hn
  have hterm : 0 <= (b - a) ^ 2 / (n : Rat) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg hwidth
      (Rat.le_of_lt ((Rat.inv_pos).2 hden))
  have hdiff :
      ((b ^ 2 - a ^ 2) - (b - a) ^ 2 / (n : Rat)) -
        (b * b - a * a) = -((b - a) ^ 2 / (n : Rat)) := by
    grind [Rat.sub_eq_add_neg, Rat.pow_succ]
  rw [hdiff]
  unfold qabs
  by_cases hzero : (b - a) ^ 2 / (n : Rat) = 0
  · simp [hzero]
  · rw [if_pos (by grind : -((b - a) ^ 2 / (n : Rat)) < 0)]
    grind

/-! The cubic rung has the same status, but its finite left-rectangle error
has the next explicit polynomial numerator.  This is still a rational
identity; no assertion about an infinite sum is involved. -/
theorem ftcErrorExact_cube_threeSquare_unit_of_pos
    {n : Nat} (hn : 0 < n) :
    ftcErrorExact cube (fun x => 3 * x ^ 2) 0 1 n =
      (3 * (n : Rat) - 1) / (2 * (n : Rat) ^ 2) := by
  unfold ftcErrorExact cube
  rw [riemannLeftExact_threeSquare_unit_of_pos hn]
  have hN : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  have hformula :
      3 * (1 / (n : Rat)) ^ 3 *
          (((n : Rat) * ((n : Rat) - 1) *
            (2 * (n : Rat) - 1)) / 6) -
        (1 ^ 3 - 0 ^ 3) =
        -((3 * (n : Rat) - 1) / (2 * (n : Rat) ^ 2)) := by
    grind [Rat.div_def, Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
      Rat.mul_inv_cancel]
  rw [hformula]
  have hnum : 0 <= 3 * (n : Rat) - 1 := by
    have hnone : (1 : Rat) <= (n : Rat) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))
    grind
  have hdenpos : 0 < 2 * (n : Rat) ^ 2 := by
    have hsq : 0 < (n : Rat) ^ 2 := by
      rw [show (n : Rat) ^ 2 = (n : Rat) * (n : Rat) by
        grind [Rat.pow_succ]]
      exact Rat.mul_pos ((Rat.natCast_pos).2 hn)
        ((Rat.natCast_pos).2 hn)
    exact Rat.mul_pos (by decide +kernel) hsq
  have hterm : 0 <= (3 * (n : Rat) - 1) / (2 * (n : Rat) ^ 2) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg hnum (Rat.le_of_lt ((Rat.inv_pos).2 hdenpos))
  unfold qabs
  by_cases hzero : (3 * (n : Rat) - 1) / (2 * (n : Rat) ^ 2) = 0
  · simp [hzero]
  · rw [if_pos (by grind :
      -((3 * (n : Rat) - 1) / (2 * (n : Rat) ^ 2)) < 0)]
    grind

theorem affine_derivative_effective (m c : Rat) :
    Nonempty (EffectiveDerivativeExact (affine m c) (constant m)) :=
  ⟨affineDerivative m c⟩

/-- Effective derivative of `x^2`:
the finite-difference quotient is exactly `2x + h`, hence it is within `eps`
of `2x` whenever `0 < h <= eps`. -/
def squareDerivative : EffectiveDerivativeExact square doubleId where
  stepRadius := fun eps => eps
  good := by
    intro x h eps hhpos hhle
    unfold square doubleId qabs
    have hcalc :
        (((x + h) * (x + h) - x * x) / h - 2 * x) = h := by
      rw [Rat.div_def]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    rw [hcalc]
    have hnot : ¬ h < 0 := by grind
    simp [hnot]
    exact hhle

theorem square_derivative_effective :
    Nonempty (EffectiveDerivativeExact square doubleId) :=
  ⟨squareDerivative⟩

/-! A first nonlinear FTC instance.  On `[0,1]`, the left rectangles for
`2*x` miss the exact area under the square primitive by precisely `1/n`.
Choosing the denominator of the requested rational precision therefore gives
an explicit finite certificate of the integral, with no completeness axiom. -/
def squareFTCExactUnit :
    EffectiveFTCExact square doubleId 0 1 where
  derivative := squareDerivative
  chooseN := fun eps => eps.val.den + 1
  good := by
    intro eps
    let n : Nat := eps.val.den + 1
    have hn : 0 < n := by
      dsimp [n]
      omega
    unfold ftcErrorExact
    change qabs
      (riemannLeftExact (fun x => 2 * x) 0 1 n -
        (square 1 - square 0)) <= eps.val
    rw [riemannLeftExact_doubleId_of_pos hn]
    unfold square
    have hcalc :
        (1 ^ 2 - 0 ^ 2 - (1 - 0) ^ 2 / (n : Rat) -
          (1 * 1 - 0 * 0)) = -(1 / (n : Rat)) := by
      grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.div_def,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    rw [hcalc]
    have hposinv : 0 < 1 / (n : Rat) := by
      simpa [Rat.div_def] using
        ((Rat.inv_pos).2 ((Rat.natCast_pos).2 hn))
    have hneg : -(1 / (n : Rat)) < 0 := by grind
    have habs : qabs (-(1 / (n : Rat))) = 1 / (n : Rat) := by
      unfold qabs
      rw [if_pos hneg]
      grind
    rw [habs]
    dsimp [n]
    exact one_div_den_succ_le_of_pos eps.property

/-- The exact rational difference quotient used by the finite product
identities below. -/
def differenceQuotient (f : Rat -> Rat) (x h : Rat) : Rat :=
  (f (x + h) - f x) / h

theorem differenceQuotient_add (f g : Rat -> Rat) {x h : Rat}
    (hh : h ≠ 0) :
    differenceQuotient (fun z => f z + g z) x h =
      differenceQuotient f x h + differenceQuotient g x h := by
  unfold differenceQuotient
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
    Rat.mul_comm]

theorem differenceQuotient_scale (c : Rat) (f : Rat -> Rat) {x h : Rat}
    (hh : h ≠ 0) :
    differenceQuotient (fun z => c * f z) x h =
      c * differenceQuotient f x h := by
  unfold differenceQuotient
  rw [Rat.div_def, Rat.div_def]
  have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
    Rat.mul_comm]

/- A finite L'Hopital-style cancellation certificate: away from the common
zero `a`, the quotient of the factored numerator and denominator is the
derivative ratio at `a`, namely `2 * a / 1`, plus its exact linear remainder.
This is only a rational identity; it makes no assertion about a limit. -/
theorem quadratic_linear_factored_quotient_derivative_ratio
    {a x : Rat} (hx : x - a ≠ 0) :
    (x ^ 2 - a ^ 2) / (x - a) = (2 * a) / 1 + (x - a) := by
  rw [Rat.div_def]
  have hcancel : (x - a) * (x - a)⁻¹ = 1 :=
    Rat.mul_inv_cancel (x - a) hx
  grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/- The cubic companion records the exact finite remainder after cancelling
the common linear factor.  It is the cubic L'Hopital-style certificate, not a
statement about a limiting quotient. -/
theorem cubic_linear_factored_quotient_derivative_ratio
    {a x : Rat} (hx : x - a ≠ 0) :
    (x ^ 3 - a ^ 3) / (x - a) =
      3 * a ^ 2 + 3 * a * (x - a) + (x - a) ^ 2 := by
  rw [Rat.div_def]
  have hcancel : (x - a) * (x - a)⁻¹ = 1 :=
    Rat.mul_inv_cancel (x - a) hx
  grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/- A reusable finite cancellation certificate for a general factored
polynomial evaluator.  The factor `g` may be any rational function here,
and in particular may be a finite polynomial evaluator; the only required
side condition is that the displayed linear factor is nonzero.  This is an
exact rational identity, not a limit or a completed-real quotient theorem. -/
theorem factored_linear_quotient_cancel
    {a x : Rat} {g : Rat -> Rat} (hx : x - a ≠ 0) :
    ((x - a) * g x) / (x - a) = g x := by
  rw [Rat.div_def]
  have hcancel : (x - a) * (x - a)⁻¹ = 1 :=
    Rat.mul_inv_cancel (x - a) hx
  grind [Rat.mul_assoc, Rat.mul_comm]

/- A two-function finite L'Hopital certificate: if numerator and denominator
share the same nonzero linear factor, their quotient is exactly the quotient
of the remaining rational evaluators.  The denominator remainder must also
be nonzero; this is the finite algebraic analogue of cancelling a common
vanishing factor before comparing derivative ratios. -/
theorem common_linear_factor_quotient_cancel
    {a x : Rat} {g h : Rat -> Rat}
    (hx : x - a ≠ 0) (hh : h x ≠ 0) :
    ((x - a) * g x) / ((x - a) * h x) = g x / h x := by
  have hscaled : (x - a) * h x ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hleft | hright
    · exact hx hleft
    · exact hh hright
  rw [Rat.div_def, Rat.div_def]
  have hcancel : (x - a) * (x - a)⁻¹ = 1 :=
    Rat.mul_inv_cancel (x - a) hx
  have hscaled_inv : ((x - a) * h x)⁻¹ = (x - a)⁻¹ * (h x)⁻¹ := by
    rw [Rat.inv_mul_rev]
    grind [Rat.mul_comm]
  have hhc : h x * (h x)⁻¹ = 1 := Rat.mul_inv_cancel (h x) hh
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem affine_differenceQuotient {m c x h : Rat} (hh : h ≠ 0) :
    differenceQuotient (affine m c) x h = m := by
  unfold differenceQuotient affine
  rw [Rat.div_def]
  have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/- The exact finite chain-rule analogue for an affine inner map.  The
composition is evaluated at rational points, and the inner difference
quotient is transported by its slope; the only side conditions are the
nonzero outer mesh and the nonzero affine slope.  This is a finite rational
identity, with no limit or completed-real interpretation. -/
theorem differenceQuotient_affine_comp
    (f : Rat -> Rat) {m c x h : Rat} (hm : m ≠ 0) (hh : h ≠ 0) :
    differenceQuotient (fun z => f (affine m c z)) x h =
      m * differenceQuotient f (affine m c x) (m * h) := by
  have hmh : m * h ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hmzero | hhzero
    · exact hm hmzero
    · exact hh hhzero
  unfold differenceQuotient affine
  rw [Rat.div_def, Rat.div_def]
  have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
  have hmhcancel : (m * h) * (m * h)⁻¹ = 1 :=
    Rat.mul_inv_cancel (m * h) hmh
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-! The zero-slope case is not an analytic exception: the affine inner map is
constant, so its finite difference quotient is exactly zero.  Including it
gives one total finite chain-rule identity, while the nonzero-slope theorem
above remains the useful transport form for inverse-coordinate arguments. -/
theorem differenceQuotient_affine_comp_of_step
    (f : Rat -> Rat) {m c x h : Rat} (hh : h ≠ 0) :
    differenceQuotient (fun z => f (affine m c z)) x h =
      m * differenceQuotient f (affine m c x) (m * h) := by
  by_cases hm : m = 0
  · subst m
    simp [differenceQuotient, affine, Rat.div_def]
    grind
  · exact differenceQuotient_affine_comp f hm hh

/-! An affine reparametrization transports the finite left-rectangle sum
exactly.  This is the computational core of substitution: it is an identity
of rational folds, before any shrinking or abstract integral is introduced.
The identity is total in the slope; positivity is needed only later when the
affine map is required to preserve orientation. -/
theorem riemannLeftExact_affine_substitution
    (g : Rat -> Rat) {m c a b : Rat} (n : Nat) :
    riemannLeftExact (fun x => m * g (affine m c x)) a b n =
      riemannLeftExact g (affine m c a) (affine m c b) n := by
  have hmesh : ∀ q : Nat,
      mesh (affine m c a) (affine m c b) q = m * mesh a b q := by
    intro q
    by_cases hq : q = 0
    · simp [mesh, hq]
    · have hqr : (q : Rat) ≠ 0 := by
        exact Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.pos_of_ne_zero hq))
      unfold mesh affine
      rw [if_neg hq, if_neg hq, Rat.div_def, Rat.div_def]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
        Rat.mul_comm, Rat.mul_inv_cancel]
  have hpoint : ∀ (q k : Nat),
      leftPoint (affine m c a) (affine m c b) q k =
        affine m c (leftPoint a b q k) := by
    intro q k
    unfold leftPoint
    rw [hmesh q]
    unfold affine
    grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
  have hsum : ∀ q : Nat,
      (List.range q).foldl
          (fun acc k => acc + mesh a b q * (m * g (affine m c (leftPoint a b q k)))) 0 =
        (List.range q).foldl
          (fun acc k => acc + mesh (affine m c a) (affine m c b) q *
            g (leftPoint (affine m c a) (affine m c b) q k)) 0 := by
    intro q
    have hfold : ∀ (xs : List Nat),
        (∀ k, k ∈ xs ->
          mesh a b q * (m * g (affine m c (leftPoint a b q k))) =
            mesh (affine m c a) (affine m c b) q *
              g (leftPoint (affine m c a) (affine m c b) q k)) ->
        ∀ acc : Rat,
          (xs.foldl
            (fun acc k => acc + mesh a b q *
              (m * g (affine m c (leftPoint a b q k)))) acc) =
          (xs.foldl
            (fun acc k => acc + mesh (affine m c a) (affine m c b) q *
              g (leftPoint (affine m c a) (affine m c b) q k)) acc) := by
      intro xs
      induction xs with
      | nil => intro _h acc; rfl
      | cons k ks ih =>
          intro hxs acc
          dsimp
          rw [hxs k (by simp)]
          exact ih (fun j hj => hxs j (by simp [hj])) _
    apply hfold (List.range q)
    intro k hk
    rw [hmesh q, hpoint q k]
    grind [Rat.mul_assoc, Rat.mul_comm]
  simpa [riemannLeftExact] using hsum n

/- A positive affine change of endpoint coordinates transports a finite
secant bracket.  The source bracket is stated at rational endpoints `a,b`,
while `hxa` and `hyb` identify those endpoints with the translated/scaled
coordinates `x,y`.  Thus this is an endpoint-level companion to
`secant_of_finite_derivative_bracket`, not a second mesh theorem. -/
theorem secant_bracket_affine_endpoint_transport
    {f : Rat -> Rat} {a b x y m c lower upper : Rat}
    (hm : 0 < m) (hab : b - a ≠ 0)
    (hxa : affine m c x = a) (hyb : affine m c y = b)
    (hbracket :
      lower <= differenceQuotient f a (b - a) /\
        differenceQuotient f a (b - a) <= upper) :
    m * lower <=
        differenceQuotient (fun z => f (affine m c z)) x (y - x) /\
      differenceQuotient (fun z => f (affine m c z)) x (y - x) <=
        m * upper := by
  have hmne : m ≠ 0 := Rat.ne_of_gt hm
  have hmstep : m * (y - x) = b - a := by
    unfold affine at hxa hyb
    grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
      Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
  have hstep : y - x ≠ 0 := by
    intro hzero
    apply hab
    rw [← hmstep, hzero, Rat.mul_zero]
  have htransport := differenceQuotient_affine_comp
    f (m := m) (c := c) (x := x) (h := y - x) hmne hstep
  rw [htransport, hmstep, hxa]
  have hnonneg : 0 <= m := Rat.le_of_lt hm
  constructor
  · exact (Rat.mul_le_mul_of_nonneg_left hbracket.1 hnonneg)
  · exact (Rat.mul_le_mul_of_nonneg_left hbracket.2 hnonneg)

theorem affine_root_of_nonzero_slope {m c : Rat} (hm : m ≠ 0) :
    affine m c (-c / m) = 0 := by
  unfold affine
  rw [Rat.div_def]
  have hcancel : m * m⁻¹ = 1 := Rat.mul_inv_cancel m hm
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem affine_root_between_of_sign_change
    {m c a b : Rat} (hmpos : 0 < m)
    (ha : affine m c a <= 0) (hb : 0 <= affine m c b) :
    a <= -c / m ∧ -c / m <= b ∧ affine m c (-c / m) = 0 := by
  have hma : m * a <= -c := by
    unfold affine at ha
    grind
  have hmb : -c <= m * b := by
    unfold affine at hb
    grind
  have hleft : a <= -c / m := by
    apply Rat.le_of_mul_le_mul_right (c := m)
    · calc
        a * m = m * a := by rw [Rat.mul_comm]
        _ <= -c := hma
        _ = (-c / m) * m := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
            Rat.neg_mul]
    · exact hmpos
  have hright : -c / m <= b := by
    apply Rat.le_of_mul_le_mul_right (c := m)
    · calc
        (-c / m) * m = -c := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
            Rat.neg_mul]
        _ <= m * b := hmb
        _ = b * m := by rw [Rat.mul_comm]
    · exact hmpos
  exact ⟨hleft, hright, affine_root_of_nonzero_slope (Rat.ne_of_gt hmpos)⟩

theorem affine_root_between_of_negative_sign_change
    {m c a b : Rat} (hmneg : m < 0)
    (ha : 0 <= affine m c a) (hb : affine m c b <= 0) :
    a <= -c / m ∧ -c / m <= b ∧ affine m c (-c / m) = 0 := by
  have hma : -m * a <= c := by
    unfold affine at ha
    grind
  have hmb : c <= -m * b := by
    unfold affine at hb
    grind
  have hpos : 0 < -m := by grind
  have hleft : a <= -c / m := by
    apply Rat.le_of_mul_le_mul_right (c := -m)
    · calc
        a * (-m) = -m * a := by rw [Rat.mul_comm]
        _ <= c := hma
        _ = (-c / m) * (-m) := by
          rw [Rat.div_def]
          have hmne : m ≠ 0 := Rat.ne_of_lt hmneg
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
            Rat.neg_mul]
    · exact hpos
  have hright : -c / m <= b := by
    apply Rat.le_of_mul_le_mul_right (c := -m)
    · calc
        (-c / m) * (-m) = c := by
          rw [Rat.div_def]
          have hmne : m ≠ 0 := Rat.ne_of_lt hmneg
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
            Rat.neg_mul]
        _ <= -m * b := hmb
        _ = b * (-m) := by rw [Rat.mul_comm]
    · exact hpos
  exact ⟨hleft, hright, affine_root_of_nonzero_slope (Rat.ne_of_lt hmneg)⟩

theorem cube_differenceQuotient {x h : Rat} (hh : h ≠ 0) :
    differenceQuotient cube x h = 3 * x ^ 2 + 3 * x * h + h ^ 2 := by
  unfold differenceQuotient cube
  rw [Rat.div_def]
  have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
  grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem cube_midpoint_secant {a b : Rat} (hab : b - a ≠ 0) :
    differenceQuotient cube a (b - a) =
      3 * ((a + b) / 2) ^ 2 + (b - a) ^ 2 / 4 := by
  rw [cube_differenceQuotient hab]
  grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem quartic_differenceQuotient {x h : Rat} (hh : h ≠ 0) :
    differenceQuotient (fun z => z ^ 4) x h =
      4 * x ^ 3 + 6 * x ^ 2 * h + 4 * x * h ^ 2 + h ^ 3 := by
  unfold differenceQuotient
  rw [Rat.div_def]
  have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
  grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem quartic_midpoint_secant {a b : Rat} (hab : b - a ≠ 0) :
    differenceQuotient (fun z => z ^ 4) a (b - a) =
      4 * ((a + b) / 2) ^ 3 + ((a + b) / 2) * (b - a) ^ 2 := by
  rw [quartic_differenceQuotient hab]
  grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem quintic_differenceQuotient {x h : Rat} (hh : h ≠ 0) :
    differenceQuotient (fun z => z ^ 5) x h =
      5 * x ^ 4 + 10 * x ^ 3 * h + 10 * x ^ 2 * h ^ 2 +
        5 * x * h ^ 3 + h ^ 4 := by
  unfold differenceQuotient
  rw [Rat.div_def]
  have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
  grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem sextic_differenceQuotient {x h : Rat} (hh : h ≠ 0) :
    differenceQuotient (fun z => z ^ 6) x h =
      6 * x ^ 5 + 15 * x ^ 4 * h + 20 * x ^ 3 * h ^ 2 +
        15 * x ^ 2 * h ^ 3 + 6 * x * h ^ 4 + h ^ 5 := by
  unfold differenceQuotient
  rw [Rat.div_def]
  have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
  grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem quintic_midpoint_secant {a b : Rat} (hab : b - a ≠ 0) :
    differenceQuotient (fun z => z ^ 5) a (b - a) =
      5 * ((a + b) / 2) ^ 4 +
        (5 / 2) * ((a + b) / 2) ^ 2 * (b - a) ^ 2 +
        (b - a) ^ 4 / 16 := by
  rw [quintic_differenceQuotient hab]
  grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem sextic_midpoint_secant {a b : Rat} (hab : b - a ≠ 0) :
    differenceQuotient (fun z => z ^ 6) a (b - a) =
      6 * ((a + b) / 2) ^ 5 +
        5 * ((a + b) / 2) ^ 3 * (b - a) ^ 2 +
        (3 / 8) * ((a + b) / 2) * (b - a) ^ 4 := by
  rw [sextic_differenceQuotient hab]
  grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem square_quotient_by_id {x : Rat} (hx : x ≠ 0) :
    square x / x = x := by
  unfold square
  rw [Rat.div_def]
  have hcancel : x * x⁻¹ = 1 := Rat.mul_inv_cancel x hx
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem cube_quotient_by_id {x : Rat} (hx : x ≠ 0) :
    cube x / x = x ^ 2 := by
  unfold cube
  rw [Rat.div_def]
  have hcancel : x * x⁻¹ = 1 := Rat.mul_inv_cancel x hx
  grind [Rat.pow_succ, Rat.mul_assoc, Rat.mul_comm]

theorem power_succ_quotient_by_id (n : Nat) {x : Rat} (hx : x ≠ 0) :
    x ^ (n + 1) / x = x ^ n := by
  rw [Rat.pow_succ, Rat.div_def]
  have hcancel : x * x⁻¹ = 1 := Rat.mul_inv_cancel x hx
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem power_succ_quotient_by_power (n : Nat) {x : Rat} (hx : x ≠ 0) :
    x ^ (n + 1) / x ^ n = x := by
  have hpow : x ^ n ≠ 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Rat.pow_succ]
        intro hzero
        rcases Rat.mul_eq_zero.mp hzero with hleft | hright
        · exact ih hleft
        · exact hx hright
  rw [Rat.pow_succ, Rat.div_def]
  have hcancel : x ^ n * (x ^ n)⁻¹ = 1 :=
    Rat.mul_inv_cancel (x ^ n) hpow
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem power_add_quotient_by_power (m n : Nat) {x : Rat} (hx : x ≠ 0) :
    x ^ (m + n) / x ^ m = x ^ n := by
  have hpow : x ^ m ≠ 0 := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Rat.pow_succ]
        intro hzero
        rcases Rat.mul_eq_zero.mp hzero with hleft | hright
        · exact ih hleft
        · exact hx hright
  have hpowadd : x ^ (m + n) = x ^ m * x ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [show m + (n + 1) = m + n + 1 by omega,
          Rat.pow_succ, ih, Rat.pow_succ]
        grind [Rat.mul_assoc, Rat.mul_comm]
  rw [hpowadd, Rat.div_def]
  have hcancel : x ^ m * (x ^ m)⁻¹ = 1 :=
    Rat.mul_inv_cancel (x ^ m) hpow
  grind [Rat.mul_assoc, Rat.mul_comm]

/-! Scalar-weighted form of the same finite cancellation. -/

theorem mul_power_add_quotient_by_power (y : Rat) (m n : Nat)
    {x : Rat} (hx : x ≠ 0) :
    (y * x ^ (m + n)) / x ^ m = y * x ^ n := by
  have hpow : x ^ m ≠ 0 := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Rat.pow_succ]
        intro hzero
        rcases Rat.mul_eq_zero.mp hzero with hleft | hright
        · exact ih hleft
        · exact hx hright
  have hpowadd : x ^ (m + n) = x ^ m * x ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [show m + (n + 1) = m + n + 1 by omega,
          Rat.pow_succ, ih, Rat.pow_succ]
        grind [Rat.mul_assoc, Rat.mul_comm]
  rw [hpowadd, Rat.div_def]
  have hcancel : x ^ m * (x ^ m)⁻¹ = 1 :=
    Rat.mul_inv_cancel (x ^ m) hpow
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem mul_power_add_quotient_by_scaled_power
    (y z : Rat) (m n : Nat) {x : Rat} (hx : x ≠ 0) (hz : z ≠ 0) :
    (y * x ^ (m + n)) / (z * x ^ m) = (y / z) * x ^ n := by
  have hpow : x ^ m ≠ 0 := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Rat.pow_succ]
        intro hzero
        rcases Rat.mul_eq_zero.mp hzero with hleft | hright
        · exact ih hleft
        · exact hx hright
  have hpowadd : x ^ (m + n) = x ^ m * x ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [show m + (n + 1) = m + n + 1 by omega,
          Rat.pow_succ, ih, Rat.pow_succ]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hscaled : z * x ^ m ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hleft | hright
    · exact hz hleft
    · exact hpow hright
  rw [hpowadd, Rat.div_def, Rat.div_def]
  have hcancel : x ^ m * (x ^ m)⁻¹ = 1 :=
    Rat.mul_inv_cancel (x ^ m) hpow
  have hzcancel : z * z⁻¹ = 1 := Rat.mul_inv_cancel z hz
  have hscaled_inv : (z * x ^ m)⁻¹ = z⁻¹ * (x ^ m)⁻¹ := by
    rw [Rat.inv_mul_rev]
    grind [Rat.mul_comm]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem square_midpoint_mean_value {a b : Rat} (hab : b - a ≠ 0) :
    differenceQuotient square a (b - a) = 2 * ((a + b) / 2) := by
  unfold differenceQuotient square
  rw [Rat.div_def]
  have hcancel : (b - a) * (b - a)⁻¹ = 1 :=
    Rat.mul_inv_cancel (b - a) hab
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem quadratic_midpoint_mean_value
    (c₀ c₁ c₂ a b : Rat) (hab : b - a ≠ 0) :
    differenceQuotient (fun z => c₀ + c₁ * z + c₂ * z * z) a (b - a) =
      c₁ + 2 * c₂ * ((a + b) / 2) := by
  unfold differenceQuotient
  rw [Rat.div_def]
  have hcancel : (b - a) * (b - a)⁻¹ = 1 :=
    Rat.mul_inv_cancel (b - a) hab
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/- A finite mean-value certificate for the cubic on a nonnegative interval.
The secant quotient is trapped between the endpoint derivatives; this is an
explicit rational inequality, not an appeal to an attained intermediate
point or to a completed real interval. -/
theorem cube_secant_derivative_bracket {a b : Rat}
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    3 * a * a <= differenceQuotient cube a (b - a) /\
      differenceQuotient cube a (b - a) <= 3 * b * b := by
  have hcalc :
      differenceQuotient cube a (b - a) = a * a + a * b + b * b := by
    unfold differenceQuotient cube
    rw [Rat.div_def]
    have hcancel : (b - a) * (b - a)⁻¹ = 1 :=
      Rat.mul_inv_cancel (b - a) hne
    grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  rw [hcalc]
  have hba : 0 <= b - a := by grind
  have hb : 0 <= b := by grind
  have hleft : 0 <= b + 2 * a := by grind
  have hright : 0 <= 2 * b + a := by grind
  have hleftprod : 0 <= (b - a) * (b + 2 * a) :=
    Rat.mul_nonneg hba hleft
  have hrightprod : 0 <= (b - a) * (2 * b + a) :=
    Rat.mul_nonneg hba hright
  constructor
  · grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm]
  · grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm]

/-- A pointwise computable MVT witness for the cubic.

The witness is supplied as a rational `t`; the only equation to check is that
the cubic secant slope agrees with the derivative value `3 * t^2`.  This is
the project-style replacement for asserting an existential intermediate real
point: the interval location and the secant identity are both finite data. -/
theorem cube_secant_supplied_mvt_witness {a b t : Rat}
    (hab : a < b) (hat : a < t) (htb : t < b)
    (hsec : a * a + a * b + b * b = 3 * t * t) :
    a < t /\ t < b /\
      differenceQuotient cube a (b - a) = 3 * t * t := by
  have hne : b - a ≠ 0 := by
    exact Rat.ne_of_gt (by grind)
  have hcalc :
      differenceQuotient cube a (b - a) = a * a + a * b + b * b := by
    unfold differenceQuotient cube
    rw [Rat.div_def]
    have hcancel : (b - a) * (b - a)⁻¹ = 1 :=
      Rat.mul_inv_cancel (b - a) hne
    grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  exact ⟨hat, htb, hcalc.trans hsec⟩

/- A finite mean-value certificate for the square on a nonnegative interval.
The secant quotient is trapped between the endpoint derivatives by the
identity `(b^2 - a^2) / (b - a) = a + b`; all quantities remain rational and
finite. -/
theorem square_secant_derivative_bracket {a b : Rat}
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    2 * a <= differenceQuotient square a (b - a) /\
      differenceQuotient square a (b - a) <= 2 * b := by
  have hcalc :
      differenceQuotient square a (b - a) = a + b := by
    unfold differenceQuotient square
    rw [Rat.div_def]
    have hcancel : (b - a) * (b - a)⁻¹ = 1 :=
      Rat.mul_inv_cancel (b - a) hne
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  rw [hcalc]
  have hb : 0 <= b := by grind
  constructor <;> grind

/- A finite mean-value certificate for the quartic on a nonnegative interval.
The secant quotient is trapped between the endpoint derivatives by two
explicit factorizations; this records the finite certificate without
selecting an intermediate real point. -/
theorem quartic_secant_derivative_bracket {a b : Rat}
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    4 * a ^ 3 <= differenceQuotient (fun z => z ^ 4) a (b - a) /\
      differenceQuotient (fun z => z ^ 4) a (b - a) <= 4 * b ^ 3 := by
  have hcalc :
      differenceQuotient (fun z => z ^ 4) a (b - a) =
        a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 := by
    unfold differenceQuotient
    rw [Rat.div_def]
    have hcancel : (b - a) * (b - a)⁻¹ = 1 :=
      Rat.mul_inv_cancel (b - a) hne
    grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  rw [hcalc]
  have hba : 0 <= b - a := by grind
  have hb : 0 <= b := by grind
  have hleft : 0 <= b ^ 2 + 2 * a * b + 3 * a ^ 2 := by
    have hbsq : 0 <= b ^ 2 := Rat.pow_nonneg hb
    have habprod : 0 <= a * b := Rat.mul_nonneg ha hb
    have hasq : 0 <= a ^ 2 := Rat.pow_nonneg ha
    have htwoprod : 0 <= 2 * a * b := by
      have htwoprod' : 0 <= 2 * (a * b) :=
        Rat.mul_nonneg (by grind) habprod
      grind [Rat.mul_assoc]
    have hthreesq : 0 <= 3 * a ^ 2 :=
      Rat.mul_nonneg (by grind) hasq
    exact Rat.add_nonneg (Rat.add_nonneg hbsq htwoprod) hthreesq
  have hright : 0 <= 3 * b ^ 2 + 2 * a * b + a ^ 2 := by
    have hbsq : 0 <= b ^ 2 := Rat.pow_nonneg hb
    have habprod : 0 <= a * b := Rat.mul_nonneg ha hb
    have hasq : 0 <= a ^ 2 := Rat.pow_nonneg ha
    have threebsq : 0 <= 3 * b ^ 2 :=
      Rat.mul_nonneg (by grind) hbsq
    have htwoprod : 0 <= 2 * a * b := by
      have htwoprod' : 0 <= 2 * (a * b) :=
        Rat.mul_nonneg (by grind) habprod
      grind [Rat.mul_assoc]
    exact Rat.add_nonneg (Rat.add_nonneg threebsq htwoprod) hasq
  have hleftprod :
      0 <= (b - a) * (b ^ 2 + 2 * a * b + 3 * a ^ 2) :=
    Rat.mul_nonneg hba hleft
  have hrightprod :
      0 <= (b - a) * (3 * b ^ 2 + 2 * a * b + a ^ 2) :=
    Rat.mul_nonneg hba hright
  constructor <;> grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add,
    Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

/- The finite kernel for the secant of the monomial `x^(n+1)`.  It is
defined by the same recurrence as the finite factorization quotient, so its
use below stays entirely within rational arithmetic. -/
def monomialSecantKernel (a b : Rat) : Nat -> Rat
  | 0 => 1
  | n + 1 => a ^ (n + 1) + b * monomialSecantKernel a b n

private theorem monomial_power_mono_nonneg {a b : Rat}
    (ha : 0 <= a) (hab : a <= b) (n : Nat) :
    a ^ n <= b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Rat.pow_succ, Rat.pow_succ]
      have hleft := Rat.mul_le_mul_of_nonneg_right ih ha
      have hb : 0 <= b := by grind
      have hbn : 0 <= b ^ n := Rat.pow_nonneg hb
      have hright := Rat.mul_le_mul_of_nonneg_left hab hbn
      exact Rat.le_trans hleft hright

private theorem monomialSecantKernel_factorization {a b : Rat} {n : Nat}
    (hne : b - a ≠ 0) :
    (b ^ (n + 1) - a ^ (n + 1)) / (b - a) =
      monomialSecantKernel a b n := by
  induction n with
  | zero =>
      unfold monomialSecantKernel
      rw [Rat.div_def]
      have hcancel : (b - a) * (b - a)⁻¹ = 1 :=
        Rat.mul_inv_cancel (b - a) hne
      grind [Rat.sub_eq_add_neg]
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        Rat.pow_succ, monomialSecantKernel]
      rw [Rat.div_def]
      have hcancel : (b - a) * (b - a)⁻¹ = 1 :=
        Rat.mul_inv_cancel (b - a) hne
      have hstep :
          (b ^ (n + 1) - a ^ (n + 1)) * (b - a)⁻¹ =
            monomialSecantKernel a b n := by
        simpa [Rat.div_def] using ih
      grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
        Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

private theorem monomialSecantKernel_lower {a b : Rat}
    (ha : 0 <= a) (hab : a <= b) (n : Nat) :
    (n + 1 : Rat) * a ^ n <= monomialSecantKernel a b n := by
  induction n with
  | zero =>
      unfold monomialSecantKernel
      grind
  | succ n ih =>
      rw [monomialSecantKernel]
      have hb : 0 <= b := by grind
      have hpow : 0 <= a ^ n := Rat.pow_nonneg ha
      have hstep : a ^ n * a <= a ^ n * b :=
        Rat.mul_le_mul_of_nonneg_left hab hpow
      have hscaled :
          (n + 1 : Rat) * (a ^ n * a) <=
            (n + 1 : Rat) * (a ^ n * b) :=
        Rat.mul_le_mul_of_nonneg_left hstep (by grind)
      have hihb :
          (n + 1 : Rat) * (a ^ n * b) <=
            b * monomialSecantKernel a b n := by
        have hmul := Rat.mul_le_mul_of_nonneg_left ih hb
        grind [Rat.mul_assoc, Rat.mul_comm]
      rw [Rat.pow_succ]
      calc
        (↑(n + 1) + 1) * (a ^ n * a) <=
            (n + 1 : Rat) * (a ^ n * b) + a ^ n * a := by
              grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul]
        _ <= b * monomialSecantKernel a b n + a ^ n * a :=
              (Rat.add_le_add_right).2 hihb
        _ = a ^ n * a + b * monomialSecantKernel a b n := by
              grind [Rat.add_comm]

private theorem monomialSecantKernel_upper {a b : Rat}
    (ha : 0 <= a) (hab : a <= b) (n : Nat) :
    monomialSecantKernel a b n <= (n + 1 : Rat) * b ^ n := by
  induction n with
  | zero =>
      unfold monomialSecantKernel
      grind
  | succ n ih =>
      rw [monomialSecantKernel]
      have hb : 0 <= b := by grind
      have hpow : 0 <= b ^ n := Rat.pow_nonneg hb
      have hstep : a ^ (n + 1) <= b ^ (n + 1) :=
        monomial_power_mono_nonneg ha hab (n + 1)
      have hscaled := Rat.mul_le_mul_of_nonneg_left ih hb
      have hstep' : a ^ n * a <= b ^ (n + 1) := by
        simpa [Rat.pow_succ] using hstep
      rw [Rat.pow_succ]
      calc
        a ^ n * a + b * monomialSecantKernel a b n <=
            b ^ (n + 1) + b * monomialSecantKernel a b n :=
              (Rat.add_le_add_right).2 hstep'
        _ <= b ^ (n + 1) + b * ((n + 1 : Rat) * b ^ n) :=
              (Rat.add_le_add_left).2 hscaled
        _ = (↑(n + 1) + 1) * b ^ (n + 1) := by
              rw [Rat.pow_succ]
              grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul]

/-- A finite monomial mean-value bracket.  For a nonnegative rational
interval `[a,b]`, the secant quotient of `x^(n+1)` is bounded by the two
endpoint finite-power derivatives `(n+1)*a^n` and `(n+1)*b^n`.

The proof is a finite factorization and positivity induction: it selects no
intermediate point and assumes neither a limit nor completeness. -/
theorem monomial_succ_secant_derivative_bracket {a b : Rat} (n : Nat)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    (n + 1 : Rat) * a ^ n <=
        differenceQuotient (fun z => z ^ (n + 1)) a (b - a) /\
      differenceQuotient (fun z => z ^ (n + 1)) a (b - a) <=
        (n + 1 : Rat) * b ^ n := by
  have hfactor :=
    monomialSecantKernel_factorization (a := a) (b := b) (n := n) hne
  have hkernelLower := monomialSecantKernel_lower ha hab n
  have hkernelUpper := monomialSecantKernel_upper ha hab n
  have hquotient :
      differenceQuotient (fun z => z ^ (n + 1)) a (b - a) =
        monomialSecantKernel a b n := by
    unfold differenceQuotient
    have habsum : a + (b - a) = b := by grind
    rw [habsum]
    exact hfactor
  rw [hquotient]
  exact ⟨hkernelLower, hkernelUpper⟩

/- A finite mesh transport for a mean-value-style certificate.  Each cell
supplies a rational bracket for its forward secant (the finite derivative
certificate), and telescoping transports the common bracket to the whole
endpoint secant.  The endpoint relation and positive mesh width are explicit;
no intermediate point, limit, or completeness principle is used. -/
theorem secant_of_finite_derivative_bracket
    {f : Rat -> Rat} {a b h lower upper : Rat} {n : Nat}
    (hn : 0 < n) (hh : 0 < h)
    (hend : b = a + (n : Rat) * h)
    (hcell : ∀ k : Nat, k < n →
      lower <= differenceQuotient f (a + (k : Rat) * h) h /\
        differenceQuotient f (a + (k : Rat) * h) h <= upper) :
    lower <= differenceQuotient f a (b - a) /\
      differenceQuotient f a (b - a) <= upper := by
  have hmesh : ∀ m : Nat,
      m <= n ->
      lower * (m : Rat) * h <= f (a + (m : Rat) * h) - f a /\
        f (a + (m : Rat) * h) - f a <= upper * (m : Rat) * h := by
    intro m
    induction m with
    | zero =>
        intro _
        constructor <;> grind
    | succ m ih =>
        intro hm
        have hlocal := hcell m (by omega)
        have hprev := ih (by omega)
        unfold differenceQuotient at hlocal
        have hstep :
            (a + (↑m : Rat) * h) + h = a + (↑(m + 1) : Rat) * h := by
          rw [Rat.natCast_add]
          grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
            Rat.mul_assoc, Rat.mul_comm]
        rw [hstep] at hlocal
        constructor
        · have hscaled := Rat.mul_le_mul_of_nonneg_right hlocal.1
            (Rat.le_of_lt hh)
          rw [Rat.div_def] at hscaled
          have hcancel : h⁻¹ * h = 1 := Rat.inv_mul_cancel _
            (Rat.ne_of_gt hh)
          have hinc :
              lower * h <=
                f (a + (↑(m + 1) : Rat) * h) - f (a + (↑m : Rat) * h) := by
            calc
              lower * h <=
                  (f (a + (↑(m + 1) : Rat) * h) -
                    f (a + (↑m : Rat) * h)) * h⁻¹ * h := hscaled
              _ = f (a + (↑(m + 1) : Rat) * h) -
                    f (a + (↑m : Rat) * h) := by
                rw [Rat.mul_assoc, hcancel, Rat.mul_one]
          have hadd := rat_add_le_add hprev.1 hinc
          rw [Rat.natCast_add]
          grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
            Rat.mul_assoc, Rat.mul_comm]
        · have hscaled := Rat.mul_le_mul_of_nonneg_right hlocal.2
            (Rat.le_of_lt hh)
          rw [Rat.div_def] at hscaled
          have hcancel : h⁻¹ * h = 1 := Rat.inv_mul_cancel _
            (Rat.ne_of_gt hh)
          have hinc :
              f (a + (↑(m + 1) : Rat) * h) - f (a + (↑m : Rat) * h) <=
                upper * h := by
            calc
              f (a + (↑(m + 1) : Rat) * h) -
                    f (a + (↑m : Rat) * h) =
                  (f (a + (↑(m + 1) : Rat) * h) -
                    f (a + (↑m : Rat) * h)) * h⁻¹ * h := by
                rw [Rat.mul_assoc, hcancel, Rat.mul_one]
              _ <= upper * h := hscaled
          have hadd := rat_add_le_add hprev.2 hinc
          rw [Rat.natCast_add]
          grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
            Rat.mul_assoc, Rat.mul_comm]
  have hba : b - a = (n : Rat) * h := by grind
  rw [hba, differenceQuotient]
  have hmeshN := hmesh n (Nat.le_refl n)
  have hdenpos : 0 < (n : Rat) * h :=
    Rat.mul_pos ((Rat.natCast_pos).2 hn) hh
  rw [Rat.div_def]
  have hcancel : ((n : Rat) * h)⁻¹ * ((n : Rat) * h) = 1 :=
    Rat.inv_mul_cancel _ (Rat.ne_of_gt hdenpos)
  constructor
  · apply Rat.le_of_mul_le_mul_right (c := (n : Rat) * h)
    · rw [Rat.mul_assoc, hcancel]
      grind [hmeshN.1]
    · exact hdenpos
  · apply Rat.le_of_mul_le_mul_right (c := (n : Rat) * h)
    · rw [Rat.mul_assoc, hcancel]
      grind [hmeshN.2]
    · exact hdenpos

/- A generic finite bisection budget for rational brackets.  The denominator
is the exact number of subintervals after `n` halvings, so the statement is
an algorithmic termination/error certificate rather than a claim about a
completed limit or an attained root. -/
def rationalBisectionWidth (a b : Rat) (n : Nat) : Rat :=
  (b - a) / (((2 ^ n : Nat) : Rat))

theorem rationalBisectionWidth_le_error_budget
    {a b eps : Rat} {n : Nat}
    (hbudget : b - a <= eps * (((2 ^ n : Nat) : Rat))) :
    rationalBisectionWidth a b n <= eps := by
  unfold rationalBisectionWidth
  have hpowNat : 0 < 2 ^ n := Nat.pow_pos (by omega)
  have hpow : 0 < (((2 ^ n : Nat) : Rat)) :=
    (Rat.natCast_pos).2 hpowNat
  have hpowne : (((2 ^ n : Nat) : Rat)) ≠ 0 := Rat.ne_of_gt hpow
  apply Rat.le_of_mul_le_mul_right
    (c := (((2 ^ n : Nat) : Rat)))
  · rw [Rat.div_def, Rat.mul_assoc]
    have hcancel : (((2 ^ n : Nat) : Rat))⁻¹ *
        (((2 ^ n : Nat) : Rat)) = 1 := by
      rw [Rat.mul_comm]
      exact Rat.mul_inv_cancel _ hpowne
    rw [hcancel]
    simpa using hbudget
  · exact hpow

/-- The exact finite-difference product decomposition with the second factor
evaluated at the right endpoint.  This is the algebraic core of the product
rule before any continuity or limiting certificate is invoked. -/
theorem product_differenceQuotient_right
    (u v : Rat -> Rat) (x h : Rat) (hh : h ≠ 0) :
    (u (x + h) * v (x + h) - u x * v x) / h =
      u x * ((v (x + h) - v x) / h) +
        v (x + h) * ((u (x + h) - u x) / h) := by
  rw [Rat.div_def]
  have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The equivalent finite-difference product decomposition with both main
terms evaluated at the left endpoint.  The last term is the explicit corner
remainder which a constructive product-derivative proof must bound. -/
theorem product_differenceQuotient_corner
    (u v : Rat -> Rat) (x h : Rat) (hh : h ≠ 0) :
    (u (x + h) * v (x + h) - u x * v x) / h =
      u x * ((v (x + h) - v x) / h) +
        v x * ((u (x + h) - u x) / h) +
          h * ((u (x + h) - u x) / h) *
            ((v (x + h) - v x) / h) := by
  rw [Rat.div_def]
  have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The finite product-rule error is bounded by the two supplied
difference-quotient errors and one explicit corner remainder.  This is a
rational inequality, before it is lifted to interval enclosures or any
continuity certificate. -/
theorem product_differenceQuotient_error_le_qabs
    (u du v dv : Rat -> Rat) (x h : Rat) (hh : h ≠ 0) :
    qabs (differenceQuotient (fun z => u z * v z) x h -
      (u x * dv x + v x * du x)) <=
      qabs (u x) * qabs (differenceQuotient v x h - dv x) +
        qabs (v x) * qabs (differenceQuotient u x h - du x) +
          qabs h * qabs (differenceQuotient u x h) *
            qabs (differenceQuotient v x h) := by
  have hdecomp :
      differenceQuotient (fun z => u z * v z) x h -
          (u x * dv x + v x * du x) =
        u x * (differenceQuotient v x h - dv x) +
          v x * (differenceQuotient u x h - du x) +
            h * differenceQuotient u x h * differenceQuotient v x h := by
    unfold differenceQuotient
    rw [product_differenceQuotient_corner u v x h hh]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  rw [hdecomp]
  calc
    qabs
        (u x * (differenceQuotient v x h - dv x) +
          v x * (differenceQuotient u x h - du x) +
            h * differenceQuotient u x h * differenceQuotient v x h) <=
        qabs
          (u x * (differenceQuotient v x h - dv x) +
            v x * (differenceQuotient u x h - du x)) +
          qabs (h * differenceQuotient u x h * differenceQuotient v x h) :=
      qabs_add_le _ _
    _ <= (qabs (u x * (differenceQuotient v x h - dv x)) +
          qabs (v x * (differenceQuotient u x h - du x))) +
          qabs (h * differenceQuotient u x h * differenceQuotient v x h) :=
      (Rat.add_le_add_right).2 (qabs_add_le _ _)
    _ = qabs (u x) * qabs (differenceQuotient v x h - dv x) +
          qabs (v x) * qabs (differenceQuotient u x h - du x) +
            qabs h * qabs (differenceQuotient u x h) *
              qabs (differenceQuotient v x h) := by
      rw [qabs_mul, qabs_mul, qabs_mul, qabs_mul]

/-- The nonnegative-step form of the two-sided product-error estimate.  This
is convenient for forward mesh arguments, while the absolute-step theorem
above is the form used by the interval derivative interface. -/
theorem product_differenceQuotient_error_le
    (u du v dv : Rat -> Rat) (x h : Rat) (hh : h ≠ 0) (h0 : 0 <= h) :
    qabs (differenceQuotient (fun z => u z * v z) x h -
      (u x * dv x + v x * du x)) <=
      qabs (u x) * qabs (differenceQuotient v x h - dv x) +
        qabs (v x) * qabs (differenceQuotient u x h - du x) +
          h * qabs (differenceQuotient u x h) *
            qabs (differenceQuotient v x h) := by
  calc
    qabs (differenceQuotient (fun z => u z * v z) x h -
      (u x * dv x + v x * du x)) <=
        qabs (u x) * qabs (differenceQuotient v x h - dv x) +
          qabs (v x) * qabs (differenceQuotient u x h - du x) +
            qabs h * qabs (differenceQuotient u x h) *
              qabs (differenceQuotient v x h) :=
      product_differenceQuotient_error_le_qabs u du v dv x h hh
    _ = qabs (u x) * qabs (differenceQuotient v x h - dv x) +
          qabs (v x) * qabs (differenceQuotient u x h - du x) +
            h * qabs (differenceQuotient u x h) *
              qabs (differenceQuotient v x h) := by
      rw [qabs_eq_self_of_nonneg h0]
end ExactFunction

namespace QInterval

def scaleRat (r : Rat) (I : QInterval) : QInterval :=
  if 0 <= r then
    { lo := r * I.lo, hi := r * I.hi }
  else
    { lo := r * I.hi, hi := r * I.lo }

def neg (I : QInterval) : QInterval :=
  { lo := -I.hi, hi := -I.lo }

def sub (I J : QInterval) : QInterval :=
  { lo := I.lo - J.hi, hi := I.hi - J.lo }

def divRat (I : QInterval) (h : Rat) : QInterval :=
  scaleRat (1 / h) I

def differenceQuotient (fxh fx : QInterval) (h : Rat) : QInterval :=
  divRat (sub fxh fx) h

/-- A difference quotient of two ordered interval enclosures is itself an
ordered interval, for either sign of the rational step. -/
theorem differenceQuotient_ordered
    (fxh fx : QInterval)
    (hxh : fxh.lo <= fxh.hi) (hx : fx.lo <= fx.hi) (h : Rat) :
    (differenceQuotient fxh fx h).lo <=
      (differenceQuotient fxh fx h).hi := by
  have hsub : fxh.lo - fx.hi <= fxh.hi - fx.lo := by grind
  unfold differenceQuotient divRat sub scaleRat
  split
  · exact Rat.mul_le_mul_of_nonneg_left hsub ‹0 <= 1 / h›
  · have hinv : 1 / h <= 0 :=
      Rat.le_of_lt (Rat.not_le.mp ‹¬0 <= 1 / h›)
    exact rat_mul_le_mul_of_nonpos_left hsub hinv

/-- Refining both endpoint enclosures narrows their rational difference
quotient, including when the step is negative. -/
theorem differenceQuotient_contains_of_contains
    {A B A' B' : QInterval} (hA : A.ContainsInterval A')
    (hB : B.ContainsInterval B') (h : Rat) :
    (differenceQuotient B A h).ContainsInterval
      (differenceQuotient B' A' h) := by
  have hleft : B.lo - A.hi <= B'.lo - A'.hi := by
    rcases hA with ⟨_, ha⟩
    rcases hB with ⟨hb, _⟩
    grind
  have hright : B'.hi - A'.lo <= B.hi - A.lo := by
    rcases hA with ⟨ha, _⟩
    rcases hB with ⟨_, hb⟩
    grind
  unfold differenceQuotient divRat sub scaleRat
  split
  · exact ⟨Rat.mul_le_mul_of_nonneg_left hleft ‹0 <= 1 / h›,
      Rat.mul_le_mul_of_nonneg_left hright ‹0 <= 1 / h›⟩
  · have hn : 1 / h <= 0 :=
      Rat.le_of_lt (Rat.not_le.mp ‹¬0 <= 1 / h›)
    exact ⟨rat_mul_le_mul_of_nonpos_left hright hn,
      rat_mul_le_mul_of_nonpos_left hleft hn⟩

/-- Refining both intervals in a near pair costs at most three times the
original tolerance: the gap and both refined widths are each bounded by the
original near tolerance. -/
theorem nearAt_refine {A B A' B' : QInterval} {eps delta : QPos}
    (h : A.NearAt B eps) (hA : A.ContainsInterval A')
    (hB : B.ContainsInterval B')
    (ha : A'.lo <= A'.hi) (hb : B'.lo <= B'.hi)
    (hbudget : 3 * eps.val <= delta.val) : A'.NearAt B' delta := by
  rcases h with ⟨h1, h2, h3, h4⟩
  rcases hA with ⟨ha1, ha2⟩
  rcases hB with ⟨hb1, hb2⟩
  have he := eps.property
  unfold NearAt width at *
  constructor
  · grind
  constructor
  · grind
  constructor <;> grind

/-! Finite difference quotients distribute over interval addition.  This is
the interval counterpart of the exact rational identity above; the proof is
just endpoint arithmetic, with the sign split belonging to interval division.
No limiting argument is involved. -/
theorem differenceQuotient_addInterval
    (A B C D : QInterval) (h : Rat) :
    differenceQuotient (addInterval A B) (addInterval C D) h =
      addInterval (differenceQuotient A C h)
        (differenceQuotient B D h) := by
  by_cases hinv : 0 <= 1 / h
  · cases A
    cases B
    cases C
    cases D
    simp [differenceQuotient, divRat, sub, addInterval, scaleRat,
      Rat.div_def, hinv]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
  · cases A
    cases B
    cases C
    cases D
    simp [differenceQuotient, divRat, sub, addInterval, scaleRat,
      Rat.div_def, hinv]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

/-- Subtracting interval enclosures adds their widths exactly. -/
theorem sub_width (I J : QInterval) :
    (sub I J).width = I.width + J.width := by
  unfold sub width
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- Nonnegative scaling preserves the exact width factor. -/
theorem scaleRat_width_of_nonneg {r : Rat} (hr : 0 <= r) (I : QInterval) :
    (scaleRat r I).width = r * I.width := by
  unfold scaleRat width
  rw [if_pos hr]
  grind [Rat.sub_eq_add_neg, Rat.mul_add]

/-- Nonnegative scaling preserves finite interval overlap. -/
theorem scaleRat_overlaps_of_nonneg {r : Rat} (hr : 0 <= r)
    {I J : QInterval} (hover : I.Overlaps J) :
    (scaleRat r I).Overlaps (scaleRat r J) := by
  unfold scaleRat QInterval.Overlaps
  simp only [if_pos hr]
  constructor
  · exact Rat.mul_le_mul_of_nonneg_left hover.1 hr
  · exact Rat.mul_le_mul_of_nonneg_left hover.2 hr

/-- Nonnegative scaling also preserves enclosure. -/
theorem scaleRat_contains_of_nonneg {r : Rat} (hr : 0 <= r)
    {outer inner : QInterval} (hcontains : outer.ContainsInterval inner) :
    (scaleRat r outer).ContainsInterval (scaleRat r inner) := by
  unfold scaleRat QInterval.ContainsInterval
  simp only [if_pos hr]
  constructor
  · exact Rat.mul_le_mul_of_nonneg_left hcontains.1 hr
  · exact Rat.mul_le_mul_of_nonneg_left hcontains.2 hr

theorem differenceQuotient_scaleRat_of_nonneg {r : Rat} (hr : 0 <= r)
    (A B : QInterval) (h : Rat) :
    differenceQuotient (scaleRat r A) (scaleRat r B) h =
      scaleRat r (differenceQuotient A B h) := by
  by_cases hinv : 0 <= 1 / h
  · cases A
    cases B
    simp [differenceQuotient, divRat, sub, scaleRat, Rat.div_def,
      if_pos hr, hinv]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
  · cases A
    cases B
    simp [differenceQuotient, divRat, sub, scaleRat, Rat.div_def,
      if_pos hr, hinv]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

theorem differenceQuotient_neg (A B : QInterval) (h : Rat) :
    differenceQuotient (neg A) (neg B) h =
      neg (differenceQuotient A B h) := by
  by_cases hinv : 0 <= 1 / h
  · cases A
    cases B
    simp [differenceQuotient, divRat, sub, neg, scaleRat,
      Rat.div_def, hinv]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
  · cases A
    cases B
    simp [differenceQuotient, divRat, sub, neg, scaleRat,
      Rat.div_def, hinv]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

/-! Negative scalar multiplication is reduced to the already-certified
nonnegative case plus endpoint negation.  Keeping this identity explicit
prevents a sign-sensitive interval multiplication from being hidden in a
later derivative proof. -/
theorem scaleRat_neg_eq_neg_scaleRat_neg {r : Rat} (hr : r < 0)
    (I : QInterval) :
    scaleRat r I = neg (scaleRat (-r) I) := by
  have hr0pos : 0 < -r := by
    simpa using (Rat.neg_lt_neg hr)
  have hr0 : 0 <= -r := Rat.le_of_lt hr0pos
  unfold scaleRat neg
  rw [if_neg (Rat.not_le.mpr hr),
    if_pos hr0]
  cases I
  dsimp
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
    Rat.mul_comm, Rat.add_comm, Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

theorem differenceQuotient_scaleRat_of_neg {r : Rat} (hr : r < 0)
    (A B : QInterval) (h : Rat) :
    differenceQuotient (scaleRat r A) (scaleRat r B) h =
      scaleRat r (differenceQuotient A B h) := by
  rw [scaleRat_neg_eq_neg_scaleRat_neg hr A,
    scaleRat_neg_eq_neg_scaleRat_neg hr B,
    differenceQuotient_neg]
  rw [differenceQuotient_scaleRat_of_nonneg (by grind : 0 <= -r)]
  exact (scaleRat_neg_eq_neg_scaleRat_neg hr
    (differenceQuotient A B h)).symm

/-- Dividing the difference of two exact singleton boxes gives the exact
rational difference quotient.  The sign split in interval division is harmless
here because both endpoints coincide. -/
theorem differenceQuotient_singleton
    (y x h : Rat) :
    differenceQuotient { lo := y, hi := y } { lo := x, hi := x } h =
      { lo := (y - x) / h, hi := (y - x) / h } := by
  unfold differenceQuotient divRat sub scaleRat
  simp [Rat.div_def, Rat.mul_comm]

/-! A positive cell width cancels the interval quotient denominator.  This is
the algebraic bridge used by the effective FTC: a finite secant enclosure can
be transported back to an endpoint-difference enclosure before the local
boxes are summed. -/

theorem scaleRat_differenceQuotient_of_pos
    {A B : QInterval} {h : Rat} (hpos : 0 < h) :
    scaleRat h (differenceQuotient B A h) = sub B A := by
  have hnonneg : 0 <= h := Rat.le_of_lt hpos
  have hne : h ≠ 0 := Rat.ne_of_gt hpos
  unfold differenceQuotient divRat scaleRat sub
  simp only [if_pos hnonneg]
  rw [if_pos]
  · simp only [Rat.div_def]
    have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hne
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.sub_eq_add_neg]
  · exact by
      rw [Rat.div_def]
      exact Rat.mul_nonneg (by decide +kernel)
        (Rat.le_of_lt ((Rat.inv_pos).2 hpos))

theorem nearAt_symm {I J : QInterval} {eps : QPos} :
    I.NearAt J eps -> J.NearAt I eps := by
  intro h
  unfold NearAt at *
  rcases h with ⟨hIJ, hJI, hIw, hJw⟩
  exact ⟨hJI, hIJ, hJw, hIw⟩

/-! A near secant quotient gives a concrete scaled endpoint enclosure. -/

theorem scaleRat_differenceQuotient_contains_of_near
    {A B D : QInterval} {h : Rat} {eps : QPos}
    (hpos : 0 < h)
    (hnear : (differenceQuotient B A h).NearAt D eps) :
    (scaleRat h (expand D (2 * eps.val))).ContainsInterval (sub B A) := by
  have hnear' : D.NearAt (differenceQuotient B A h) eps :=
    nearAt_symm hnear
  have hcontains := expand_contains_right_of_near hnear'
  have hscaled := scaleRat_contains_of_nonneg
    (Rat.le_of_lt hpos) hcontains
  rw [scaleRat_differenceQuotient_of_pos hpos] at hscaled
  exact hscaled

/-- Reversing a positive finite step reverses both interval endpoints and the
sign of its denominator, leaving the enclosure of the difference quotient
unchanged.  This is the finite algebra needed to transport a forward
derivative certificate to a backward step. -/
theorem differenceQuotient_reverse_of_pos {A B : QInterval} {h : Rat}
    (hpos : 0 < h) :
    differenceQuotient B A (-h) = differenceQuotient A B h := by
  have hhne : h ≠ 0 := Rat.ne_of_gt hpos
  have hnegne : -h ≠ 0 := by grind
  have hinvpos' : 0 < h⁻¹ := (Rat.inv_pos).2 hpos
  have hinvneg_eq : (-h)⁻¹ = -h⁻¹ := by
    have hnegmul : (-h) * (-h⁻¹) = 1 := by
      have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hhne
      grind [Rat.mul_assoc, Rat.mul_comm]
    calc
      (-h)⁻¹ = (-h)⁻¹ * 1 := by grind
      _ = (-h)⁻¹ * ((-h) * (-h⁻¹)) := by rw [hnegmul]
      _ = ((-h)⁻¹ * (-h)) * (-h⁻¹) := by
        rw [Rat.mul_assoc]
      _ = 1 * (-h⁻¹) := by
        rw [Rat.inv_mul_cancel _ hnegne]
      _ = -h⁻¹ := by grind
  have hinvpos : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt hinvpos'
  have hinvneg : ¬ 0 <= 1 / (-h) := by
    rw [Rat.div_def]
    rw [hinvneg_eq]
    apply Rat.not_le.mpr
    simpa using Rat.neg_lt_neg hinvpos'
  unfold differenceQuotient divRat sub scaleRat
  rw [if_neg hinvneg, if_pos hinvpos]
  rw [Rat.div_def, hinvneg_eq]
  cases A
  cases B
  dsimp
  congr 1 <;>
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.mul_comm]

/-- A finite secant certificate can be converted directly into the endpoint
difference enclosure used by the FTC layer.  More precisely, if the interval
quotient over a positive rational step is near a derivative box, then the
endpoint difference lies in the step times that box widened by twice the
requested tolerance.  The second tolerance pays for the quotient box's own
width; no limiting or completeness principle is involved. -/
theorem scaleByRat_expand_contains_subInterval_of_differenceQuotient_near
    {A B D : QInterval} {h : Rat} {eps : QPos}
    (hpos : 0 < h)
    (hnear : (differenceQuotient B A h).NearAt D eps) :
    (scaleByRat h (expand D (2 * eps.val))).ContainsInterval
      (subInterval B A) := by
  have h0 : 0 <= h := Rat.le_of_lt hpos
  have hne : h ≠ 0 := Rat.ne_of_gt hpos
  have hinv : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
  have hcancel : h * (1 / h) = 1 := by
    simpa [Rat.div_def] using Rat.mul_inv_cancel h hne
  have hlo : (1 / h) * (B.lo - A.hi) <= D.hi + eps.val := by
    simpa [differenceQuotient, divRat, sub, scaleRat, if_pos hinv] using
      hnear.1
  have hDlo : D.lo <= (1 / h) * (B.hi - A.lo) + eps.val := by
    simpa [differenceQuotient, divRat, sub, scaleRat, if_pos hinv] using
      hnear.2.1
  have hwidth :
      (1 / h) * (B.hi - A.lo) - (1 / h) * (B.lo - A.hi) <= eps.val := by
    simpa [differenceQuotient, divRat, sub, scaleRat, if_pos hinv,
      QInterval.width] using hnear.2.2.1
  have hDlo' : D.lo - 2 * eps.val <= (1 / h) * (B.lo - A.hi) := by
    grind [Rat.sub_eq_add_neg]
  have hDhi' : (1 / h) * (B.hi - A.lo) <= D.hi + 2 * eps.val := by
    grind [Rat.sub_eq_add_neg]
  unfold ContainsInterval scaleByRat expand subInterval
  rw [if_pos h0]
  constructor
  · calc
      h * (D.lo - 2 * eps.val) <=
          h * ((1 / h) * (B.lo - A.hi)) :=
            Rat.mul_le_mul_of_nonneg_left hDlo' h0
      _ = B.lo - A.hi := by
            rw [← Rat.mul_assoc, hcancel]
            grind
  · calc
      B.hi - A.lo = h * ((1 / h) * (B.hi - A.lo)) := by
        rw [← Rat.mul_assoc, hcancel]
        grind
      _ <= h * (D.hi + 2 * eps.val) :=
            Rat.mul_le_mul_of_nonneg_left hDhi' h0

/-- Combine two finite nearness certificates into one derivative-bound box.

The first certificate places a positive-step secant near a derivative box;
the second places a candidate value near a possibly differently evaluated
base derivative box.  The hull of the two twice-widened boxes contains both
the candidate value and the scaled endpoint difference.  Its width is at
most ten times the requested tolerance.  This is the local algebra needed to
combine a step-aware derivative evaluator with a continuity evaluator before
forming a common FTC cell bound. -/
theorem common_secant_derivative_bound_of_near
    {A B secantDerivative baseDerivative candidateValue : QInterval}
    {h : Rat} {eps : QPos}
    (hpos : 0 < h)
    (hsecant :
      (differenceQuotient B A h).NearAt secantDerivative eps)
    (hvalue : baseDerivative.NearAt candidateValue eps)
    (hover : secantDerivative.Overlaps baseDerivative)
    (hsecantOrdered : 0 <= secantDerivative.width)
    (hbaseOrdered : 0 <= baseDerivative.width) :
    let bound :=
      hull (expand secantDerivative (2 * eps.val))
        (expand baseDerivative (2 * eps.val))
    bound.ContainsInterval candidateValue /\
      (scaleByRat h bound).ContainsInterval (subInterval B A) /\
        bound.width <= 10 * eps.val := by
  let left := expand secantDerivative (2 * eps.val)
  let right := expand baseDerivative (2 * eps.val)
  let bound := hull left right
  have hzero : 0 <= eps.val := Rat.le_of_lt eps.property
  have hvalueRight : right.ContainsInterval candidateValue := by
    dsimp [right]
    exact expand_contains_right_of_near hvalue
  have hboundRight : bound.ContainsInterval right := by
    dsimp [bound]
    exact hull_contains_right left right
  have hcandidate : bound.ContainsInterval candidateValue :=
    ⟨Rat.le_trans hboundRight.1 hvalueRight.1,
      Rat.le_trans hvalueRight.2 hboundRight.2⟩
  have hsecantLeft :
      (scaleByRat h left).ContainsInterval (subInterval B A) := by
    dsimp [left]
    exact scaleByRat_expand_contains_subInterval_of_differenceQuotient_near
      hpos hsecant
  have hboundLeft : bound.ContainsInterval left := by
    dsimp [bound]
    exact hull_contains_left left right
  have hscaledBound :
      (scaleByRat h bound).ContainsInterval (scaleByRat h left) :=
    scaleByRat_contains_of_nonneg (Rat.le_of_lt hpos) hboundLeft
  have hendpoint :
      (scaleByRat h bound).ContainsInterval (subInterval B A) :=
    ⟨Rat.le_trans hscaledBound.1 hsecantLeft.1,
      Rat.le_trans hsecantLeft.2 hscaledBound.2⟩
  have hleftOrdered : 0 <= left.width := by
    rw [show left = expand secantDerivative (2 * eps.val) by rfl,
      expand_width]
    grind [Rat.mul_nonneg]
  have hrightOrdered : 0 <= right.width := by
    rw [show right = expand baseDerivative (2 * eps.val) by rfl,
      expand_width]
    grind [Rat.mul_nonneg]
  have hleftRightOverlap : left.Overlaps right := by
    dsimp [left, right]
    unfold Overlaps at hover
    unfold Overlaps expand
    constructor <;> grind [Rat.sub_eq_add_neg]
  have hwidth :
      bound.width <= left.width + right.width := by
    dsimp [bound]
    exact hull_width_le_add_of_overlaps hleftOrdered hrightOrdered
      hleftRightOverlap
  have hwidthBound : bound.width <= 10 * eps.val := by
    calc
      bound.width <= left.width + right.width := hwidth
      _ = (secantDerivative.width + 2 * (2 * eps.val)) +
            (baseDerivative.width + 2 * (2 * eps.val)) := by
            rw [show left = expand secantDerivative (2 * eps.val) by rfl,
              show right = expand baseDerivative (2 * eps.val) by rfl,
              expand_width, expand_width]
      _ <= 10 * eps.val := by
            have hsecantWidth : secantDerivative.width <= eps.val :=
              hsecant.2.2.2
            have hbaseWidth : baseDerivative.width <= eps.val :=
              hvalue.2.2.1
            grind
  exact ⟨hcandidate, hendpoint, hwidthBound⟩

end QInterval

/-- Two identical exact singleton boxes are near at every requested precision.
This small lemma is the interval-valued replacement for treating a rational
calculation as an exact real value. -/
theorem intervalNearAtPrecision_singleton_self (q : Rat) (n : Nat) :
    intervalNearAtPrecision { lo := q, hi := q } { lo := q, hi := q } n := by
  unfold intervalNearAtPrecision QInterval.NearAt QInterval.width
  have heps : 0 <= (precisionAtStage n).val :=
    Rat.le_of_lt (precisionAtStage n).property
  constructor
  · grind
  constructor
  · grind
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- Two interval functions represent the same function on the same rational
interval when all point-values overlap at every precision.

This is deliberately local to a chosen interval; raw partial functions with
different domains do not have a global transitive equivalence relation. -/
def FunctionOnInterval.Equivalent (f g : FunctionOnInterval) : Prop :=
  f.lower = g.lower /\
  f.upper = g.upper /\
  forall x
      (hxF : inDomainInterval f.lower f.upper x)
      (hxG : inDomainInterval g.lower g.upper x),
    (PartialRealFunRaw.apply f.raw f.valid_on x (f.defined_on x hxF)).Equiv
      (PartialRealFunRaw.apply g.raw g.valid_on x (g.defined_on x hxG))

/-- Arbitrarily close cofinal lower endpoints imply equality of represented
functions. This exposes the exact convergence step needed after a quantitative
mesh comparison: for each rational input and each pair of requested raw
stages, later mesh samples must be cofinal and their lower endpoints must be
arbitrarily close. -/
theorem FunctionOnInterval.equivalent_of_cofinal_lower_endpoint_closeness
    {f g : FunctionOnInterval}
    (hlower : f.lower = g.lower) (hupper : f.upper = g.upper)
    (hclose : forall x
      (hxF : inDomainInterval f.lower f.upper x)
      (hxG : inDomainInterval g.lower g.upper x)
      n m (eps : QPos),
      exists N M, n <= N /\ m <= M /\
        qabs
          (((PartialRealFunRaw.apply f.raw f.valid_on x (f.defined_on x hxF)).compute N).lo -
           ((PartialRealFunRaw.apply g.raw g.valid_on x (g.defined_on x hxG)).compute M).lo)
          <= eps.val) :
    FunctionOnInterval.Equivalent f g := by
  refine ⟨hlower, hupper, ?_⟩
  intro x hxF hxG
  have hFvalid :
      (PartialRealFunRaw.apply f.raw f.valid_on x (f.defined_on x hxF)).Valid :=
    f.valid_on x (f.defined_on x hxF)
  have hGvalid :
      (PartialRealFunRaw.apply g.raw g.valid_on x (g.defined_on x hxG)).Valid :=
    g.valid_on x (g.defined_on x hxG)
  apply RealCompute.equiv_of_cofinal_lower_endpoint_closeness
    hFvalid hGvalid
  intro n m eps
  obtain ⟨N, M, hnN, hmM, hsample⟩ := hclose x hxF hxG n m eps
  exact ⟨N, M, hnN, hmM, hsample⟩

namespace FunctionOnInterval

/-! Equivalence edges form the local representation graph for a function.
These laws are proved at the `realCompute` level, so a chain of different native
stage schedules can be composed without selecting a completed function. -/

theorem equivalent_refl (f : FunctionOnInterval) :
    Equivalent f f := by
  refine ⟨rfl, rfl, ?_⟩
  intro x hxF hxG
  exact RealCompute.equiv_refl
    (PartialRealFunRaw.apply f.raw f.valid_on x (f.defined_on x hxF))
    (f.valid_on x (f.defined_on x hxF))

theorem equivalent_symm {f g : FunctionOnInterval}
    (h : Equivalent f g) : Equivalent g f := by
  refine ⟨h.1.symm, h.2.1.symm, ?_⟩
  intro x hxG hxF
  have hfg := h.2.2 x hxF hxG
  exact RealCompute.equiv_symm hfg

theorem equivalent_trans {f g h : FunctionOnInterval}
    (hfg : Equivalent f g) (hgh : Equivalent g h) :
    Equivalent f h := by
  refine ⟨hfg.1.trans hgh.1, hfg.2.1.trans hgh.2.1, ?_⟩
  intro x hxF hxH
  have hxG : inDomainInterval g.lower g.upper x := by
    simpa [← hfg.1, ← hfg.2.1] using hxF
  have hFvalid :
      (PartialRealFunRaw.apply f.raw f.valid_on x
        (f.defined_on x hxF)).Valid := by
    change RealCompute.ValidCompute (f.raw.compute x (f.defined_on x hxF))
    exact f.valid_on x (f.defined_on x hxF)
  have hGvalid :
      (PartialRealFunRaw.apply g.raw g.valid_on x
        (g.defined_on x hxG)).Valid := by
    change RealCompute.ValidCompute (g.raw.compute x (g.defined_on x hxG))
    exact g.valid_on x (g.defined_on x hxG)
  have hHvalid :
      (PartialRealFunRaw.apply h.raw h.valid_on x
        (h.defined_on x hxH)).Valid := by
    change RealCompute.ValidCompute (h.raw.compute x (h.defined_on x hxH))
    exact h.valid_on x (h.defined_on x hxH)
  exact RealCompute.equiv_trans hFvalid hGvalid hHvalid
    (hfg.2.2 x hxF hxG) (hgh.2.2 x hxG hxH)

/-! Product evaluation transports along the local representation graph. -/
theorem equivalent_mulOfNonnegBounded
    (F F' G G' : FunctionOnInterval)
    (hFF' : Equivalent F F') (hGG' : Equivalent G G')
    (same_lower_FG : F.lower = G.lower) (same_upper_FG : F.upper = G.upper)
    (same_lower_F'G' : F'.lower = G'.lower) (same_upper_F'G' : F'.upper = G'.upper)
    (Fbounds : forall x (hx : inDomainInterval F.lower F.upper x),
      Exists fun B : Rat => 0 < B /\ forall n,
        0 <= (F.compute x hx n).lo /\ (F.compute x hx n).hi <= B)
    (Gbounds : forall x (hx : inDomainInterval G.lower G.upper x),
      Exists fun B : Rat => 0 < B /\ forall n,
        0 <= (G.compute x hx n).lo /\ (G.compute x hx n).hi <= B)
    (F'bounds : forall x (hx : inDomainInterval F'.lower F'.upper x),
      Exists fun B : Rat => 0 < B /\ forall n,
        0 <= (F'.compute x hx n).lo /\ (F'.compute x hx n).hi <= B)
    (G'bounds : forall x (hx : inDomainInterval G'.lower G'.upper x),
      Exists fun B : Rat => 0 < B /\ forall n,
        0 <= (G'.compute x hx n).lo /\ (G'.compute x hx n).hi <= B) :
    Equivalent
      (mulOfNonnegBounded F G same_lower_FG same_upper_FG Fbounds Gbounds)
      (mulOfNonnegBounded F' G' same_lower_F'G' same_upper_F'G' F'bounds G'bounds) := by
  refine ⟨hFF'.1, hFF'.2.1, ?_⟩
  intro x hx hx'
  let hxG : inDomainInterval G.lower G.upper x :=
    ⟨by rw [← same_lower_FG]; exact hx.1, by rw [← same_upper_FG]; exact hx.2⟩
  let hxG' : inDomainInterval G'.lower G'.upper x :=
    ⟨by rw [← same_lower_F'G']; exact hx'.1, by rw [← same_upper_F'G']; exact hx'.2⟩
  have hnonneg : forall (H : FunctionOnInterval)
      (bounds : forall y (hy : inDomainInterval H.lower H.upper y),
        Exists fun B : Rat => 0 < B /\ forall n,
          0 <= (H.compute y hy n).lo /\ (H.compute y hy n).hi <= B)
      (y : Rat) (hy : inDomainInterval H.lower H.upper y) n,
      0 <= (H.raw.compute y (H.defined_on y hy) n).lo := by
    intro H bounds y hy n
    rcases bounds y hy with ⟨B, hB, h⟩
    exact (h n).1
  have hXF : (PartialRealFunRaw.apply F.raw F.valid_on x
      (F.defined_on x hx)).Valid := by
    change RealCompute.ValidCompute (F.raw.compute x (F.defined_on x hx))
    exact F.valid_on x (F.defined_on x hx)
  have hXG : (PartialRealFunRaw.apply G.raw G.valid_on x
      (G.defined_on x hxG)).Valid := by
    change RealCompute.ValidCompute (G.raw.compute x (G.defined_on x hxG))
    exact G.valid_on x (G.defined_on x hxG)
  have hXF' : (PartialRealFunRaw.apply F'.raw F'.valid_on x
      (F'.defined_on x hx')).Valid := by
    change RealCompute.ValidCompute (F'.raw.compute x (F'.defined_on x hx'))
    exact F'.valid_on x (F'.defined_on x hx')
  have hXG' : (PartialRealFunRaw.apply G'.raw G'.valid_on x
      (G'.defined_on x hxG')).Valid := by
    change RealCompute.ValidCompute (G'.raw.compute x (G'.defined_on x hxG'))
    exact G'.valid_on x (G'.defined_on x hxG')
  have h := RealCompute.mul_equiv_of_nonneg
    hXF hXF' hXG hXG'
    (hnonneg F Fbounds x hx) (hnonneg F' F'bounds x hx')
    (hnonneg G Gbounds x hxG) (hnonneg G' G'bounds x hxG')
    (hFF'.2.2 x hx hx') (hGG'.2.2 x hxG hxG')
  change (RealCompute.mul
      (PartialRealFunRaw.apply F.raw F.valid_on x (F.defined_on x hx))
      (PartialRealFunRaw.apply G.raw G.valid_on x (G.defined_on x hxG))).Equiv
    (RealCompute.mul
      (PartialRealFunRaw.apply F'.raw F'.valid_on x (F'.defined_on x hx'))
      (PartialRealFunRaw.apply G'.raw G'.valid_on x (G'.defined_on x hxG')))
  exact h

end FunctionOnInterval

/-- Effective derivative on a rational interval.

For every requested output precision, small enough rational steps make the
finite-difference interval lie within the derivative interval's requested
tolerance.  Literal overlap would incorrectly demand equality at every finite
nonzero step. -/
structure HasDerivativeOnInterval (f df : FunctionOnInterval) where
  same_lower : df.lower = f.lower
  same_upper : df.upper = f.upper
  stepPrecision : Nat -> Nat
  /-- Interval evaluators need a step-aware precision schedule: a fixed
  nonzero box width would be magnified without bound when divided by an
  arbitrarily smaller rational step. -/
  evalPrecision : Rat -> Rat -> Nat -> Nat
  close :
    forall x h n
      (hx : inDomainInterval f.lower f.upper x)
      (hxh : inDomainInterval f.lower f.upper (x + h))
      (hdx : inDomainInterval df.lower df.upper x),
      h ≠ 0 ->
      qabs h <= (1 / ((stepPrecision n : Nat) : Rat)) ->
        intervalNearAtPrecision
          (QInterval.differenceQuotient
            (f.compute (x + h) hxh (evalPrecision x h n))
            (f.compute x hx (evalPrecision x h n))
            h)
          (df.compute x hdx (evalPrecision x h n))
          n

/-- Restrict a derivative certificate to a closed rational subinterval. The
underlying computations and precision schedules are unchanged; only interval
membership evidence is transported into the original domain. This is the
derivative-side closure operation needed when local ODE uniqueness is proved
on a finite rational partition. -/
def HasDerivativeOnInterval.restrict
    {f df : FunctionOnInterval} (D : HasDerivativeOnInterval f df)
    (a b : Rat) (hlo : f.lower <= a) (hab : a <= b)
    (hhi : b <= f.upper) :
    HasDerivativeOnInterval
      (FunctionOnInterval.restrict f a b hlo hab hhi)
      (FunctionOnInterval.restrict df a b
        (by rw [D.same_lower]; exact hlo) hab
        (by rw [D.same_upper]; exact hhi)) where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := D.stepPrecision
  evalPrecision := D.evalPrecision
  close := by
    intro x h n hx hxh hdx hh hsmall
    have hx' : inDomainInterval f.lower f.upper x :=
      ⟨Rat.le_trans hlo hx.1, Rat.le_trans hx.2 hhi⟩
    have hxh' : inDomainInterval f.lower f.upper (x + h) :=
      ⟨Rat.le_trans hlo hxh.1, Rat.le_trans hxh.2 hhi⟩
    have hdx' : inDomainInterval df.lower df.upper x := by
      rw [D.same_lower, D.same_upper]
      exact hx'
    have hclose := D.close x h n hx' hxh' hdx' hh hsmall
    simpa [FunctionOnInterval.restrict, FunctionOnInterval.compute] using hclose

/-- Reindex an interval function by a cofinal computation-stage schedule.
This changes its raw evaluator while retaining the same rational domain. -/
def FunctionOnInterval.reindexStages (f : FunctionOnInterval)
    (sigma : RealCompute.StageSchedule) : FunctionOnInterval where
  raw :=
    { definedAt := f.raw.definedAt
      compute := fun x hx n => f.raw.compute x hx (sigma.stage n) }
  lower := f.lower
  upper := f.upper
  defined_on := f.defined_on
  valid_on := by
    intro x hx
    let value : RealCompute := { compute := fun n => f.raw.compute x hx n }
    have hvalid := RealCompute.schedule_valid value (f.valid_on x hx) sigma
    change RealCompute.Valid (RealCompute.schedule sigma value)
    exact hvalid

@[simp] theorem FunctionOnInterval.reindexStages_compute (f : FunctionOnInterval)
    (sigma : RealCompute.StageSchedule) (x : Rat)
    (hx : inDomainInterval f.lower f.upper x) (n : Nat) :
    (f.reindexStages sigma).compute x hx n = f.compute x hx (sigma.stage n) := rfl

/-- A cofinal stage schedule changes the computation, but not its represented
value at any rational input. -/
theorem FunctionOnInterval.reindexStages_equivalent (f : FunctionOnInterval)
    (sigma : RealCompute.StageSchedule) :
    FunctionOnInterval.Equivalent f (f.reindexStages sigma) := by
  refine ⟨rfl, rfl, ?_⟩
  intro x hxF hxG
  have hx : inDomainInterval f.lower f.upper x := hxF
  change ({ compute := f.compute x hx } : RealCompute).Equiv
    (RealCompute.schedule sigma ({ compute := f.compute x hx } : RealCompute))
  exact RealCompute.schedule_equiv
    ({ compute := f.compute x hx } : RealCompute)
    (f.valid_on x (f.defined_on x hx)) sigma

/-- Reindex a function and its derivative evaluator by the same cofinal
stage schedule. The derivative proof chooses a finer request for the original
certificate, then encloses each reindexed quotient and derivative box inside
the corresponding original boxes. Thus its exact equality meaning is
preserved while the executable stage schedule changes. -/
def HasDerivativeOnInterval.reindexStages
    {f df : FunctionOnInterval} (D : HasDerivativeOnInterval f df)
    (sigma : RealCompute.StageSchedule)
    (inner step : Nat -> Nat) (eval : Rat -> Rat -> Nat -> Nat)
    (hbudget : forall n,
      3 * (precisionAtStage (inner n)).val <= (precisionAtStage n).val)
    (hstep : forall n,
      1 / ((step n : Nat) : Rat) <=
        1 / ((D.stepPrecision (inner n) : Nat) : Rat))
    (heval : forall x h n,
      D.evalPrecision x h (inner n) <= sigma.stage (eval x h n)) :
    HasDerivativeOnInterval (f.reindexStages sigma) (df.reindexStages sigma) where
  same_lower := D.same_lower
  same_upper := D.same_upper
  stepPrecision := step
  evalPrecision := eval
  close := by
    intro x h n hx hxh hdx hh hsmall
    have hsmall' := Rat.le_trans hsmall (hstep n)
    have hold := D.close x h (inner n) hx hxh hdx hh hsmall'
    let oldStage := D.evalPrecision x h (inner n)
    let newStage := sigma.stage (eval x h n)
    have hstage : oldStage <= newStage := heval x h n
    have hxF : inDomainInterval f.lower f.upper x := hx
    have hxhF : inDomainInterval f.lower f.upper (x + h) := hxh
    have hdxF : inDomainInterval df.lower df.upper x := hdx
    have hfx := (f.valid_on x (f.defined_on x hxF)).2.1
      oldStage newStage hstage
    have hfxh := (f.valid_on (x + h) (f.defined_on (x + h) hxhF)).2.1
      oldStage newStage hstage
    have hdf := (df.valid_on x (df.defined_on x hdxF)).2.1
      oldStage newStage hstage
    have hquotient := QInterval.differenceQuotient_contains_of_contains
      ⟨hfx.1, hfx.2.2⟩ ⟨hfxh.1, hfxh.2.2⟩ h
    have hleftOrdered :
        (f.compute (x + h) hxhF newStage).lo <=
          (f.compute (x + h) hxhF newStage).hi := by
      have hw := (f.valid_on (x + h) (f.defined_on (x + h) hxhF)).1 newStage
      change 0 <= (f.compute (x + h) hxhF newStage).width at hw
      grind [QInterval.width]
    have hbaseOrdered :
        (f.compute x hxF newStage).lo <= (f.compute x hxF newStage).hi := by
      have hw := (f.valid_on x (f.defined_on x hxF)).1 newStage
      change 0 <= (f.compute x hxF newStage).width at hw
      grind [QInterval.width]
    have hquotientOrdered := QInterval.differenceQuotient_ordered
      (f.compute (x + h) hxhF newStage) (f.compute x hxF newStage)
      hleftOrdered hbaseOrdered h
    have hdfOrdered :
        (df.compute x hdxF newStage).lo <= (df.compute x hdxF newStage).hi := by
      have hw := (df.valid_on x (df.defined_on x hdxF)).1 newStage
      change 0 <= (df.compute x hdxF newStage).width at hw
      grind [QInterval.width]
    change QInterval.NearAt
      (QInterval.differenceQuotient
        (f.compute (x + h) hxhF newStage) (f.compute x hxF newStage) h)
      (df.compute x hdxF newStage) (precisionAtStage n)
    exact QInterval.nearAt_refine hold hquotient
      ⟨hdf.1, hdf.2.2⟩ hquotientOrdered hdfOrdered (hbudget n)

/-! A local FTC bridge for one positive rational cell.  The derivative
certificate controls the finite secant quotient; scaling that quotient back
by the cell width produces an enclosure of the endpoint difference.  The
explicit expansion pays twice the requested stage tolerance, so this is a
finite statement about rational interval computations rather than a limit
argument. -/
theorem HasDerivativeOnInterval.endpointDifference_contains_of_pos
    {f df : FunctionOnInterval}
    (D : HasDerivativeOnInterval f df)
    {x h : Rat} {n : Nat}
    (hx : inDomainInterval f.lower f.upper x)
    (hxh : inDomainInterval f.lower f.upper (x + h))
    (hdx : inDomainInterval df.lower df.upper x)
    (hpos : 0 < h)
    (hsmall : qabs h <=
      (1 / ((D.stepPrecision n : Nat) : Rat))) :
    (QInterval.scaleByRat h
      (QInterval.expand
        (df.compute x hdx (D.evalPrecision x h n))
        (2 * (precisionAtStage n).val))).ContainsInterval
      (QInterval.subInterval
        (f.compute (x + h) hxh (D.evalPrecision x h n))
        (f.compute x hx (D.evalPrecision x h n))) := by
  have hnear := D.close x h n hx hxh hdx (Rat.ne_of_gt hpos) hsmall
  change (QInterval.differenceQuotient
      (f.compute (x + h) hxh (D.evalPrecision x h n))
      (f.compute x hx (D.evalPrecision x h n)) h).NearAt
      (df.compute x hdx (D.evalPrecision x h n)) (precisionAtStage n) at hnear
  exact QInterval.scaleByRat_expand_contains_subInterval_of_differenceQuotient_near
    hpos hnear

/-! Closure under addition is stated for certificates using a common stage
schedule.  This is intentional: an evaluator's stage parameter is an
algorithmic resource, so combining two implementations must say how their
stages are synchronized.  The inner stage may be chosen finer than the
requested output stage to pay for the two summands' error budgets. -/
def HasDerivativeOnInterval.addOfCommonSchedule
    {f g df dg : FunctionOnInterval}
    (hf : HasDerivativeOnInterval f df)
    (hg : HasDerivativeOnInterval g dg)
    (hfgLower : f.lower = g.lower)
    (hfgUpper : f.upper = g.upper)
    (hdfgLower : df.lower = dg.lower)
    (hdfgUpper : df.upper = dg.upper)
    (hstep : hf.stepPrecision = hg.stepPrecision)
    (heval : hf.evalPrecision = hg.evalPrecision)
    (inner : Nat -> Nat)
    (hprecision : forall n,
      2 * (precisionAtStage (inner n)).val <= (precisionAtStage n).val) :
    HasDerivativeOnInterval
      (FunctionOnInterval.add f g hfgLower hfgUpper)
      (FunctionOnInterval.add df dg hdfgLower hdfgUpper) where
  same_lower := by
    calc
      (FunctionOnInterval.add df dg hdfgLower hdfgUpper).lower = df.lower := rfl
      _ = f.lower := hf.same_lower
      _ = (FunctionOnInterval.add f g hfgLower hfgUpper).lower := rfl
  same_upper := by
    calc
      (FunctionOnInterval.add df dg hdfgLower hdfgUpper).upper = df.upper := rfl
      _ = f.upper := hf.same_upper
      _ = (FunctionOnInterval.add f g hfgLower hfgUpper).upper := rfl
  stepPrecision := fun n => hf.stepPrecision (inner n)
  evalPrecision := fun x h n => hf.evalPrecision x h (inner n)
  close := by
    intro x h n hx hxh hdx hh hsmall
    have hxg : inDomainInterval g.lower g.upper x := by
      constructor
      · rw [← hfgLower]
        exact hx.1
      · rw [← hfgUpper]
        exact hx.2
    have hxhg : inDomainInterval g.lower g.upper (x + h) := by
      constructor
      · rw [← hfgLower]
        exact hxh.1
      · rw [← hfgUpper]
        exact hxh.2
    have hdxg : inDomainInterval dg.lower dg.upper x := by
      constructor
      · rw [← hdfgLower]
        exact hdx.1
      · rw [← hdfgUpper]
        exact hdx.2
    have hsmallG : qabs h <=
        (1 / ((hg.stepPrecision (inner n) : Nat) : Rat)) := by
      simpa [hstep] using hsmall
    have hcloseF := hf.close x h (inner n) hx hxh hdx hh hsmall
    have hcloseG₀ := hg.close x h (inner n) hxg hxhg hdxg hh hsmallG
    have hcloseG : intervalNearAtPrecision
        (QInterval.differenceQuotient
          (g.compute (x + h) hxhg (hf.evalPrecision x h (inner n)))
          (g.compute x hxg (hf.evalPrecision x h (inner n))) h)
        (dg.compute x hdxg (hf.evalPrecision x h (inner n))) (inner n) := by
      simpa [heval] using hcloseG₀
    have hcombined := intervalNearAtPrecision_addInterval
      hcloseF hcloseG (hprecision n)
    change intervalNearAtPrecision
      (QInterval.differenceQuotient
        (QInterval.addInterval
          (f.compute (x + h) hxh (hf.evalPrecision x h (inner n)))
          (g.compute (x + h) hxhg (hf.evalPrecision x h (inner n))))
        (QInterval.addInterval
          (f.compute x hx (hf.evalPrecision x h (inner n)))
          (g.compute x hxg (hf.evalPrecision x h (inner n)))) h)
      (QInterval.addInterval
        (df.compute x hdx (hf.evalPrecision x h (inner n)))
        (dg.compute x hdxg (hf.evalPrecision x h (inner n)))) n
    rw [QInterval.differenceQuotient_addInterval]
    exact hcombined

/-- A pointwise forward finite-difference derivative certificate.

This deliberately records only positive rational steps from one specified
basepoint.  It is useful for boundary calculations before the separate
two-sided and transport arguments needed by an interval derivative
certificate. -/
structure HasForwardDerivativeAt (f : FunctionOnInterval)
    (x : Rat) (derivative : RealCompute) where
  x_mem : inDomainInterval f.lower f.upper x
  derivative_valid : derivative.Valid
  stepPrecision : Nat -> Nat
  /-- The evaluator stage may depend on the positive rational step because
later non-exact certificates may divide a box by that step. -/
  evalPrecision : Rat -> Nat -> Nat
  close :
    forall h n
      (hxh : inDomainInterval f.lower f.upper (x + h)),
      0 < h ->
      h <= (1 / ((stepPrecision n : Nat) : Rat)) ->
        intervalNearAtPrecision
          (QInterval.differenceQuotient
            (f.compute (x + h) hxh (evalPrecision h n))
            (f.compute x x_mem (evalPrecision h n))
            h)
          (derivative.compute (evalPrecision h n))
          n

namespace FunctionOnInterval

/-! Pointwise negation preserves the rational chart and validity of interval
values. -/
def neg (F : FunctionOnInterval) : FunctionOnInterval where
  raw :=
    { definedAt := F.raw.definedAt
      compute := fun x hx n => QInterval.neg (F.raw.compute x hx n) }
  lower := F.lower
  upper := F.upper
  defined_on := F.defined_on
  valid_on := by
    intro x hx
    let X : RealCompute := { compute := F.raw.compute x hx }
    have hX : X.Valid := by
      change RealCompute.ValidCompute X.compute
      exact F.valid_on x hx
    change RealCompute.ValidCompute (RealCompute.negCompute X)
    exact RealCompute.negCompute_valid hX

@[simp] theorem neg_compute (F : FunctionOnInterval)
    (x : Rat) (hx : inDomainInterval F.lower F.upper x) (n : Nat) :
    (neg F).compute x hx n = QInterval.neg (F.compute x hx n) := by
  rfl

/-! Subtraction is exposed as addition with pointwise negation.  Keeping this
definition factored lets all validity and derivative closure proofs reuse the
two primitive finite interval operations. -/
def sub
    (F G : FunctionOnInterval)
    (same_lower : F.lower = G.lower)
    (same_upper : F.upper = G.upper) : FunctionOnInterval :=
  add F (neg G) same_lower same_upper

/-- Rationally scale every interval value of an interval-domain function.
The domain is deliberately unchanged: scalar multiplication is a pointwise
operation, not an extension of the function's rational chart. -/
def scaleRat (r : Rat) (F : FunctionOnInterval) : FunctionOnInterval where
  raw :=
    { definedAt := F.raw.definedAt
      compute := fun x hx n => QInterval.scaleRat r (F.raw.compute x hx n) }
  lower := F.lower
  upper := F.upper
  defined_on := by
    intro x hx
    exact F.defined_on x hx
  valid_on := by
    intro x hraw
    let X : RealCompute :=
      { compute := F.raw.compute x hraw }
    have hX : X.Valid := by
      change RealCompute.ValidCompute X.compute
      exact F.valid_on x hraw
    change RealCompute.ValidCompute
      (fun n => QInterval.scaleRat r (F.raw.compute x hraw n))
    change RealCompute.ValidCompute (RealCompute.scaleRatCompute r X)
    exact RealCompute.scaleRatCompute_valid (r := r) hX

/-- The pointwise evaluator for a rationally scaled interval function. -/
theorem scaleRat_compute (r : Rat) (F : FunctionOnInterval)
    (x : Rat) (hx : inDomainInterval F.lower F.upper x) (n : Nat) :
    (scaleRat r F).compute x hx n = QInterval.scaleRat r (F.compute x hx n) := by
  rfl

/-- Exact affine rational functions satisfy the interval-valued derivative
definition on every rational interval.  The certificate uses no limiting
operation: each finite quotient is literally the constant rational slope. -/
def exactRatAffineDerivative (a b m c : Rat) :
    HasDerivativeOnInterval
      (exactRat (fun x => m * x + c) a b)
      (exactRat (fun _x => m) a b) where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := fun _n => 1
  evalPrecision := fun _x _h _n => 0
  close := by
    intro x h n _hx _hxh _hdx hh _hsmall
    change intervalNearAtPrecision
      (QInterval.differenceQuotient
        { lo := m * (x + h) + c, hi := m * (x + h) + c }
        { lo := m * x + c, hi := m * x + c } h)
      { lo := m, hi := m } n
    rw [QInterval.differenceQuotient_singleton]
    have hcalc : (m * (x + h) + c - (m * x + c)) / h = m := by
      rw [Rat.div_def]
      have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc,
        Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    rw [hcalc]
    exact intervalNearAtPrecision_singleton_self m n

/-- The exact unit coordinate has derivative one in the interval-valued
finite-difference sense used by the calculus layer. -/
def exactRatIdDerivative (a b : Rat) :
    HasDerivativeOnInterval
      (exactRat (fun x => x) a b)
      (exactRat (fun _x => 1) a b) := by
  simpa [Rat.one_mul, Rat.add_zero] using
    exactRatAffineDerivative a b 1 0

/-- The exact square is the first non-affine example of the interval-valued
derivative definition.  Its finite quotient differs from twice its input by
exactly the signed step, so the precision-indexed step budget closes the four
interval-nearness inequalities without a limit principle. -/
def exactRatSquareDerivative (a b : Rat) :
    HasDerivativeOnInterval
      (exactRat (fun x => x * x) a b)
      (exactRat (fun x => 2 * x) a b) where
  same_lower := rfl
  same_upper := rfl
  stepPrecision := fun n => if n = 0 then 1 else n
  evalPrecision := fun _x _h _n => 0
  close := by
    intro x h n _hx _hxh _hdx hh hsmall
    change intervalNearAtPrecision
      (QInterval.differenceQuotient
        { lo := (x + h) * (x + h), hi := (x + h) * (x + h) }
        { lo := x * x, hi := x * x } h)
      { lo := 2 * x, hi := 2 * x } n
    rw [QInterval.differenceQuotient_singleton]
    have hcalc : ((x + h) * (x + h) - x * x) / h = 2 * x + h := by
      rw [Rat.div_def]
      have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc,
        Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    rw [hcalc]
    have hprecision : qabs h <= (precisionAtStage n).val := by
      change qabs h <=
        1 / (((if n = 0 then 1 else n : Nat) : Rat)) at hsmall
      by_cases hn : n = 0
      · subst n
        have hsmall' : qabs h <= 1 / (1 : Rat) := by
          simpa [if_pos rfl] using hsmall
        calc
          qabs h <= 1 / (1 : Rat) := hsmall'
          _ = (precisionAtStage 0).val := by decide +kernel
      · simpa [precisionAtStage, hn] using hsmall
    have hupper : h <= (precisionAtStage n).val :=
      Rat.le_trans (self_le_qabs h) hprecision
    have hlower : -h <= (precisionAtStage n).val :=
      Rat.le_trans (by simpa [qabs_neg] using self_le_qabs (-h)) hprecision
    unfold intervalNearAtPrecision QInterval.NearAt QInterval.width
    constructor
    · grind
    constructor
    · grind
    constructor <;> grind [Rat.sub_eq_add_neg]

end FunctionOnInterval

namespace QInterval

/-- Scaling both endpoint values by two commutes with the finite difference
quotient, including for a negative rational step. -/
theorem differenceQuotient_scaleRat_two (A B : QInterval) (h : Rat) :
    differenceQuotient (scaleRat 2 A) (scaleRat 2 B) h =
      scaleRat 2 (differenceQuotient A B h) := by
  have htwo : (0 : Rat) <= 2 := by decide +kernel
  by_cases hinv : 0 <= 1 / h
  · cases A
    cases B
    congr 1 <;>
      simp [differenceQuotient, divRat, sub, scaleRat, htwo, hinv] <;>
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]
  · cases A
    cases B
    congr 1 <;>
      simp [differenceQuotient, divRat, sub, scaleRat, htwo, hinv] <;>
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]

end QInterval

/-! A nonnegative rational scaling transports a finite near-certificate when
the internal error is multiplied into the requested output budget. -/
theorem intervalNearAtPrecision_scaleRat_of_nonneg
    {r : Rat} (hr : 0 <= r)
    {I J : QInterval} {m n : Nat}
    (hnear : intervalNearAtPrecision I J m)
    (hprecision : r * (precisionAtStage m).val <=
      (precisionAtStage n).val) :
    intervalNearAtPrecision (QInterval.scaleRat r I)
      (QInterval.scaleRat r J) n := by
  unfold intervalNearAtPrecision QInterval.NearAt at hnear ⊢
  rcases hnear with ⟨hleft, hright, hwidthI, hwidthJ⟩
  unfold QInterval.scaleRat
  simp only [if_pos hr]
  constructor
  · calc
      r * I.lo <= r * (J.hi + (precisionAtStage m).val) :=
        Rat.mul_le_mul_of_nonneg_left hleft hr
      _ = r * J.hi + r * (precisionAtStage m).val := by
        rw [Rat.mul_add]
      _ <= r * J.hi + (precisionAtStage n).val := by
        exact (Rat.add_le_add_left).2 hprecision
  constructor
  · calc
      r * J.lo <= r * (I.hi + (precisionAtStage m).val) :=
        Rat.mul_le_mul_of_nonneg_left hright hr
      _ = r * I.hi + r * (precisionAtStage m).val := by
        rw [Rat.mul_add]
      _ <= r * I.hi + (precisionAtStage n).val := by
        exact (Rat.add_le_add_left).2 hprecision
  constructor
  · change r * I.hi - r * I.lo <= (precisionAtStage n).val
    calc
      r * I.hi - r * I.lo = r * I.width := by
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg, Rat.mul_add]
      _ <= r * (precisionAtStage m).val :=
        Rat.mul_le_mul_of_nonneg_left hwidthI hr
      _ <= (precisionAtStage n).val := hprecision
  · change r * J.hi - r * J.lo <= (precisionAtStage n).val
    calc
      r * J.hi - r * J.lo = r * J.width := by
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg, Rat.mul_add]
      _ <= r * (precisionAtStage m).val :=
        Rat.mul_le_mul_of_nonneg_left hwidthJ hr
      _ <= (precisionAtStage n).val := hprecision

theorem intervalNearAtPrecision_neg
    {I J : QInterval} {n : Nat}
    (hnear : intervalNearAtPrecision I J n) :
    intervalNearAtPrecision (QInterval.neg I) (QInterval.neg J) n := by
  unfold intervalNearAtPrecision QInterval.NearAt at hnear ⊢
  rcases hnear with ⟨hleft, hright, hwidthI, hwidthJ⟩
  unfold QInterval.neg QInterval.width
  constructor
  · grind [Rat.sub_eq_add_neg]
  constructor
  · grind [Rat.sub_eq_add_neg]
  constructor
  · simpa [QInterval.width, Rat.sub_eq_add_neg, Rat.add_comm] using hwidthI
  · simpa [QInterval.width, Rat.sub_eq_add_neg, Rat.add_comm] using hwidthJ

/-- If two interval boxes are close at a sufficiently finer precision, then
doubling both boxes remains close at the requested precision.  This is the
finite error-budget step behind the scalar-multiple derivative rule. -/
theorem intervalNearAtPrecision_scaleRat_two
    {I J : QInterval} {m n : Nat}
    (hnear : intervalNearAtPrecision I J m)
    (hprecision : 2 * (precisionAtStage m).val <= (precisionAtStage n).val) :
    intervalNearAtPrecision (QInterval.scaleRat 2 I) (QInterval.scaleRat 2 J) n := by
  unfold intervalNearAtPrecision QInterval.NearAt at hnear ⊢
  rcases hnear with ⟨hleft, hright, hwidthI, hwidthJ⟩
  have htwo : (0 : Rat) <= 2 := by decide +kernel
  unfold QInterval.scaleRat
  simp only [if_pos htwo]
  constructor
  · calc
      2 * I.lo <= 2 * (J.hi + (precisionAtStage m).val) :=
        Rat.mul_le_mul_of_nonneg_left hleft htwo
      _ = 2 * J.hi + 2 * (precisionAtStage m).val := by
        grind [Rat.mul_add]
      _ <= 2 * J.hi + (precisionAtStage n).val :=
        (Rat.add_le_add_left).2 hprecision
  constructor
  · calc
      2 * J.lo <= 2 * (I.hi + (precisionAtStage m).val) :=
        Rat.mul_le_mul_of_nonneg_left hright htwo
      _ = 2 * I.hi + 2 * (precisionAtStage m).val := by
        grind [Rat.mul_add]
      _ <= 2 * I.hi + (precisionAtStage n).val :=
        (Rat.add_le_add_left).2 hprecision
  constructor
  · change 2 * I.hi - 2 * I.lo <= (precisionAtStage n).val
    calc
      2 * I.hi - 2 * I.lo = 2 * I.width := by
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg, Rat.mul_add]
      _ <= 2 * (precisionAtStage m).val :=
        Rat.mul_le_mul_of_nonneg_left hwidthI htwo
      _ <= (precisionAtStage n).val := hprecision
  · change 2 * J.hi - 2 * J.lo <= (precisionAtStage n).val
    calc
      2 * J.hi - 2 * J.lo = 2 * J.width := by
        unfold QInterval.width
        grind [Rat.sub_eq_add_neg, Rat.mul_add]
      _ <= 2 * (precisionAtStage m).val :=
        Rat.mul_le_mul_of_nonneg_left hwidthJ htwo
      _ <= (precisionAtStage n).val := hprecision

private theorem one_div_nat_antitone_for_derivative_precision {n m : Nat}
    (hn : 0 < n) (hm : 0 < m) (hnm : n <= m) :
    (1 / (m : Rat)) <= 1 / (n : Rat) := by
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat) * (m : Rat))
  · calc
      (1 / (m : Rat)) * ((n : Rat) * (m : Rat)) = (n : Rat) := by
        have hmne : (m : Rat) ≠ 0 := Rat.ne_of_gt ((Rat.natCast_pos).2 hm)
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= (m : Rat) := by exact_mod_cast hnm
      _ = (1 / (n : Rat)) * ((n : Rat) * (m : Rat)) := by
        have hnne : (n : Rat) ≠ 0 := Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact Rat.mul_pos ((Rat.natCast_pos).2 hn) ((Rat.natCast_pos).2 hm)

/-- The doubled function evaluates its derivative certificate at a finer
stage.  The resulting finite interval error remains within the original
precision budget after multiplication by two. -/
theorem precisionAtStage_scaleRat_two (n : Nat) :
    2 * (precisionAtStage (2 * (n + 1))).val <= (precisionAtStage n).val := by
  have hscaled :
      2 * (precisionAtStage (2 * (n + 1))).val =
        1 / (((n + 1 : Nat) : Rat)) := by
    have hstage : 2 * (n + 1) ≠ 0 := by omega
    change 2 * (1 / (((2 * (n + 1) : Nat) : Rat))) =
      1 / (((n + 1 : Nat) : Rat))
    rw [Rat.natCast_mul]
    rw [Rat.div_def, Rat.inv_mul_rev]
    have htwo : (2 : Rat) * (2 : Rat)⁻¹ = 1 := by decide +kernel
    grind [Rat.mul_assoc, Rat.mul_comm]
  rw [hscaled]
  by_cases hn : n = 0
  · subst n
    decide +kernel
  · rw [precisionAtStage, dif_neg hn]
    exact one_div_nat_antitone_for_derivative_precision
      (Nat.pos_of_ne_zero hn) (Nat.succ_pos n) (Nat.le_succ n)

/-- A two-sided interval derivative certificate is closed under multiplication
by two.  This is a literal rational-box calculation, not a topology or a
completed-real linearity rule. -/
def HasDerivativeOnInterval.scaleRat_two
    {f df : FunctionOnInterval}
    (D : HasDerivativeOnInterval f df) :
    HasDerivativeOnInterval
      (FunctionOnInterval.scaleRat 2 f)
      (FunctionOnInterval.scaleRat 2 df) where
  same_lower := D.same_lower
  same_upper := D.same_upper
  stepPrecision := fun n => D.stepPrecision (2 * (n + 1))
  evalPrecision := fun x h n => D.evalPrecision x h (2 * (n + 1))
  close := by
    intro x h n hx hxh hdx hh hsmall
    change inDomainInterval f.lower f.upper x at hx
    change inDomainInterval f.lower f.upper (x + h) at hxh
    change inDomainInterval df.lower df.upper x at hdx
    have hbase := D.close x h (2 * (n + 1)) hx hxh hdx hh hsmall
    have hscaled := intervalNearAtPrecision_scaleRat_two hbase
      (precisionAtStage_scaleRat_two n)
    simpa only [FunctionOnInterval.scaleRat_compute,
      QInterval.differenceQuotient_scaleRat_two] using hscaled

/-! General nonnegative rational scalar closure.  The caller supplies the
internal stage schedule and its finite error-budget proof; this keeps the
computational cost visible instead of baking in a convergence-rate theorem. -/
def HasDerivativeOnInterval.scaleRat_of_nonneg
    {r : Rat} (hr : 0 <= r)
    {f df : FunctionOnInterval}
    (D : HasDerivativeOnInterval f df)
    (inner : Nat -> Nat)
    (hprecision : forall n,
      r * (precisionAtStage (inner n)).val <= (precisionAtStage n).val) :
    HasDerivativeOnInterval
      (FunctionOnInterval.scaleRat r f)
      (FunctionOnInterval.scaleRat r df) where
  same_lower := D.same_lower
  same_upper := D.same_upper
  stepPrecision := fun n => D.stepPrecision (inner n)
  evalPrecision := fun x h n => D.evalPrecision x h (inner n)
  close := by
    intro x h n hx hxh hdx hh hsmall
    change inDomainInterval f.lower f.upper x at hx
    change inDomainInterval f.lower f.upper (x + h) at hxh
    change inDomainInterval df.lower df.upper x at hdx
    have hbase := D.close x h (inner n) hx hxh hdx hh hsmall
    have hscaled := intervalNearAtPrecision_scaleRat_of_nonneg hr
      hbase (hprecision n)
    simpa only [FunctionOnInterval.scaleRat_compute,
      QInterval.differenceQuotient_scaleRat_of_nonneg hr] using hscaled

/-! Full rational scalar closure.  Nonnegative scalars use interval scaling
directly; negative scalars use the proved sign decomposition and the negation
closure.  In both cases the caller supplies the finite precision budget
`|r| * eps_inner <= eps`. -/
def HasDerivativeOnInterval.scaleRat
    {r : Rat}
    {f df : FunctionOnInterval}
    (D : HasDerivativeOnInterval f df)
    (inner : Nat -> Nat)
    (hprecision : forall n,
      qabs r * (precisionAtStage (inner n)).val <=
        (precisionAtStage n).val) :
    HasDerivativeOnInterval
      (FunctionOnInterval.scaleRat r f)
      (FunctionOnInterval.scaleRat r df) := by
  by_cases hr : 0 <= r
  · exact D.scaleRat_of_nonneg hr inner (by
      intro n
      simpa [qabs_eq_self_of_nonneg hr] using hprecision n)
  · have hrneg : r < 0 := Rat.not_le.mp hr
    have hnonneg : 0 <= -r := by
      have hpos : 0 < -r := by
        simpa using (Rat.neg_lt_neg hrneg)
      exact Rat.le_of_lt hpos
    have hprecision' : forall n,
        (-r) * (precisionAtStage (inner n)).val <=
          (precisionAtStage n).val := by
      have hrq : qabs r = -r :=
        qabs_eq_neg_of_nonpos (Rat.le_of_lt hrneg)
      intro n
      simpa [hrq] using hprecision n
    refine
      { same_lower := D.same_lower
        same_upper := D.same_upper
        stepPrecision := fun n => D.stepPrecision (inner n)
        evalPrecision := fun x h n => D.evalPrecision x h (inner n)
        close := ?_ }
    intro x h n hx hxh hdx hh hsmall
    change inDomainInterval f.lower f.upper x at hx
    change inDomainInterval f.lower f.upper (x + h) at hxh
    change inDomainInterval df.lower df.upper x at hdx
    have hbase := D.close x h (inner n) hx hxh hdx hh hsmall
    have hscaled := intervalNearAtPrecision_scaleRat_of_nonneg hnonneg
      hbase (hprecision' n)
    have hneg := intervalNearAtPrecision_neg hscaled
    have hsecant :=
      (QInterval.scaleRat_neg_eq_neg_scaleRat_neg hrneg
        (QInterval.differenceQuotient
          (f.compute (x + h) hxh (D.evalPrecision x h (inner n)))
          (f.compute x hx (D.evalPrecision x h (inner n))) h)).symm
    have hderivative :=
      (QInterval.scaleRat_neg_eq_neg_scaleRat_neg hrneg
        (df.compute x hdx (D.evalPrecision x h (inner n)))).symm
    simpa only [FunctionOnInterval.scaleRat_compute,
      QInterval.differenceQuotient_scaleRat_of_neg hrneg, hsecant,
      hderivative] using hneg

/-! Negation needs no finer stage: it reverses both interval endpoints but
does not enlarge widths or the finite nearness budget. -/
def HasDerivativeOnInterval.neg
    {f df : FunctionOnInterval}
    (D : HasDerivativeOnInterval f df) :
    HasDerivativeOnInterval (FunctionOnInterval.neg f)
      (FunctionOnInterval.neg df) where
  same_lower := D.same_lower
  same_upper := D.same_upper
  stepPrecision := D.stepPrecision
  evalPrecision := D.evalPrecision
  close := by
    intro x h n hx hxh hdx hh hsmall
    change inDomainInterval f.lower f.upper x at hx
    change inDomainInterval f.lower f.upper (x + h) at hxh
    change inDomainInterval df.lower df.upper x at hdx
    have hbase := D.close x h n hx hxh hdx hh hsmall
    have hneg := intervalNearAtPrecision_neg hbase
    simpa only [FunctionOnInterval.neg_compute,
      QInterval.differenceQuotient_neg] using hneg

def HasDerivativeOnInterval.subOfCommonSchedule
    {f g df dg : FunctionOnInterval}
    (hf : HasDerivativeOnInterval f df)
    (hg : HasDerivativeOnInterval g dg)
    (hfgLower : f.lower = g.lower)
    (hfgUpper : f.upper = g.upper)
    (hdfgLower : df.lower = dg.lower)
    (hdfgUpper : df.upper = dg.upper)
    (hstep : hf.stepPrecision = hg.stepPrecision)
    (heval : hf.evalPrecision = hg.evalPrecision)
    (inner : Nat -> Nat)
    (hprecision : forall n,
      2 * (precisionAtStage (inner n)).val <= (precisionAtStage n).val) :
    HasDerivativeOnInterval
      (FunctionOnInterval.sub f g hfgLower hfgUpper)
      (FunctionOnInterval.add df (FunctionOnInterval.neg dg)
        hdfgLower hdfgUpper) := by
  simpa [FunctionOnInterval.sub] using
    (HasDerivativeOnInterval.addOfCommonSchedule hf (HasDerivativeOnInterval.neg hg)
      hfgLower hfgUpper hdfgLower hdfgUpper hstep heval inner hprecision)

/-! A named linear-combination wrapper for the two primitive closures.  The
scaled certificates are supplied explicitly so their sign splits and stage
schedules remain visible; this theorem only performs the common-chart
addition and its finite doubled-error budget. -/
def HasDerivativeOnInterval.linearCombinationOfCommonSchedule
    {r s : Rat} {f g df dg : FunctionOnInterval}
    (hf : HasDerivativeOnInterval
      (FunctionOnInterval.scaleRat r f)
      (FunctionOnInterval.scaleRat r df))
    (hg : HasDerivativeOnInterval
      (FunctionOnInterval.scaleRat s g)
      (FunctionOnInterval.scaleRat s dg))
    (hfgLower : (FunctionOnInterval.scaleRat r f).lower =
      (FunctionOnInterval.scaleRat s g).lower)
    (hfgUpper : (FunctionOnInterval.scaleRat r f).upper =
      (FunctionOnInterval.scaleRat s g).upper)
    (hdfgLower : (FunctionOnInterval.scaleRat r df).lower =
      (FunctionOnInterval.scaleRat s dg).lower)
    (hdfgUpper : (FunctionOnInterval.scaleRat r df).upper =
      (FunctionOnInterval.scaleRat s dg).upper)
    (hstep : hf.stepPrecision = hg.stepPrecision)
    (heval : hf.evalPrecision = hg.evalPrecision)
    (inner : Nat -> Nat)
    (hprecision : forall n,
      2 * (precisionAtStage (inner n)).val <= (precisionAtStage n).val) :
    HasDerivativeOnInterval
      (FunctionOnInterval.add
        (FunctionOnInterval.scaleRat r f)
        (FunctionOnInterval.scaleRat s g) hfgLower hfgUpper)
      (FunctionOnInterval.add
        (FunctionOnInterval.scaleRat r df)
        (FunctionOnInterval.scaleRat s dg) hdfgLower hdfgUpper) :=
  HasDerivativeOnInterval.addOfCommonSchedule hf hg
    hfgLower hfgUpper hdfgLower hdfgUpper hstep heval inner hprecision

/-- A function solving `f' = f` on an interval with a specified initial value.

This is the constructive uniqueness route for comparing exponential
representations without appealing to classical real completeness. -/
structure SolvesSelfDerivativeOnInterval (f : FunctionOnInterval) where
  derivative_self : HasDerivativeOnInterval f f
  /-- The small-step condition must admit positive rational steps at every
  requested precision. Without this field, choosing `stepPrecision n = 0`
  makes the implication in `HasDerivativeOnInterval.close` vacuous. -/
  step_precision_pos : forall n, 0 < derivative_self.stepPrecision n
  initial : Rat
  initial_mem : inDomainInterval f.lower f.upper initial
  initial_value : RealCompute
  initial_value_valid : initial_value.Valid
  initial_value_equiv :
    (PartialRealFunRaw.apply f.raw f.valid_on initial
      (f.defined_on initial initial_mem)).Equiv initial_value

/-- Uniqueness principle for `f' = f`.

The future proof should be constructive: estimate the difference of two
solutions on a finite rational subdivision, rather than invoking a classical
ODE theorem. The shared rational domain, initial coordinate, and raw-real
initial value are explicit hypotheses; none is inferred from the differential
equation. -/
def SelfDerivativeInitialValueUnique : Prop :=
  forall f g,
    (hf : SolvesSelfDerivativeOnInterval f) ->
    (hg : SolvesSelfDerivativeOnInterval g) ->
    f.lower = g.lower ->
    f.upper = g.upper ->
    hf.initial = hg.initial ->
    hf.initial_value.Equiv hg.initial_value ->
    FunctionOnInterval.Equivalent f g

end ComputableAnalysis


