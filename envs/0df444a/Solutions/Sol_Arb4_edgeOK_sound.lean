-- Prove2me | solution 1 for Arb4.edgeOK_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:35:08.310326+00:00
-- url     : https://prove2.me/submissions/1da6055a-a5ca-4035-9d5b-6567d8e14681

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Edge
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Side
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_ArgHoriz
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabClear
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_EdgeClearGlue
import Definitions.Def_ArdaRH65K_Turing121_H1000Octant
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_Arb4_Q_val_div
import Theorems.Thm_Arb4_pieceOK_sound
import Theorems.Thm_ArbEcon_Off_checkG_sound
import Theorems.Thm_ArbEcon_Off_initO_sound
import Theorems.Thm_ArbEcon_Off_stepO_sound
import Theorems.Thm_ArbEcon_OrderK_valid64
import Theorems.Thm_ArctanTaylor_arctan_le_self
import Theorems.Thm_ArctanTaylor_self_sub_cube_le_arctan
import Theorems.Thm_ArgHoriz_hAH_of_octCert_boxes
namespace Arb4.Q
end Arb4.Q
namespace ArbEcon
end ArbEcon
namespace ArbEcon.Off
end ArbEcon.Off
namespace ArbEcon.OrderK
end ArbEcon.OrderK
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
/-  Arb4_Q.lean -- lane Arb4 (h1000 compaction): exact rational arithmetic for Boolean kernel
    checkers.

    A certificate side condition such as the error budget of an octant piece is a polynomial
    inequality between explicit rationals.  Closing it by `norm_num` stores the whole normalisation
    trace in the olean (about 300 KB per budget at height 1000).  Here the same inequality is
    computed by `decide +kernel` over plain `Int`/`Nat` arithmetic (GMP-accelerated literals) and
    transported to `ℝ` by ONE soundness theorem per operation, proved once:

      * `Q`             -- an UNNORMALISED rational `n / (dm + 1)` (`n : ℤ`, `dm : ℕ`): the
                           denominator is positive by construction, so no positivity bookkeeping;
                           `val` is its real value, `frac n d` the rational `n / d` (`d ≥ 1`);
      * `add sub mul neg qabs npow div sumQ` -- the operations, `val_*` their homomorphism laws;
      * `le lt`         -- the Boolean comparisons, `le_sound`, `lt_sound`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/


namespace Arb4



namespace Q





























/-! ## The value homomorphism -/

theorem den_pos (a : Q) : (0 : ℝ) < (a.dm : ℝ) + 1 := by positivity

theorem den_ne (a : Q) : (a.dm : ℝ) + 1 ≠ 0 := ne_of_gt (den_pos a)

theorem val_frac (n : ℤ) {d : ℕ} (hd : 1 ≤ d) : (frac n d).val = (n : ℝ) / (d : ℝ) := by
  simp only [val, frac]
  rw [Nat.cast_sub hd]
  push_cast
  ring_nf

@[simp] theorem val_ofNat (m : ℕ) : (ofNat m).val = (m : ℝ) := by
  simp [val, ofNat]

@[simp] theorem val_ofInt (m : ℤ) : (ofInt m).val = (m : ℝ) := by
  simp [val, ofInt]

theorem cast_den_mul (a b : Q) :
    (((a.dm * b.dm + a.dm + b.dm : ℕ) : ℝ) + 1) = ((a.dm : ℝ) + 1) * ((b.dm : ℝ) + 1) := by
  push_cast; ring

theorem val_add (a b : Q) : (add a b).val = a.val + b.val := by
  have h1 := den_ne a
  have h2 := den_ne b
  simp only [val, add]
  rw [cast_den_mul]
  push_cast
  field_simp

theorem val_sub (a b : Q) : (sub a b).val = a.val - b.val := by
  have h1 := den_ne a
  have h2 := den_ne b
  simp only [val, sub]
  rw [cast_den_mul]
  push_cast
  field_simp

theorem val_mul (a b : Q) : (mul a b).val = a.val * b.val := by
  simp only [val, mul]
  rw [cast_den_mul]
  push_cast
  rw [mul_div_mul_comm]



theorem val_qabs (a : Q) : (qabs a).val = |a.val| := by
  simp only [val, qabs]
  rw [abs_div, abs_of_pos (den_pos a), Int.natCast_natAbs, Int.cast_abs]

theorem val_npow (a : Q) : ∀ k, (npow a k).val = a.val ^ k
  | 0 => by simp [npow, val]
  | k + 1 => by rw [npow, val_mul, val_npow a k, pow_succ]





/-! ## The comparisons -/

theorem le_sound {a b : Q} (h : le a b = true) : a.val ≤ b.val := by
  have hz : a.n * ((b.dm : ℤ) + 1) ≤ b.n * ((a.dm : ℤ) + 1) := of_decide_eq_true h
  have hr : (a.n : ℝ) * ((b.dm : ℝ) + 1) ≤ (b.n : ℝ) * ((a.dm : ℝ) + 1) := by exact_mod_cast hz
  simp only [val]
  rw [div_le_div_iff₀ (den_pos a) (den_pos b)]
  exact hr

theorem lt_sound {a b : Q} (h : lt a b = true) : a.val < b.val := by
  have hz : a.n * ((b.dm : ℤ) + 1) < b.n * ((a.dm : ℤ) + 1) := of_decide_eq_true h
  have hr : (a.n : ℝ) * ((b.dm : ℝ) + 1) < (b.n : ℝ) * ((a.dm : ℝ) + 1) := by exact_mod_cast hz
  simp only [val]
  rw [div_lt_div_iff₀ (den_pos a) (den_pos b)]
  exact hr



/-- `0 ≤ n` makes the value nonnegative. -/
theorem val_nonneg {a : Q} (hn : 0 ≤ a.n) : 0 ≤ a.val := by
  have hn' : (0 : ℝ) ≤ a.n := by exact_mod_cast hn
  exact div_nonneg hn' (den_pos a).le



/-! ## Literal conversions (small proof terms for the generated certificates) -/











end Q

end Arb4


/-  ArgHoriz.lean -- brick K6c of the ANDURIL Arb discharge: piecewise half-plane tracking of the
    horizontal argument change (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, inventory row
    H2e, brick K6c).

    THE BINDERS IT REDUCES.  Conjuncts 6 and 7 of the `hArbT` binder of every emitted Turing band
    (`TuringBand.BandStatement`, `BandGlue.BandData.EnclHyp`) are

        hAHt : DiffractionCore.argChangeHoriz riemannZeta T1 2 (-1) ∈ Set.Icc L2 H2,
        hAHb : DiffractionCore.argChangeHoriz riemannZeta T0 2 (-1) ∈ Set.Icc L3 H3,

    the argument change of ζ along the horizontal edges `[2, -1] + i T` of the RvM rectangle
    (20,758 binders at h280000, 13,235 distinct heights).  Unlike K6a/K6b these are NOT generic:
    they need values of ζ off the line.  This file proves the reduction theorem that turns them
    into a finite, kernel-checkable certificate, so that only ENCLOSURES remain.

    THE CERTIFICATE (`OctCert`).  Breakpoints `2 = p 0, p 1, ..., p m = -1` and one integer label
    `k j` per piece `[p j, p (j+1)]`, the octant direction `k j · π/4`.  It is valid when
      * `StepOK`   : consecutive labels differ by at most 3 (a decidable check on integers);
      * `NoCross`  : on piece `j`, ζ never crosses the line through 0 orthogonal to the octant
                     direction: `0 < α Re ζ(x + i T) + β Im ζ(x + i T)` for all `x` in the piece,
                     `(α, β) ∈ {(1,0),(1,1),(0,1),(-1,1),(-1,0),(-1,-1),(0,-1),(1,-1)}` the integer
                     octant vector (`octX`).  One strict sign condition per piece: a range
                     enclosure of ζ over the piece that avoids the octant boundary discharges it
                     (`octX_pos_of_box`, bundled per certificate as `OctCert.noCross_of_boxes`).
    Then (`argChangeHoriz_eq_of_octCert`, EXACT, no approximation):

        argChangeHoriz ζ T 2 (-1) = octAngle (k (m-1)) ζ(-1 + i T) - octAngle (k 0) ζ(2 + i T),
        octAngle k w = k π/4 + arctan ((α Im w - β Re w)/(α Re w + β Im w)).

    Every interior breakpoint cancels exactly: the chart angles of the two pieces meeting there
    agree (`chartAngle_eq`), because both charts contain the point and their directions differ by
    less than π.  So the only numerics left are TWO POINT ENCLOSURES, of ζ(2 + i T) and ζ(-1 + i T),
    turned into an arctan interval by `octAngle_mem_of_box` and the rational arctan brackets
    `atanLo ≤ arctan ≤ atanHi` (the emitter may use the sharper `ArctanTaylor.arctan_bracket`).
    `hAH_of_octCert_boxes` is the end-to-end binder-form statement.

    THE GENERAL THEOREM behind it (`argChangeHoriz_chain`): for any `f` analytic along the segment
    and any real chart directions `θ j` with `|θ (j+1) - θ j| < π` and `0 < Re (e^{-i θ j} f)` on
    piece `j`, the horizontal argument change is `chartAngle (θ (m-1)) f(end) - chartAngle (θ 0)
    f(start)`, `chartAngle θ w = θ + arg (e^{-i θ} w)` (FTC for `log (e^{-i θ} f)` on each piece).

    WHAT IS NOT HERE.  The off-line ζ evaluator (memo brick B6) that produces the `NoCross` range
    enclosures and the two endpoint point enclosures, and the functional-equation fold K6d.

    Trust: no hypotheses beyond those stated; axioms [propext, Classical.choice, Quot.sound]
    (see AxiomGuardArgChange.lean).  No `sorry`.

    conjecture1_proved = False.  A reduction of one edge of a finite zero count to finitely many
    enclosures; nothing here bears on the Riemann Hypothesis. -/





open Complex

namespace ArgHoriz

/-! ## 1. Charts: rotated principal arguments -/















/-! ## 2. One piece: FTC for `log (e^{-iθ} f)` -/



/-! ## 3. The chain of pieces -/



/-! ## 4. Octant charts: integer directions -/































/-! ## 5. The octant certificate -/



namespace OctCert





end OctCert





/-! ## 6. Endpoint enclosures -/















theorem atanLo_le (q : ℝ) : atanLo q ≤ Real.arctan q := by
  unfold atanLo
  split_ifs with h
  · exact ArctanTaylor.self_sub_cube_le_arctan h
  · have h' : 0 ≤ -q := by linarith
    have := ArctanTaylor.arctan_le_self h'
    rw [Real.arctan_neg] at this
    linarith

theorem le_atanHi (q : ℝ) : Real.arctan q ≤ atanHi q := by
  unfold atanHi
  split_ifs with h
  · exact ArctanTaylor.arctan_le_self h
  · have h' : 0 ≤ -q := by linarith
    have := ArctanTaylor.self_sub_cube_le_arctan h'
    rw [Real.arctan_neg] at this
    nlinarith



/-! ## 7. The ζ edge in binder form -/







/-! ## 8. Non-vacuity: the certificate on `f = id` -/





end ArgHoriz


/-  EMZetaOfflineSound.lean -- soundness of the off-line Nat-only evaluator (EMZetaOfflineEval).

    Every function of `EMZetaOfflineEval` produces a TRUE enclosure:
      * `imul_sound`     : the product `x · v` of a nonnegative bracket and a term ball;
      * `ampl_sound`     : the validated Newton root brackets `2^P m^(-σ)`, `σ = (a - b)/q`
                           (for ANY Newton output: the two kernel comparisons decide the bracket);
      * `termTB_sound`   : the term ball of `m^(-s) = m^(-σ)(cos θ - i sin θ)`, `θ = t log m`;
      * `addChain_sound` : accumulator `k` receives `(log m)^k m^(-s)`;
      * `stepO_sound`, `runO_sound`, `chunkO_sound` : the loop invariant `InvO` (log bracket and
                           the `p + 1` complex balls of `Σ_{m ≤ n} (log m)^k m^(-s)`).
    The log increment and the cos/sin kernels are `ArbEcon.logInc`/`ArbEcon.trig`, whose soundness
    (`ArbEcon.logInc_bound`, `ArbEcon.trig_sound`) is reused unchanged.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/



open Real Finset

namespace ArbEcon

namespace Off



/-! ## A. Specifications. -/















/-! ## B. The bracket-times-ball product. -/



/-! ## C. Term balls, accumulation, the log chain. -/







/-! ## D. The validated amplitude bracket. -/





/-! ## E. The term `m^(-s)`. -/





/-! ## F. The partial sums. -/







/-! ## G. One step, the run, the chunks. -/



theorem runO_sound (c : Cfg) (o : OCfg) (σ t : ℝ) (K : ℕ) (hv : Valid c t K) (ho : OValid c o σ) :
    ∀ (L n : ℕ) (s : StO), InvO c σ t n s → InvO c σ t (n + L) (runO c o L s) := by
  intro L
  induction L with
  | zero => intro n s h; exact h
  | succ L ih =>
    intro n s h
    have := ih (n + 1) (stepO c o s) (stepO_sound c o σ t K hv ho n s h)
    rw [show n + (L + 1) = n + 1 + L by ring]
    exact this













end Off

end ArbEcon


/-  EMZetaOfflineCheck.lean -- lane offline: the KERNEL-ONLY assembly of an order-(2K+1)
    Euler-Maclaurin enclosure of ζ(σ + i t) at a rational `σ = (a - b)/q` (any sign, `σ > -2K`) and a
    dyadic `t = tn / 2^tq > 0`.

      * `gpochG`, `pochRI_eq_gpochG`  -- the Gaussian-integer rising factorial
                                         `(q u)^k (σ + i t)_k` (`u = 2^tq`);
      * `corrDataG`, `corr_eqG`       -- the exact correction factor `emCorr K (σ + i t) N` as
                                         `(BreN + i BimN) / BD` in integers;
      * `pnG`, `pochNormSq_eq_pnG`    -- the remainder numerator `Π_{j<k} ((sN + j q)² u² + tn² q²)`;
      * `rpow_neg_le_of_pow`          -- `N^(-σ) ≤ Rn/Rd` from `Rd^q N^b ≤ Rn^q N^a`;
      * `remOddG`, `remOddG_sound`    -- the odd-saw remainder of `EMOff.em_zeta_orderK_enclosure_odd_ext`
                                         (valid off the line, `σ > -2K`) as `EN/ED`;
      * `zeta_ballG`                  -- the evaluator balls after `N-1` and `N` terms plus any remainder
                                         bound give balls for `Re ζ(s)`, `Im ζ(s)`;
      * `checkG`, `checkG_sound`      -- ONE Boolean checker (run by `decide +kernel`) and its
                                         soundness: `lo/D ≤ Re ζ(σ + i t) ≤ hi/D`, same for `Im`.

    conjecture1_proved = False.  Finite interval arithmetic at one point; nothing about RH.
-/




open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace ArbEcon

namespace Off

open ArbEcon.OrderK (betaN Lbeta  )

/-! ## A. The Gaussian-integer rising factorial at `σ = sN/q`, `t = tn/u`. -/















/-! ## B. The remainder numerator and `N^(-σ)`. -/







/-! ## C. The odd-saw remainder certificate, off the line. -/





/-! ## D. The ball: evaluator invariants + remainder + correction factor. -/







/-! ## E. The kernel checker and its soundness. -/









/-- The `k = 0` accumulator of an invariant state. -/
theorem accOK_head (c : Cfg) (σ t : ℝ) (n : ℕ) (s : StO) (x : Acc) (xs : List Acc)
    (hI : InvO c σ t n s) (hs : s.acc = x :: xs) : AccOK c.P (psumK σ t 0 n) x := by
  obtain ⟨_, _, _, _, hA⟩ := hI
  rw [hs] at hA
  exact hA.1

end Off

end ArbEcon


/-  H1000Octant.lean -- lane h1000-integrate: the kernel-checked OCTANT PIECE, the evaluator side of
    brick K6c (`ArgHoriz`) for the horizontal edges `[2, -1] + i T` of the RvM rectangles.

    `ArgHoriz.hAH_of_octCert_boxes` reduces `argChangeHoriz ζ T 2 (-1) ∈ [L, H]` to an octant
    certificate: breakpoints `2 = p 0 > p 1 > … > p m = -1`, one octant label `k j` per piece, and
    the no-crossing facts `0 < octX (k j) ζ(x + i T)` for every `x` of piece `j`, plus two point
    enclosures at `x = 2` and `x = -1`.  This file proves the no-crossing fact of ONE piece from ONE
    run of the off-line evaluator (`EMZetaOfflineEval`, `p + 1` accumulators) at the piece center
    `c = σc + i tc` and ONE Boolean check run by `decide +kernel`:

      A1. `emCorr_sub_le_norm`, `norm_emCorr_le_norm` -- the correction-factor bounds of
          `EMZetaOfflineSlab` with `a ≤ ‖c - 1‖` in place of `a ≤ Im c` (so they hold near `s = 1`
          at small heights);
      A2. `emFinite_taylor_le_G` -- the Taylor model of the EM finite part for ANY real part of the
          center: `‖n^(-c)‖ ≤ G` for `n ≤ N` (`G = 1` for `σc ≥ 0`, `N^(-σc)` for `σc < 0`);
      B.  `pochNormSq_mono_abs`, `em_remainder_horiz` -- the order-(2K+1) remainder uniformly on a
          horizontal segment `xlo ≤ x ≤ xhi` (negative `x` allowed, `x > -2K`);
          `natCpow_norm_le_of_pow` -- the `G` certificate `Gd^q N^b ≤ Gn^q N^a`;
      C.  `octLo`, `octUp`, `sumOct`, `checkOct`, `checkOct_sound` -- the kernel check
          `Σ_{k=1}^p |octX (W_k)| r^k/k! + (|α| + |β|) F < octX (W_0)` on the evaluator balls;
      D.  `piece_octX_pos` -- THE PIECE: for every real `x` with `|x - σc| ≤ r`,
          `0 < ArgHoriz.octX kk (ζ(x + i tc))`.  Along a horizontal piece `h = x - σc` is REAL, so
          the octant projection of the Taylor polynomial is a real polynomial in `h` and only the
          projections `octX (W_k)` enter;
      E.  `abs_sub_le_of_mem_uIcc`, `budget_mono` -- small helpers for the generated certificates.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (AxiomGuardAllZerosKernel_h1000).  No `sorry`.
    conjecture1_proved = False.  Finite interval arithmetic along finitely many segments; nothing
    here bears on the Riemann Hypothesis.
-/



open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace H1000Oct

open ArbEcon ArbEcon.Off

/-! ## A1. The correction factor, with `a ≤ ‖c - 1‖`. -/





/-! ## A2. The Taylor model for any real part of the center. -/



/-! ## B. The remainder along a horizontal segment, and the `G` certificate. -/









/-! ## C. The kernel check of a piece. -/

































/-! ## D. The piece. -/





/-! ## E. Helpers for the generated certificates. -/

/-- A point of `[a, b]` (either order) is within `r` of `σ` when both ends are. -/
theorem abs_sub_le_of_mem_uIcc {x a b σ r : ℝ} (hx : x ∈ Set.uIcc a b) (ha : |a - σ| ≤ r)
    (hb : |b - σ| ≤ r) : |x - σ| ≤ r := by
  rw [abs_le] at ha hb ⊢
  rcases Set.mem_uIcc.mp hx with h | h <;> constructor <;> linarith [h.1, h.2]





/-! ## F. Closed forms for the generated budgets (K ≤ 6), and the slab-cell wrapper. -/











/-! ## G. Generated-certificate adapters. -/







/-- The endpoint point enclosure of an octant certificate from the `k = 0` accumulators of the piece
    centred at the endpoint and ONE `ArbEcon.Off.checkG`. -/
theorem inBox_of_checkG (c : Cfg) (o : OCfg) (σ t : ℝ) (hσ : σ = ((o.a : ℝ) - o.b) / o.q)
    (ht : t = (c.tn : ℝ) / 2 ^ c.tq) (K N : ℕ) (s1 s2 : StO) (h1 : InvO c σ t (N - 1) s1)
    (h2 : InvO c σ t N s2) (hne1 : s1.acc ≠ []) (hne2 : s2.acc ≠ []) (D : ℕ)
    (reLo reHi imLo imHi : ℤ) (Qp Rn Rd : ℕ)
    (hc : checkG c o K N (s1.acc.headD Acc.zero) (s2.acc.headD Acc.zero) D reLo reHi imLo imHi Qp Rn Rd
      = true) :
    ArgHoriz.InBox (riemannZeta ((σ : ℂ) + (t : ℂ) * I)) ((reLo : ℝ) / D) ((reHi : ℝ) / D)
      ((imLo : ℝ) / D) ((imHi : ℝ) / D) := by
  obtain ⟨x1, xs1, hs1⟩ := List.exists_cons_of_ne_nil hne1
  obtain ⟨x2, xs2, hs2⟩ := List.exists_cons_of_ne_nil hne2
  have ha1 := accOK_head c σ t (N - 1) s1 x1 xs1 h1 hs1
  have ha2 := accOK_head c σ t N s2 x2 xs2 h2 hs2
  rw [hs1, hs2] at hc
  have := checkG_sound c o σ t hσ ht K N x1 x2 ha1 ha2 D reLo reHi imLo imHi Qp Rn Rd hc
  exact ⟨this.1.1, this.1.2, this.2.1, this.2.2⟩

end H1000Oct


/-  Arb4_Side.lean -- lane Arb4 (h1000 compaction): Boolean kernel checkers, with soundness proved
    once, for the per-piece side conditions of an octant certificate (brick K6c, `H1000Octant`).

    The generated edge modules `H1000Edge_*` of lane h1000-integrate close, per octant piece, an error
    budget, a horizontal remainder bound, a `G` certificate and six scalar conditions by `norm_num`
    (about 400 KB of olean per piece).  Here all of them are ONE Boolean `pieceOK`, run by
    `decide +kernel` on exact rationals (`Arb4_Q`), together with the off-line evaluator run itself
    (the states after `N - 1` and `N` terms are recomputed in the kernel, not stored):

      * `CpQ betaQ emcBQ corrVarQ budgetQ` (+ `val_*`) -- the error budget of
                           `H1000Oct.piece_octX_pos` as a rational, EQUAL to the real one;
      * `pochQ`, `val_pochQ` -- `pochNormSq` as a rational;
      * `PieceD`         -- the certificate data of one piece (center `(a - b)/q`, radius `rn/rd`,
                           octant `kk`, budget `FN/FD`, and the rationals of the side conditions);
      * `gOK remOK geomOK budgetOK` and their soundness -- the `G` bound, the order-13 remainder on the
                           piece, the scalar geometry, the budget;
      * `pieceOK`, `pieceOK_sound` -- THE PIECE: `pieceOK tn tq N L P = true` gives
                           `0 < octX kk (ζ(x + i t))` for every `x` with `|x - σ| ≤ r`, `t = tn / 2^tq`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  Finite interval
    arithmetic along finitely many segments; nothing here bears on the Riemann Hypothesis.
-/



open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace Arb4

open Q

/-! ## A. The error budget as a rational -/























/-! ## B. `pochNormSq` as a rational -/





/-! ## C. The certificate data of one octant piece -/







namespace PieceD















theorem val_σQ (P : PieceD) (hq : 1 ≤ P.q) : P.σQ.val = P.σ := by
  rw [σQ, val_frac _ hq, σ]
  push_cast
  ring

theorem val_rQ (P : PieceD) (hrd : 1 ≤ P.rd) : P.rQ.val = (P.rn : ℝ) / P.rd := by
  rw [rQ, val_frac _ hrd]
  push_cast
  ring







end PieceD

/-! ## D. The side conditions as Booleans -/













/-! ## E. THE PIECE -/





end Arb4


/-  Arb4_Edge.lean -- lane Arb4 (h1000 compaction): ONE Boolean kernel checker per horizontal edge.

    `ArgHoriz.hAH_of_octCert_boxes` (brick K6c) reduces `argChangeHoriz ζ T 2 (-1) ∈ [Lo, Hi]` to an
    octant certificate (breakpoints `2 = x 0 > … > x m = -1`, labels, no crossing on every piece),
    two endpoint point enclosures with their corner slopes, and two final inequalities with `π` and
    `arctan`.  The generated edge modules `H1000Edge_*` prove these by `norm_num` per piece and per
    edge.  Here the WHOLE edge is one Boolean `edgeOK`, run by ONE `decide +kernel`:

      * `EdgeD`         -- the certificate data of an edge: height `t = tn / 2^tq`, EM cut `N`, log
                           bound `L`, breakpoints `x`, pieces `pc` (`Arb4_Side.PieceD`), endpoint
                           boxes (`ArbEcon.Off.checkG` data), corner slopes, the final `[Lo, Hi]`;
      * `boxOK`, `boxOK_sound` -- an endpoint enclosure (evaluator run at the piece center, recomputed)
                           and its four corner conditions;
      * `atanLoQ atanHiQ piL piH`, `finalLo_sound`, `finalHi_sound` -- the two final inequalities
                           (`3.141592 < π < 3.141593`, `ArgHoriz.atanLo_le`, `ArgHoriz.le_atanHi`);
      * `edgeOK`, `edgeOK_sound` -- THE EDGE: `edgeOK E = true` gives
                           `argChangeHoriz riemannZeta (tn / 2^tq) 2 (-1) ∈ [Lo, Hi]`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  One edge of a finite
    zero count; nothing here bears on the Riemann Hypothesis.
-/


open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace Arb4

open Q

/-! ## A. Small Boolean helpers -/



theorem eqB_sound {a b : Q} (h : eqB a b = true) : a.val = b.val := by
  simp only [eqB, Bool.and_eq_true] at h
  exact le_antisymm (le_sound h.1) (le_sound h.2)



theorem inRad_sound {x : Q} {P : PieceD} (hq : 1 ≤ P.q) (hrd : 1 ≤ P.rd) (h : inRad x P = true) :
    |x.val - P.σ| ≤ (P.rn : ℝ) / P.rd := by
  have h' := le_sound h
  rw [val_qabs, val_sub, P.val_σQ hq, P.val_rQ hrd] at h'
  exact h'

/-! ## B. The evaluator invariants of a piece center -/

theorem runs_inv (tn tq N : ℕ) (P : PieceD) (hN : 2 ≤ N) (hq : 1 ≤ P.q) :
    ArbEcon.Off.InvO (ArbEcon.OrderK.cfg64 tn tq) P.σ ((tn : ℝ) / 2 ^ tq) (N - 1)
        (ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 tn tq) P.oc (N - 2)
          (ArbEcon.Off.StO.init (ArbEcon.OrderK.cfg64 tn tq) 5)) ∧
      ArbEcon.Off.InvO (ArbEcon.OrderK.cfg64 tn tq) P.σ ((tn : ℝ) / 2 ^ tq) N
        (ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 tn tq) P.oc 1
          (ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 tn tq) P.oc (N - 2)
            (ArbEcon.Off.StO.init (ArbEcon.OrderK.cfg64 tn tq) 5))) := by
  set c := ArbEcon.OrderK.cfg64 tn tq with hc
  set t : ℝ := (tn : ℝ) / 2 ^ tq with ht
  have hv : ArbEcon.Valid c t 9 := ArbEcon.OrderK.valid64 tn tq t rfl
  have ho : ArbEcon.Off.OValid c P.oc P.σ := ⟨rfl, hq, rfl⟩
  have i0 := ArbEcon.Off.initO_sound c P.σ t 5 hv.one_eq
  have i1 := ArbEcon.Off.runO_sound c P.oc P.σ t 9 hv ho (N - 2) 1 _ i0
  rw [show 1 + (N - 2) = N - 1 by omega] at i1
  have i2 := ArbEcon.Off.runO_sound c P.oc P.σ t 9 hv ho 1 (N - 1) _ i1
  rw [show N - 1 + 1 = N by omega] at i2
  exact ⟨i1, i2⟩

/-! ## C. Endpoint enclosures and their corner slopes -/



theorem cornerOK_sound {al be : ℤ} {a b qlo qhi : Q} (h : cornerOK al be a b qlo qhi = true) :
    0 < (al : ℝ) * a.val + be * b.val ∧
      qlo.val * ((al : ℝ) * a.val + be * b.val) ≤ (al : ℝ) * b.val - be * a.val ∧
      (al : ℝ) * b.val - be * a.val ≤ qhi.val * ((al : ℝ) * a.val + be * b.val) := by
  simp only [cornerOK, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h1' := lt_sound h1
  have h2' := le_sound h2
  have h3' := le_sound h3
  simp only [val_add, val_mul, val_sub, val_ofInt] at h1' h2' h3'
  push_cast at h1'
  exact ⟨h1', h2', h3'⟩



theorem boxOK_sound (tn tq N : ℕ) (P : PieceD) (D : ℕ) (reLo reHi imLo imHi : ℤ) (Qp Rn Rd : ℕ)
    (qlo qhi : Q) (h : boxOK tn tq N P D reLo reHi imLo imHi Qp Rn Rd qlo qhi = true) :
    ArgHoriz.InBox (riemannZeta ((P.σ : ℂ) + (((tn : ℝ) / 2 ^ tq : ℝ) : ℂ) * I))
        (frac reLo D).val (frac reHi D).val (frac imLo D).val (frac imHi D).val ∧
      ∀ a ∈ ({(frac reLo D).val, (frac reHi D).val} : Set ℝ),
        ∀ b ∈ ({(frac imLo D).val, (frac imHi D).val} : Set ℝ),
        0 < (ArgHoriz.octA P.kk : ℝ) * a + ArgHoriz.octB P.kk * b ∧
          qlo.val * ((ArgHoriz.octA P.kk : ℝ) * a + ArgHoriz.octB P.kk * b)
            ≤ (ArgHoriz.octA P.kk : ℝ) * b - ArgHoriz.octB P.kk * a ∧
          (ArgHoriz.octA P.kk : ℝ) * b - ArgHoriz.octB P.kk * a
            ≤ qhi.val * ((ArgHoriz.octA P.kk : ℝ) * a + ArgHoriz.octB P.kk * b) := by
  simp only [boxOK, Bool.and_eq_true, Nat.ble_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff]
    at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hN, hq⟩, hD⟩, hne1⟩, hne2⟩, hG⟩, c00⟩, c01⟩, c10⟩, c11⟩ := h
  obtain ⟨i1, i2⟩ := runs_inv tn tq N P hN hq
  have hbox := H1000Oct.inBox_of_checkG (ArbEcon.OrderK.cfg64 tn tq) P.oc P.σ ((tn : ℝ) / 2 ^ tq)
    rfl rfl 6 N _ _ i1 i2 hne1 hne2 D reLo reHi imLo imHi Qp Rn Rd hG
  have hv : ∀ z : ℤ, (frac z D).val = (z : ℝ) / (D : ℝ) := fun z => val_frac z hD
  refine ⟨?_, ?_⟩
  · rw [hv, hv, hv, hv]; exact hbox
  · intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact cornerOK_sound c00
    · exact cornerOK_sound c01
    · exact cornerOK_sound c10
    · exact cornerOK_sound c11

/-! ## D. The two final inequalities -/





theorem val_nonneg_iff (q : Q) : 0 ≤ q.val ↔ 0 ≤ q.n := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have : q.val < 0 := by
      have hn' : (q.n : ℝ) < 0 := by exact_mod_cast hn
      exact div_neg_of_neg_of_pos hn' (den_pos q)
    linarith
  · exact val_nonneg

theorem val_atanLoQ (q : Q) : (atanLoQ q).val = ArgHoriz.atanLo q.val := by
  unfold atanLoQ ArgHoriz.atanLo
  by_cases h : 0 ≤ q.n
  · rw [if_pos h, if_pos ((val_nonneg_iff q).mpr h), val_sub, val_div _ (by norm_num [ofNat]),
      val_npow, val_ofNat]
    push_cast; ring
  · rw [if_neg h, if_neg (fun h' => h ((val_nonneg_iff q).mp h'))]

theorem val_atanHiQ (q : Q) : (atanHiQ q).val = ArgHoriz.atanHi q.val := by
  unfold atanHiQ ArgHoriz.atanHi
  by_cases h : 0 ≤ q.n
  · rw [if_pos h, if_pos ((val_nonneg_iff q).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((val_nonneg_iff q).mp h')), val_sub,
      val_div _ (by norm_num [ofNat]), val_npow, val_ofNat]
    push_cast; ring





theorem piL_le (dk : ℤ) : (dk : ℝ) * (piL dk).val ≤ (dk : ℝ) * Real.pi := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  unfold piL
  by_cases h : 0 ≤ dk
  · rw [if_pos h, val_frac _ (by norm_num)]
    have hd : (0 : ℝ) ≤ dk := by exact_mod_cast h
    apply mul_le_mul_of_nonneg_left _ hd
    norm_num at h1 ⊢; linarith
  · rw [if_neg h, val_frac _ (by norm_num)]
    have hd : (dk : ℝ) ≤ 0 := by push Not at h; exact_mod_cast h.le
    apply mul_le_mul_of_nonpos_left _ hd
    norm_num at h2 ⊢; linarith

theorem le_piH (dk : ℤ) : (dk : ℝ) * Real.pi ≤ (dk : ℝ) * (piH dk).val := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  unfold piH
  by_cases h : 0 ≤ dk
  · rw [if_pos h, val_frac _ (by norm_num)]
    have hd : (0 : ℝ) ≤ dk := by exact_mod_cast h
    apply mul_le_mul_of_nonneg_left _ hd
    norm_num at h2 ⊢; linarith
  · rw [if_neg h, val_frac _ (by norm_num)]
    have hd : (dk : ℝ) ≤ 0 := by push Not at h; exact_mod_cast h.le
    apply mul_le_mul_of_nonpos_left _ hd
    norm_num at h1 ⊢; linarith





theorem finalLo_sound {dk : ℤ} {qhi0 qlo1 Lo : Q} (h : finalLoOK dk qhi0 qlo1 Lo = true) :
    Lo.val ≤ (dk : ℝ) * Real.pi / 4 + Real.arctan qlo1.val - Real.arctan qhi0.val := by
  have h' := le_sound h
  rw [val_sub, val_add, val_div _ (by norm_num [ofNat]), val_mul, val_ofInt, val_ofNat,
    val_atanLoQ, val_atanHiQ] at h'
  have a1 := ArgHoriz.atanLo_le qlo1.val
  have a2 := ArgHoriz.le_atanHi qhi0.val
  have p := piL_le dk
  push_cast at h'
  linarith

theorem finalHi_sound {dk : ℤ} {qlo0 qhi1 Hi : Q} (h : finalHiOK dk qlo0 qhi1 Hi = true) :
    (dk : ℝ) * Real.pi / 4 + Real.arctan qhi1.val - Real.arctan qlo0.val ≤ Hi.val := by
  have h' := le_sound h
  rw [val_sub, val_add, val_div _ (by norm_num [ofNat]), val_mul, val_ofInt, val_ofNat,
    val_atanLoQ, val_atanHiQ] at h'
  have a1 := ArgHoriz.le_atanHi qhi1.val
  have a2 := ArgHoriz.atanLo_le qlo0.val
  have p := le_piH dk
  push_cast at h'
  linarith

/-! ## E. THE EDGE -/



namespace EdgeD





end EdgeD





end Arb4


/-  Arb4_Edge.lean -- lane Arb4 (h1000 compaction): ONE Boolean kernel checker per horizontal edge.

    `ArgHoriz.hAH_of_octCert_boxes` (brick K6c) reduces `argChangeHoriz ζ T 2 (-1) ∈ [Lo, Hi]` to an
    octant certificate (breakpoints `2 = x 0 > … > x m = -1`, labels, no crossing on every piece),
    two endpoint point enclosures with their corner slopes, and two final inequalities with `π` and
    `arctan`.  The generated edge modules `H1000Edge_*` prove these by `norm_num` per piece and per
    edge.  Here the WHOLE edge is one Boolean `edgeOK`, run by ONE `decide +kernel`:

      * `EdgeD`         -- the certificate data of an edge: height `t = tn / 2^tq`, EM cut `N`, log
                           bound `L`, breakpoints `x`, pieces `pc` (`Arb4_Side.PieceD`), endpoint
                           boxes (`ArbEcon.Off.checkG` data), corner slopes, the final `[Lo, Hi]`;
      * `boxOK`, `boxOK_sound` -- an endpoint enclosure (evaluator run at the piece center, recomputed)
                           and its four corner conditions;
      * `atanLoQ atanHiQ piL piH`, `finalLo_sound`, `finalHi_sound` -- the two final inequalities
                           (`3.141592 < π < 3.141593`, `ArgHoriz.atanLo_le`, `ArgHoriz.le_atanHi`);
      * `edgeOK`, `edgeOK_sound` -- THE EDGE: `edgeOK E = true` gives
                           `argChangeHoriz riemannZeta (tn / 2^tq) 2 (-1) ∈ [Lo, Hi]`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  One edge of a finite
    zero count; nothing here bears on the Riemann Hypothesis.
-/


open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

section
namespace Arb4
end Arb4
open Arb4

open Q

/-! ## A. Small Boolean helpers -/









/-! ## B. The evaluator invariants of a piece center -/



/-! ## C. Endpoint enclosures and their corner slopes -/









/-! ## D. The two final inequalities -/



























/-! ## E. THE EDGE -/



section
namespace Arb4.EdgeD
end Arb4.EdgeD
open Arb4.EdgeD





end




set_option maxHeartbeats 1000000

theorem solution (E : EdgeD) (h : edgeOK E = true) :
    DiffractionCore.argChangeHoriz riemannZeta E.T 2 (-1) ∈ Set.Icc E.Lo.val E.Hi.val := by
  simp only [edgeOK, Bool.and_eq_true, Nat.ble_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm, htn⟩, hx0⟩, hxm⟩, hpcs⟩, hsteps⟩, hc0⟩, hc1⟩, hb0⟩, hb1⟩, hlo⟩, hhi⟩ := h
  have hT : E.T ≠ 0 := by
    have : (0 : ℝ) < E.tn := by exact_mod_cast htn
    unfold EdgeD.T; positivity
  -- the pieces
  have hpc : ∀ j, j < E.m → pieceOK E.tn E.tq E.N E.L (E.pc j) = true ∧
      inRad (E.x j) (E.pc j) = true ∧ inRad (E.x (j + 1)) (E.pc j) = true := by
    intro j hj
    have := hpcs j hj
    exact ⟨this.1.1, this.1.2, this.2⟩
  -- piece side facts (q ≥ 1, rd ≥ 1) from the piece checker
  have hqr : ∀ j, j < E.m → 1 ≤ (E.pc j).q ∧ 1 ≤ (E.pc j).rd := by
    intro j hj
    have hp := (hpc j hj).1
    simp only [pieceOK, Bool.and_eq_true, Nat.ble_eq] at hp
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hq⟩, hrd⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hp
    exact ⟨hq, hrd⟩
  have hnc : E.cert.NoCross riemannZeta E.T := by
    intro j hj x hx
    obtain ⟨hP, hr0, hr1⟩ := hpc j hj
    obtain ⟨hq, hrd⟩ := hqr j hj
    exact pieceOK_sound E.tn E.tq E.N E.L (E.pc j) hP x
      (H1000Oct.abs_sub_le_of_mem_uIcc hx (inRad_sound hq hrd hr0) (inRad_sound hq hrd hr1))
  have hstep : E.cert.StepOK := by
    intro j hj
    exact hsteps j (by change j + 1 < E.m at hj; omega)
  have hp0 : E.cert.p 0 = 2 := by
    show (E.x 0).val = 2
    rw [eqB_sound hx0, val_ofNat]; norm_num
  have hpm : E.cert.p E.cert.m = -1 := by
    show (E.x E.m).val = -1
    rw [eqB_sound hxm, val_ofInt]; norm_num
  -- the endpoint boxes
  obtain ⟨hw0, hS0⟩ := boxOK_sound E.tn E.tq E.N (E.pc 0) _ _ _ _ _ _ _ _ _ _ hb0
  obtain ⟨hw1, hS1⟩ := boxOK_sound E.tn E.tq E.N (E.pc (E.m - 1)) _ _ _ _ _ _ _ _ _ _ hb1
  have hσ0 : (E.pc 0).σ = 2 := by
    rw [← (E.pc 0).val_σQ (hqr 0 (by omega)).1, eqB_sound hc0, val_ofNat]; norm_num
  have hσ1 : (E.pc (E.m - 1)).σ = -1 := by
    rw [← (E.pc (E.m - 1)).val_σQ (hqr (E.m - 1) (by omega)).1, eqB_sound hc1, val_ofInt]; norm_num
  rw [hσ0] at hw0
  rw [hσ1] at hw1
  have hw0' : ArgHoriz.InBox (riemannZeta (((2 : ℝ) : ℂ) + ((E.T : ℝ) : ℂ) * I))
      (frac E.reLo0 E.D0).val (frac E.reHi0 E.D0).val (frac E.imLo0 E.D0).val (frac E.imHi0 E.D0).val :=
    hw0
  have hw1' : ArgHoriz.InBox (riemannZeta (((-1 : ℝ) : ℂ) + ((E.T : ℝ) : ℂ) * I))
      (frac E.reLo1 E.D1).val (frac E.reHi1 E.D1).val (frac E.imLo1 E.D1).val (frac E.imHi1 E.D1).val :=
    hw1
  have hL := finalLo_sound hlo
  have hH := finalHi_sound hhi
  push_cast at hL hH
  exact ArgHoriz.hAH_of_octCert_boxes (T := E.T) (L := E.Lo.val) (H := E.Hi.val) hT E.cert hm hp0 hpm
    hstep hnc hw0' hS0 hw1' hS1 hL hH
