-- Prove2me | Definitions.Def_QMCLeafB_finalization
-- name    : QMCLeafB_finalization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:11:38.252931+00:00
-- url     : https://prove2.me/theorems/e7cecabe-cc63-4f82-9b94-0b851c7a9214
-- title:
--   QMCLeafB finalization
-- statement:
--   Prove2me QMC campaign — leaf B phase 3 — brick `brick-finalization` (member m4).
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_RoundingOut
import Definitions.Def_QMCLeafB_certpsd
import Definitions.Def_QMCLeafB_Core
/-
Prove2me QMC campaign — leaf B phase 3 — brick `brick-finalization` (member m4).

# Finalisation: the terminal engine state -> a certified `DisplayPair` -> the real sandwich

This file closes the last leg of the leaf-B engine.  Its input is exactly what the GLS
shallow-cut iterate loop (`brick-engine-iterates`) can hand over at termination:

* a rational centre `X` of the last ellipsoid, together with a *PSD margin*
  `∀ x, -(δ * (x ⬝ᵥ x)) ≤ qf X x` — the shallow-cut method only certifies `X ⪰ -δ • 1`, not `X ⪰ 0`;
* the diagonal tolerance `∀ i, |X i i + δ - 1| ≤ ν` of the *promoted* centre;
* a cut histogram: recorded dual candidates `Y t` with weights `w t` (`w ≥ 0`, `∑ w = 1`) and
  per-cut duality budgets `g t` that hold at `X`;
* the engine-side budget coupling `∑ t, w t * g t ≤ V/10000`.

Its output is a `QMCLeafB.RoundingOut.DisplayPair A` — the exact premise triple of
`QMCLeafB.IntegrationProbe.rat_sandwich` — whose primal and dual parts both come with an
**executable** `QMCLeafB.CertPSD.GramCert` whose `Bool`-valued `check` returns `true`, and hence,
via `QMCLeafB.IntegrationProbe.rat_sandwich`, the real value bound
`lowerValue A Xbar ≤ S ≤ lowerValue A Xbar + V/20000`.

## The two genuinely new steps

1. **Free PSD promotion** (`trace_mul_add_diagonal`, `ratPSD_add_diagonal_const`).
   The shallow-cut centre is only `X ⪰ -δ • 1`.  Adding the diagonal `δ • 1` makes it exactly PSD
   (`RatPSD (X + diagonal (fun _ => δ))`), and because a Quantum Max-Cut weight matrix has *zero
   diagonal*, that shift costs **nothing** in the objective:
   `(A * (X + diagonal e)).trace = (A * X).trace`.  This is what makes the terminal centre usable
   by `RoundingOut.roundDiag`, whose hypotheses are about a genuinely PSD point.
2. **Certificate extraction** (`exists_cert_of_ratPSD`).
   `RoundingOut` proves the rounded primal passes the *infinite* rational test; `CertPSD.exists_gram`
   (completeness of the Gram certificate) converts that into a finite certificate, so the
   finalisation output is *checkable by exact rational arithmetic* — the form the runtime needs.

The arithmetic regime is `RoundingOut.budget_closes`: histogram part `≤ V/10000`, rounding part
`≤ 3ν·V` with `ν ≤ 1/30000`, total `≤ V/5000`, which is `rat_sandwich`'s `5000`.

## Main statements

| name | content |
| --- | --- |
| `finalize` | terminal report ⟹ `∃ P : DisplayPair A` with executable `GramCert`s for `P.X` and `diagonal P.y + A` |
| `finalize_psd` / `finalize_split` | `δ = 0` form, and the `ν/2` split bookkeeping the loop naturally keeps |
| `displayPair_sandwich` | a `DisplayPair` is literally `rat_sandwich`'s premise triple |
| `finalize_sandwich` | the above composed: the real bound `lowerValue ≤ S ≤ lowerValue + V/20000` |
| `wMatrixQ`, `wMatrix_castM`, `isQMCWeight_wMatrixQ`, `Vq_wMatrixQ` | the campaign's own weight matrix, over `ℚ` |
| `finalize_sandwich_wMatrix` | the campaign-facing form: at `A = wMatrixQ G`, giving the leaf's slack `∑ e, (G.weights e : ℝ) / 10000` |
| `instance_finalize`, `instance_finalize_sandwich`, `singleEdge_primal_cert` | non-vacuity: the single edge runs end to end, `decide`-checked certificate included |

`IsQMCWeight` is not an abstract class: `wMatrix Q G` (the graph's weights are already rational,
`Weights n = Edge n → ℚ≥0`) satisfies it, and `CastBridge.castM (wMatrixQ G) = QMCLeafB.wMatrix G`
entry by entry, so every statement above is about the leaf statement's own object.

Everything is exact `ℚ`; no analysis, no eigenvalues, no square roots.  No `sorry`, no `axiom`.
-/

open scoped BigOperators
open Matrix

namespace QMCLeafB.Finalization

variable {n : ℕ}

/-! ## 1.  Definitional bridges

`RoundingOut.qf`, `CertPSD.qf` and `CastBridge.qf` all have the body `x ⬝ᵥ (M *ᵥ x)`, so every
statement of one brick is *definitionally* a statement about the object the others consume.  These
two `rfl` lemmas make that bridge explicit so that the composed statements below are about the
literal `rat_sandwich` premises. -/

theorem qf_eq_certPSD (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    RoundingOut.qf M x = CertPSD.qf M x := rfl

theorem qf_eq_castBridge (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    RoundingOut.qf M x = CastBridge.qf M x := rfl

/-! ## 2.  Structural hypotheses on a Quantum Max-Cut weight matrix -/

/-- The rational total weight `V = ∑ᵢ ∑ⱼ Aᵢⱼ` (twice the total edge weight). -/
def Vq (A : Matrix (Fin n) (Fin n) ℚ) : ℚ := ∑ i, ∑ j, A i j

/-- The three structural facts about a Quantum Max-Cut weight matrix that finalisation uses.
`A = wMatrix G` satisfies all three: it is symmetric, its entries are nonnegative edge weights, and
it has no self-loop (`A i i = 0`).

The zero diagonal is *not* cosmetic: it is what makes the PSD promotion of §4 free (§3). -/
structure IsQMCWeight (A : Matrix (Fin n) (Fin n) ℚ) : Prop where
  /-- the weight matrix is symmetric -/
  symm : Aᵀ = A
  /-- edge weights are nonnegative -/
  nonneg : ∀ i j, 0 ≤ A i j
  /-- no self-loops -/
  diag_zero : ∀ i, A i i = 0

/-! ## 3.  A diagonal shift is free in the objective -/

/-- **The zero-diagonal dividend.**  Shifting `X` by an arbitrary diagonal matrix leaves the
objective `tr (A X)` untouched when `A` has no self-loops: the only entries of `A` that see the
diagonal are the diagonal ones. -/
theorem trace_mul_add_diagonal {A X : Matrix (Fin n) (Fin n) ℚ} {e : Fin n → ℚ}
    (hAz : ∀ i, A i i = 0) :
    (A * (X + diagonal e)).trace = (A * X).trace := by
  rw [Matrix.mul_add, Matrix.trace_add, RoundingOut.trace_mul_diagonal]
  simp [hAz]

/-- A diagonal shift preserves symmetry. -/
theorem transpose_add_diagonal {X : Matrix (Fin n) (Fin n) ℚ} {e : Fin n → ℚ}
    (hX : Xᵀ = X) : (X + diagonal e)ᵀ = X + diagonal e := by
  rw [Matrix.transpose_add, diagonal_transpose, hX]

/-- The quadratic form of a constant diagonal matrix. -/
theorem qf_diagonal_const (d : ℚ) (x : Fin n → ℚ) :
    RoundingOut.qf (diagonal (fun _ : Fin n => d)) x = d * (x ⬝ᵥ x) := by
  rw [RoundingOut.qf_diagonal, RoundingOut.dotProduct_self, Finset.mul_sum]

/-- **Free PSD promotion.**  An ellipsoid centre that is only *nearly* PSD — the rational
shallow-cut conclusion `X ⪰ -δ • 1`, written as `-(δ * (x ⬝ᵥ x)) ≤ qf X x` — becomes exactly PSD
after adding `δ • 1`.  Together with §3 this costs nothing in the objective, so the engine never has
to produce an exactly-PSD centre. -/
theorem ratPSD_add_diagonal_const {X : Matrix (Fin n) (Fin n) ℚ} {δ : ℚ}
    (h : ∀ x : Fin n → ℚ, -(δ * (x ⬝ᵥ x)) ≤ RoundingOut.qf X x) :
    RoundingOut.RatPSD (X + diagonal (fun _ : Fin n => δ)) := by
  intro x
  rw [RoundingOut.qf_add, qf_diagonal_const]
  linarith [h x]

/-- The diagonal tolerance of the promoted centre, from the engine's split bookkeeping:
`|X i i - 1| ≤ ν/2` plus `δ ≤ ν/2` gives `|X i i + δ - 1| ≤ ν`. -/
theorem abs_diag_add_le {d δ ν : ℚ} (h1 : |d - 1| ≤ ν / 2) (h2 : δ ≤ ν / 2) (h3 : 0 ≤ δ) :
    |d + δ - 1| ≤ ν := by
  have h2' : |δ| ≤ ν / 2 := by rw [abs_of_nonneg h3]; exact h2
  calc |d + δ - 1| = |(d - 1) + δ| := by rw [show d + δ - 1 = (d - 1) + δ by ring]
    _ ≤ |d - 1| + |δ| := abs_add_le _ _
    _ ≤ ν / 2 + ν / 2 := add_le_add h1 h2'
    _ = ν := by ring

/-! ## 4.  From the infinite rational test to an executable certificate -/

/-- **Certificate extraction.**  A symmetric rational matrix whose quadratic form is nonnegative on
every rational vector has a `GramCert` whose executable `check` returns `true` — this is
`CertPSD.exists_gram` (completeness) read through `CertPSD.GramCert.check_spec`.  It is the step
that makes the finalisation output *verifiable by exact rational arithmetic*. -/
theorem exists_cert_of_ratPSD {X : Matrix (Fin n) (Fin n) ℚ} (hX : Xᵀ = X)
    (hp : RoundingOut.RatPSD X) :
    ∃ (m : ℕ) (C : CertPSD.GramCert n m), C.check X = true := by
  have hp' : ∀ x : Fin n → ℚ, 0 ≤ CertPSD.qf X x := fun x => by
    rw [← qf_eq_certPSD]; exact hp x
  obtain ⟨m, C, hmat, hc⟩ := CertPSD.exists_gram n X hX hp'
  exact ⟨m, C, (CertPSD.GramCert.check_spec C X).mpr ⟨hmat, hc⟩⟩

/-! ## 5.  The engine-side histogram budget coupling -/

/-- **Per-cut budgets average, they do not add.**  If every recorded cut's budget is at most `B`,
then so is the histogram average, because the weights form a convex combination.  Taking
`B = V/10000` gives the `hhist` slot of §6 — the engine only has to certify the bound *per cut*. -/
theorem histogram_budget_le {T : ℕ} {w g : Fin T → ℚ} {B : ℚ}
    (hw0 : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t = 1) (hg : ∀ t, g t ≤ B) :
    (∑ t, w t * g t) ≤ B := by
  have h1 : (∑ t, w t * g t) ≤ ∑ t, w t * B :=
    Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hg t) (hw0 t)
  have h2 : (∑ t, w t * B) = B := by rw [← Finset.sum_mul, hw1, one_mul]
  linarith

/-! ## 6.  Finalisation -/

/-- **Finalisation.**  From the terminal report of the iterate loop — centre `X` with PSD margin
`δ` and diagonal tolerance, cut histogram `(w, Y, g)` with per-cut budgets at `X`, and the histogram
coupling `∑ w g ≤ V/10000` — and with the arithmetic regime `ν ≤ 1/30000`, the engine produces a
display pair whose primal and dual parts are *both* certified by an executable `GramCert`.

The `∀ x, -(δ * (x ⬝ᵥ x)) ≤ qf X x` hypothesis is the only place the shallow-cut depth analysis
enters: it says the last ellipsoid centre is PSD up to `δ`. -/
theorem finalize
    (A X : Matrix (Fin n) (Fin n) ℚ) {T : ℕ}
    (w : Fin T → ℚ) (Y : Fin T → Fin n → ℚ) (g : Fin T → ℚ) {ν δ : ℚ}
    (hQ : IsQMCWeight A)
    (hXsym : Xᵀ = X)
    (hmargin : ∀ x : Fin n → ℚ, -(δ * (x ⬝ᵥ x)) ≤ RoundingOut.qf X x)
    (hXdiag : ∀ i, |X i i + δ - 1| ≤ ν)
    (hν0 : 0 ≤ ν) (hν : ν ≤ 1 / 30000)
    (hw0 : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t = 1)
    (hytest : ∀ t x, 0 ≤ RoundingOut.qf (diagonal (Y t) + A) x)
    (hbudget : ∀ t, (∑ i, Y t i) + (A * X).trace ≤ g t)
    (hhist : (∑ t, w t * g t) ≤ Vq A / 10000) :
    ∃ P : RoundingOut.DisplayPair A,
      (∃ (m : ℕ) (C : CertPSD.GramCert n m), C.check P.X = true) ∧
      (∃ (m : ℕ) (C : CertPSD.GramCert n m), C.check (diagonal P.y + A) = true) := by
  obtain ⟨hAsym, hAnonneg, hAz⟩ := hQ.symm, hQ.nonneg, hQ.diag_zero
  -- the promoted centre: exactly PSD, same objective, diagonal within `ν`
  set X' : Matrix (Fin n) (Fin n) ℚ := X + diagonal (fun _ : Fin n => δ) with hX'
  have hX'sym : X'ᵀ = X' := by rw [hX']; exact transpose_add_diagonal hXsym
  have hX'p : RoundingOut.RatPSD X' := by
    rw [hX']; exact ratPSD_add_diagonal_const hmargin
  have hX'diag : ∀ i, |X' i i - 1| ≤ ν := by
    intro i
    have hii : X' i i = X i i + δ := by
      rw [hX', Matrix.add_apply, Matrix.diagonal_apply_eq]
    rw [hii]; exact hXdiag i
  have hbudget' : ∀ t, (∑ i, Y t i) + (A * X').trace ≤ g t := by
    intro t
    rw [hX', trace_mul_add_diagonal hAz]
    exact hbudget t
  -- the arithmetic regime closes the total budget under `V/5000`
  have hV : (∑ t, w t * g t) + RoundingOut.roundCost A ν ≤ Vq A / 5000 :=
    RoundingOut.budget_closes hAnonneg hAz hν0 hν hhist
  obtain ⟨Xbar, ybar, hsym, hp, hdiagb, hysym, hytestb, hgap⟩ :=
    RoundingOut.rounding_out hν0 hAsym hX'sym hX'p hX'diag hw0 hw1 hytest hbudget'
  have hgap' : (∑ i, ybar i) + (A * Xbar).trace ≤ Vq A / 5000 := le_trans hgap hV
  exact ⟨⟨Xbar, ybar, hsym, hp, hdiagb, hysym, hytestb, hgap'⟩,
    exists_cert_of_ratPSD hsym hp, exists_cert_of_ratPSD hysym hytestb⟩

/-- **Finalisation from an exactly-PSD centre** (`δ = 0`), the shape the engine produces when the
iterate loop keeps its centre inside the PSD cone rather than only in a shallow-cut enclosure. -/
theorem finalize_psd
    (A X : Matrix (Fin n) (Fin n) ℚ) {T : ℕ}
    (w : Fin T → ℚ) (Y : Fin T → Fin n → ℚ) (g : Fin T → ℚ) {ν : ℚ}
    (hQ : IsQMCWeight A)
    (hXsym : Xᵀ = X) (hXp : RoundingOut.RatPSD X)
    (hXdiag : ∀ i, |X i i - 1| ≤ ν)
    (hν0 : 0 ≤ ν) (hν : ν ≤ 1 / 30000)
    (hw0 : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t = 1)
    (hytest : ∀ t x, 0 ≤ RoundingOut.qf (diagonal (Y t) + A) x)
    (hbudget : ∀ t, (∑ i, Y t i) + (A * X).trace ≤ g t)
    (hhist : (∑ t, w t * g t) ≤ Vq A / 10000) :
    ∃ P : RoundingOut.DisplayPair A,
      (∃ (m : ℕ) (C : CertPSD.GramCert n m), C.check P.X = true) ∧
      (∃ (m : ℕ) (C : CertPSD.GramCert n m), C.check (diagonal P.y + A) = true) := by
  refine finalize A X w Y g (ν := ν) (δ := 0) hQ hXsym ?_ ?_ hν0 hν hw0 hw1 hytest
    hbudget hhist
  · intro x; simpa using hXp x
  · intro i; simpa using hXdiag i

/-- **Finalisation with split diagonal bookkeeping.**  The `ν/2` form the iterate loop naturally
maintains: the centre is `ν/2`-close to unit diagonal and the PSD margin is at most `ν/2`, so the
promoted centre is `ν`-close.  This is `finalize` plus `abs_diag_add_le`. -/
theorem finalize_split
    (A X : Matrix (Fin n) (Fin n) ℚ) {T : ℕ}
    (w : Fin T → ℚ) (Y : Fin T → Fin n → ℚ) (g : Fin T → ℚ) {ν δ : ℚ}
    (hQ : IsQMCWeight A)
    (hXsym : Xᵀ = X)
    (hmargin : ∀ x : Fin n → ℚ, -(δ * (x ⬝ᵥ x)) ≤ RoundingOut.qf X x)
    (hδ0 : 0 ≤ δ) (hδν : δ ≤ ν / 2)
    (hXdiag : ∀ i, |X i i - 1| ≤ ν / 2)
    (hν0 : 0 ≤ ν) (hν : ν ≤ 1 / 30000)
    (hw0 : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t = 1)
    (hytest : ∀ t x, 0 ≤ RoundingOut.qf (diagonal (Y t) + A) x)
    (hbudget : ∀ t, (∑ i, Y t i) + (A * X).trace ≤ g t)
    (hhist : (∑ t, w t * g t) ≤ Vq A / 10000) :
    ∃ P : RoundingOut.DisplayPair A,
      (∃ (m : ℕ) (C : CertPSD.GramCert n m), C.check P.X = true) ∧
      (∃ (m : ℕ) (C : CertPSD.GramCert n m), C.check (diagonal P.y + A) = true) :=
  finalize A X w Y g hQ hXsym hmargin
    (fun i => abs_diag_add_le (hXdiag i) hδν hδ0) hν0 hν hw0 hw1 hytest hbudget hhist

/-! ## 7.  The value bound: `rat_sandwich` on the finalised pair -/

/-- **The display pair is a `rat_sandwich` input.**  A `DisplayPair A` produced by finalisation
satisfies, verbatim, the six hypotheses of `QMCLeafB.IntegrationProbe.rat_sandwich`; the only work
is transporting the quadratic form across the two definitionally equal `qf`s.  The conclusion is
the leaf-B real sandwich for the primal point `P.X`. -/
theorem displayPair_sandwich {A : Matrix (Fin n) (Fin n) ℚ} (P : RoundingOut.DisplayPair A)
    (S : ℝ)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue (CastBridge.castM A) S) :
    QMCLeafB.lowerValue (CastBridge.castM A) (CastBridge.castM P.X) ≤ S ∧
      S - QMCLeafB.lowerValue (CastBridge.castM A) (CastBridge.castM P.X)
        ≤ QMCLeafB.V (CastBridge.castM A) / 20000 := by
  refine IntegrationProbe.rat_sandwich A P.X P.y S P.Xsym ?_ P.Xdiag P.ysym ?_ P.gap hS
  · intro x; rw [← qf_eq_castBridge]; exact P.Xtest x
  · intro x; rw [← qf_eq_castBridge]; exact P.ytest x

/-- **The whole leaf-B finish for one graph.**  Finalisation produces a display pair together with
its certified primal, and that pair carries the real value bound
`lowerValue ≤ S ≤ lowerValue + V/20000` for the Quantum Max-Cut SDP value `S` of `castM A`.  The
only inputs are the engine's terminal report and the structural facts about the weight matrix. -/
theorem finalize_sandwich
    (A X : Matrix (Fin n) (Fin n) ℚ) {T : ℕ}
    (w : Fin T → ℚ) (Y : Fin T → Fin n → ℚ) (g : Fin T → ℚ) {ν δ : ℚ}
    (hQ : IsQMCWeight A)
    (hXsym : Xᵀ = X)
    (hmargin : ∀ x : Fin n → ℚ, -(δ * (x ⬝ᵥ x)) ≤ RoundingOut.qf X x)
    (hXdiag : ∀ i, |X i i + δ - 1| ≤ ν)
    (hν0 : 0 ≤ ν) (hν : ν ≤ 1 / 30000)
    (hw0 : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t = 1)
    (hytest : ∀ t x, 0 ≤ RoundingOut.qf (diagonal (Y t) + A) x)
    (hbudget : ∀ t, (∑ i, Y t i) + (A * X).trace ≤ g t)
    (hhist : (∑ t, w t * g t) ≤ Vq A / 10000)
    (S : ℝ) (hS : ModernConvex.Relaxations.IsMaxcutSDPValue (CastBridge.castM A) S) :
    ∃ P : RoundingOut.DisplayPair A,
      (∃ (m : ℕ) (C : CertPSD.GramCert n m), C.check P.X = true) ∧
      QMCLeafB.lowerValue (CastBridge.castM A) (CastBridge.castM P.X) ≤ S ∧
      S - QMCLeafB.lowerValue (CastBridge.castM A) (CastBridge.castM P.X)
        ≤ QMCLeafB.V (CastBridge.castM A) / 20000 := by
  obtain ⟨P, hcert⟩ :=
    finalize A X w Y g hQ hXsym hmargin hXdiag hν0 hν hw0 hw1 hytest hbudget hhist
  exact ⟨P, hcert.1, (displayPair_sandwich P S hS).1, (displayPair_sandwich P S hS).2⟩

/-! ## 8.  Instantiation at the campaign's own weight matrix

`IsQMCWeight` is not an abstract hypothesis class: the graph weights of `Input` are already
rational (`Weights n = Edge n → ℚ≥0`), so the campaign's weight matrix has an exact `ℚ` version
`wMatrixQ G` whose cast is `QMCLeafB.wMatrix G` verbatim.  Hence §6/§7 apply with `A = wMatrixQ G`
and produce the leaf's own slack `∑ e, (G.weights e : ℝ) / 10000`. -/

section WeightMatrix

open QuantumMaxCutEnergy

/-- The rational weight matrix of a Quantum Max-Cut input: the exact `ℚ` counterpart of
`QMCLeafB.wMatrix` (same pattern, upper triangle first). -/
noncomputable def wMatrixQ (G : Input) : Matrix (Fin G.n) (Fin G.n) ℚ :=
  Matrix.of fun i j : Fin G.n =>
    if h : i < j then ((G.weights ⟨(i, j), h⟩ : ℚ≥0) : ℚ)
    else if h : j < i then ((G.weights ⟨(j, i), h⟩ : ℚ≥0) : ℚ) else 0

@[simp] theorem wMatrixQ_apply (G : Input) (i j : Fin G.n) :
    wMatrixQ G i j = (if h : i < j then ((G.weights ⟨(i, j), h⟩ : ℚ≥0) : ℚ)
      else if h : j < i then ((G.weights ⟨(j, i), h⟩ : ℚ≥0) : ℚ) else 0) := rfl

theorem wMatrixQ_apply_of_lt {G : Input} {i j : Fin G.n} (h : i < j) :
    wMatrixQ G i j = ((G.weights ⟨(i, j), h⟩ : ℚ≥0) : ℚ) := by
  rw [wMatrixQ_apply, dif_pos h]

theorem wMatrixQ_apply_of_gt {G : Input} {i j : Fin G.n} (h : j < i) :
    wMatrixQ G i j = ((G.weights ⟨(j, i), h⟩ : ℚ≥0) : ℚ) := by
  rw [wMatrixQ_apply, dif_neg (not_lt.mpr h.le), dif_pos h]

theorem wMatrixQ_apply_of_eq {G : Input} {i : Fin G.n} : wMatrixQ G i i = 0 := by
  rw [wMatrixQ_apply, dif_neg (lt_irrefl i), dif_neg (lt_irrefl i)]

/-- **The cast bridge**: the rational weight matrix casts to the leaf statement's weight matrix,
entry by entry. -/
theorem wMatrix_castM (G : Input) : CastBridge.castM (wMatrixQ G) = QMCLeafB.wMatrix G := by
  ext i j
  rw [CastBridge.castM_apply]
  unfold wMatrixQ QMCLeafB.wMatrix
  simp only [Matrix.of_apply]
  split_ifs <;> push_cast <;> rfl

/-- The rational weight matrix is a Quantum Max-Cut weight matrix: symmetric, entrywise
nonnegative, zero diagonal. -/
theorem isQMCWeight_wMatrixQ (G : Input) : IsQMCWeight (wMatrixQ G) where
  symm := by
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · rw [Matrix.transpose_apply, wMatrixQ_apply_of_gt h, wMatrixQ_apply_of_lt h]
    · subst h; simp only [Matrix.transpose_apply, wMatrixQ_apply_of_eq]
    · rw [Matrix.transpose_apply, wMatrixQ_apply_of_lt h, wMatrixQ_apply_of_gt h]
  nonneg := by
    intro i j
    rw [wMatrixQ_apply]
    split_ifs <;> positivity
  diag_zero := fun _ => wMatrixQ_apply_of_eq

/-- The rational total weight of the weight matrix is twice the total edge weight, over `ℚ`
(the `ℚ` counterpart of `QMCLeafB.V_wMatrix`). -/
theorem Vq_wMatrixQ (G : Input) :
    Vq (wMatrixQ G) = 2 * ∑ e : Edge G.n, ((G.weights e : ℚ≥0) : ℚ) := by
  have h1 : ((Vq (wMatrixQ G) : ℚ) : ℝ) = 2 * ∑ e : Edge G.n, (G.weights e : ℝ) := by
    rw [Vq, ← IntegrationProbe.V_castM (wMatrixQ G), wMatrix_castM, QMCLeafB.V_wMatrix]
  have h2 : ((2 * ∑ e : Edge G.n, ((G.weights e : ℚ≥0) : ℚ) : ℚ) : ℝ)
      = 2 * ∑ e : Edge G.n, (G.weights e : ℝ) := by
    push_cast
    rfl
  exact Rat.cast_injective (h1.trans h2.symm)

/-- **The leaf's value bound from the graph's own weights.**  Finalisation at `A = wMatrixQ G`
gives, for every `S` that is the Quantum Max-Cut SDP value of `wMatrix G`, a display pair whose
primal is certified by an executable `GramCert` and whose real value bound carries the leaf's own
slack `∑ e, (G.weights e : ℝ) / 10000` — i.e. exactly `V/20000` after `V = 2 ∑ e`. -/
theorem finalize_sandwich_wMatrix (G : Input) {T : ℕ}
    (X : Matrix (Fin G.n) (Fin G.n) ℚ) (w : Fin T → ℚ)
    (Y : Fin T → Fin G.n → ℚ) (g : Fin T → ℚ) {ν δ : ℚ}
    (hXsym : Xᵀ = X)
    (hmargin : ∀ x : Fin G.n → ℚ, -(δ * (x ⬝ᵥ x)) ≤ RoundingOut.qf X x)
    (hXdiag : ∀ i, |X i i + δ - 1| ≤ ν)
    (hν0 : 0 ≤ ν) (hν : ν ≤ 1 / 30000)
    (hw0 : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t = 1)
    (hytest : ∀ t x, 0 ≤ RoundingOut.qf (diagonal (Y t) + wMatrixQ G) x)
    (hbudget : ∀ t, (∑ i, Y t i) + (wMatrixQ G * X).trace ≤ g t)
    (hhist : (∑ t, w t * g t) ≤ Vq (wMatrixQ G) / 10000)
    (S : ℝ) (hS : ModernConvex.Relaxations.IsMaxcutSDPValue (QMCLeafB.wMatrix G) S) :
    ∃ P : RoundingOut.DisplayPair (wMatrixQ G),
      (∃ (m : ℕ) (C : CertPSD.GramCert G.n m), C.check P.X = true) ∧
      QMCLeafB.lowerValue (QMCLeafB.wMatrix G) (CastBridge.castM P.X) ≤ S ∧
      S - QMCLeafB.lowerValue (QMCLeafB.wMatrix G) (CastBridge.castM P.X)
        ≤ (∑ e : Edge G.n, (G.weights e : ℝ)) / 10000 := by
  obtain ⟨P, hc, h1, h2⟩ :=
    finalize_sandwich (wMatrixQ G) X w Y g (isQMCWeight_wMatrixQ G) hXsym hmargin hXdiag hν0 hν
      hw0 hw1 hytest hbudget hhist S (by rw [wMatrix_castM]; exact hS)
  refine ⟨P, hc, ?_, ?_⟩
  · simpa only [wMatrix_castM] using h1
  · have hV : QMCLeafB.V (QMCLeafB.wMatrix G) / 20000
        = (∑ e : Edge G.n, (G.weights e : ℝ)) / 10000 := by
      rw [QMCLeafB.V_wMatrix]; ring
    simpa only [wMatrix_castM, hV] using h2

end WeightMatrix

/-! ## 9.  Non-vacuity

The single edge: `A = [[0,1],[1,0]]`, `V = 2`, optimal rank-one primal `X = [[1,-1],[-1,1]]`,
dual `y = (1,1)`, one-cut histogram with budget `0`.  This runs the *whole* pipeline of §6
through the kernel. -/

/-- An explicit `GramCert` for the rank-one primal `[[1,-1],[-1,1]] = u uᵀ`, `u = (1,-1)`;
`check` is decided by kernel computation, so the executable side of the certificate is exercised. -/
theorem singleEdge_primal_cert :
    (⟨fun i _ => if i = (0 : Fin 2) then (1 : ℚ) else -1, fun _ => (1 : ℚ)⟩ :
        CertPSD.GramCert 2 1).check (!![(1 : ℚ), -1; -1, 1]) = true := by
  rw [CertPSD.GramCert.check_spec]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CertPSD.GramCert.mat_apply]
  · intro k; norm_num

/-- **The engine's hypotheses are simultaneously satisfiable**: `finalize` fires on the single
edge and returns a display pair whose primal carries a passing executable certificate and whose dual
slack carries a passing executable certificate. -/
theorem instance_finalize :
    ∃ P : RoundingOut.DisplayPair (!![(0 : ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ),
      (∃ (m : ℕ) (C : CertPSD.GramCert 2 m), C.check P.X = true) ∧
      (∃ (m : ℕ) (C : CertPSD.GramCert 2 m), C.check (diagonal P.y
        + (!![(0 : ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ)) = true) := by
  have hA : IsQMCWeight (!![(0 : ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) := by
    refine ⟨?_, ?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp
    · intro i j; fin_cases i <;> fin_cases j <;> norm_num
    · intro i; fin_cases i <;> simp
  have hXsym : (!![(1 : ℚ), -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ)ᵀ
      = !![(1 : ℚ), -1; -1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hXp : RoundingOut.RatPSD (!![(1 : ℚ), -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ) := by
    have h : (!![(1 : ℚ), -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ)
        = vecMulVec ![1, -1] ![1, -1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [vecMulVec]
    rw [h]; exact RoundingOut.ratPSD_vecMulVec ![1, -1]
  have hdiag : ∀ i, |(!![(1 : ℚ), -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ) i i - 1| ≤ 0 := by
    intro i; fin_cases i <;> simp
  have hSlack : (diagonal (![1, 1] : Fin 2 → ℚ)
      + (!![(0 : ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ))
      = vecMulVec ![1, 1] ![1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [vecMulVec, diagonal]
  have hytest : ∀ t : Fin 1, ∀ x : Fin 2 → ℚ,
      0 ≤ RoundingOut.qf (diagonal (![1, 1] : Fin 2 → ℚ)
        + (!![(0 : ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ)) x := by
    intro t x
    rw [show RoundingOut.qf (diagonal (![1, 1] : Fin 2 → ℚ)
        + (!![(0 : ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ)) x
        = RoundingOut.qf (vecMulVec ![1, 1] ![1, 1]) x by rw [hSlack]]
    exact RoundingOut.ratPSD_vecMulVec (![1, 1] : Fin 2 → ℚ) x
  have hbudget : ∀ t : Fin 1, (∑ i, (![1, 1] : Fin 2 → ℚ) i)
      + ((!![(0 : ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ)
        * !![(1 : ℚ), -1; -1, 1]).trace ≤ 0 := by
    intro t
    have h1 : (∑ i, (![1, 1] : Fin 2 → ℚ) i) = 2 := by norm_num [Fin.sum_univ_two]
    have h2 : ((!![(0 : ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ)
        * !![(1 : ℚ), -1; -1, 1]).trace = -2 := by
      simp [Matrix.trace, Fin.sum_univ_two]
      norm_num
    rw [h1, h2]; norm_num
  have hhist : (∑ t : Fin 1, (fun _ : Fin 1 => (1 : ℚ)) t * (fun _ : Fin 1 => (0 : ℚ)) t)
      ≤ Vq (!![(0 : ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) / 10000 := by
    have hV : Vq (!![(0 : ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) = 2 := by
      norm_num [Vq, Fin.sum_univ_two]
    rw [hV]
    norm_num [Fin.sum_univ_one]
  exact finalize_psd (A := !![(0 : ℚ), 1; 1, 0]) (X := !![(1 : ℚ), -1; -1, 1])
    (T := 1) (w := fun _ => 1) (Y := fun _ => ![1, 1]) (g := fun _ => 0) (ν := 0)
    hA hXsym hXp hdiag (le_refl 0) (by norm_num) (fun _ => zero_le_one) (by simp) hytest
    hbudget hhist

/-- **And the sandwich fires on the single edge.**  Any `S` that is the Quantum Max-Cut SDP value of
the single-edge weight matrix lies between `lowerValue` at the finalised primal and
`lowerValue + V/20000`.  Stated for an abstract `S` so that no instantiation of the SDP-value
predicate is needed; that is the assembly brick's job. -/
theorem instance_finalize_sandwich (S : ℝ)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue
      (CastBridge.castM (!![(0 : ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ)) S) :
    ∃ P : RoundingOut.DisplayPair (!![(0 : ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ),
      (∃ (m : ℕ) (C : CertPSD.GramCert 2 m), C.check P.X = true) ∧
      QMCLeafB.lowerValue (CastBridge.castM (!![(0 : ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ))
        (CastBridge.castM P.X) ≤ S ∧
      S - QMCLeafB.lowerValue
          (CastBridge.castM (!![(0 : ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ))
          (CastBridge.castM P.X)
        ≤ QMCLeafB.V (CastBridge.castM (!![(0 : ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ))
          / 20000 := by
  obtain ⟨P, hcert⟩ := instance_finalize
  exact ⟨P, hcert.1, (displayPair_sandwich P S hS).1, (displayPair_sandwich P S hS).2⟩

end QMCLeafB.Finalization

#print axioms QMCLeafB.Finalization.qf_eq_castBridge
#print axioms QMCLeafB.Finalization.trace_mul_add_diagonal
#print axioms QMCLeafB.Finalization.ratPSD_add_diagonal_const
#print axioms QMCLeafB.Finalization.abs_diag_add_le
#print axioms QMCLeafB.Finalization.exists_cert_of_ratPSD
#print axioms QMCLeafB.Finalization.histogram_budget_le
#print axioms QMCLeafB.Finalization.finalize
#print axioms QMCLeafB.Finalization.finalize_psd
#print axioms QMCLeafB.Finalization.finalize_split
#print axioms QMCLeafB.Finalization.displayPair_sandwich
#print axioms QMCLeafB.Finalization.finalize_sandwich
#print axioms QMCLeafB.Finalization.wMatrix_castM
#print axioms QMCLeafB.Finalization.isQMCWeight_wMatrixQ
#print axioms QMCLeafB.Finalization.Vq_wMatrixQ
#print axioms QMCLeafB.Finalization.finalize_sandwich_wMatrix
#print axioms QMCLeafB.Finalization.singleEdge_primal_cert
#print axioms QMCLeafB.Finalization.instance_finalize
#print axioms QMCLeafB.Finalization.instance_finalize_sandwich


