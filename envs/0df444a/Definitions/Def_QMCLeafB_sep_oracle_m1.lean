-- Prove2me | Definitions.Def_QMCLeafB_sep_oracle_m1
-- name    : QMCLeafB_sep_oracle_m1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:21:57.547733+00:00
-- url     : https://prove2.me/theorems/9496ffd6-3ef0-45c4-bdf3-68a86cefd85b
-- title:
--   QMCLeafB sep_oracle_m1
-- statement:
--   # brick-sep-oracle — the PolyProgram separation oracle (leaf B, phase 3)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
/-
# brick-sep-oracle — the PolyProgram separation oracle (leaf B, phase 3)

The GLS shallow-cut engine needs one non-negotiable ingredient: at every rational centre `cX`
and every rational threshold `t`, an exactly computable *verdict* that is either

  * `ok`  — the centre is a feasible threshold point, with an explicit **margin ledger**; or
  * `cut` — a rational normal `N` and a rational margin `d > 0` such that the halfspace
            `{X | -d <= N(X - cX)}` contains the whole threshold body.

This file builds that oracle, proves it **total**, and makes it a **computation** (exact rational
arithmetic only: no square root, no eigenvalue, no limit, no classical choice in the returned
data).  The cut side is proved over an arbitrary linear ordered field `K`, so the same theorem is
available at `K = QQ` (the engine's arithmetic) and at `K = RR` (the geometry of
`EllipsoidStep.stepMatrix`); the real instances are recorded in section 4.

## What is here

* 0  the quadratic form `qf M x = x^T M x` and the Frobenius pairing `[C, X] = sum_i sum_j C_ij X_ij`,
  with `qf_eq_frob : qf X v = [v v^T, X]` (a violated quadratic form *is* a violated halfspace) and
  `frob_eq_trace : [A, X] = tr (A X)` on symmetric `X` (the brief's `tr (A cX)`).
* 1  `PSD`, `unitDiag`, and the threshold body `Body A t`.
* 2  the three cut families with **exact** margins and their validity over any linear ordered
  field, plus **totality**: `ok_or_cut : Ok A t cX or Nonempty (GoodCut A t cX)`, bundled as
  `Response` (`ok`/`cut`) with `response_total` and `oracle`.

      psd branch        normal `v v^T`,   margin `mu = -qf cX v`     (`psdCut_separates`)
      diag branch       normal `+-e_i e_i^T`, margin `|cX_ii - 1|`   (`diagCut_up/down_separates`)
      threshold branch  normal `A`,       margin `t - [A, cX]`       (`traceCut_separates`)

* 3  `OkReport A t cX`: the `ok` branch's margin ledger (`d > 0`, `-d/2 * sum x^2 <= qf cX x`,
  `|cX_ii - 1| <= d/4`, `t - d/2 <= [A, cX]`), produced from a passing `GramCert`
  (`okReport_of_cert`) or from a certificate for an entrywise `eps`-close matrix
  (`okReport_of_shifted_cert`, exchange rate `d = 2 eps n`), i.e. exactly the
  `CertPSD.premise_of_check_shifted` margin shape.
* 4  the real instances: `qf`/`frob` commute with `Rat.castHom RR` (`qf_map`, `frob_map`) and the
  three branches hold for the *real* threshold body with the same rational margins.
* 5  the companion report: which quantity of each branch is `EllipsoidStep`'s `c` and which is its
  `d`, the two side conditions `EllipsoidStep.containment` asks (`c != 0`, `0 <= d`) with the branch
  proofs, the scale invariance of the relative depth, and the off-diagonal coordinate reduction for
  the unit-diagonal slice.
* 5.5 **the computable PSD split**: `split : (n) -> (X) -> (forall i j, X i j = X j i) -> Split n X`,
  an exact rational LDL^T pivot recursion returning *either* a checked `GramCert` *or* an explicit
  violated rational vector.  `split_trichotomy` is the resulting computable dichotomy (the
  constructive counterpart of `CertPSD.premise_iff_exists_cert`'s completeness direction).
* 5.6 the **summed diagonal cut** (`[diagonal (diagSign cX), X - cX] = sum_i |cX_ii - 1|` exactly,
  the computable replacement for "find an index `i`") and `sepOracle : Response A t cX`, a `def`
  whose every branch is decided by rational comparisons and the pivot split.  `#eval` at the end of
  the file shows it running (verdicts and witness vectors) on four test matrices, including the
  zero-pivot case.

`sepOracle_toReport` / `Response.toReport` hand the verdict to the consumer in the shape it needs:
either `OkReport` (the finalization's ledger) or a `GoodCut` (normal + exact positive margin, ready
to be `EllipsoidStep`'s `(c, d)`).

Self-contained (`import Mathlib`), sorry-free, standard three axioms (section 6).
-/


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open scoped BigOperators
open Matrix

namespace QMCLeafB.SepOracle

section Generic

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n : ℕ}

/-! ## 0.  The rational quadratic form and the Frobenius pairing -/

/-- `qf M x = xᵀ M x`.  The body is verbatim `CertPSD.qf` / `CastBridge.qf`, so every statement
below is definitionally a statement about the object `rat_sandwich` consumes. -/
def qf (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K) : K := x ⬝ᵥ (M *ᵥ x)

theorem qf_eq_sum (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    qf M x = ∑ i, ∑ j, x i * (M i j * x j) := by
  simp only [qf, dotProduct, mulVec, Finset.mul_sum]

theorem qf_add (M N : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    qf (M + N) x = qf M x + qf N x := by
  simp only [qf, add_mulVec, dotProduct_add]

theorem qf_sub (M N : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    qf (M - N) x = qf M x - qf N x := by
  simp only [qf, sub_mulVec, dotProduct_sub]

theorem qf_zero (M : Matrix (Fin n) (Fin n) K) : qf M (0 : Fin n → K) = 0 := by
  simp [qf]

/-- The Frobenius pairing `⟪C, X⟫ = ∑ᵢ ∑ⱼ Cᵢⱼ Xᵢⱼ`.  This is the coordinate functional of the
engine: `t ≤ ⟪A, X⟫` is the objective test and every cut normal is an element of this dual. -/
def frob (C X : Matrix (Fin n) (Fin n) K) : K := ∑ i, ∑ j, C i j * X i j

theorem frob_add (C X Y : Matrix (Fin n) (Fin n) K) :
    frob C (X + Y) = frob C X + frob C Y := by
  simp only [frob, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem frob_sub (C X Y : Matrix (Fin n) (Fin n) K) :
    frob C (X - Y) = frob C X - frob C Y := by
  simp only [frob, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem frob_neg (C X : Matrix (Fin n) (Fin n) K) : frob C (-X) = -frob C X := by
  simp only [frob, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem frob_neg_left (C X : Matrix (Fin n) (Fin n) K) : frob (-C) X = -frob C X := by
  simp only [frob, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-- **The rank-one identification**: `qf X v = ⟪v vᵀ, X⟫`.  A violated quadratic form is therefore
a violated *linear* halfspace, with the same constant: this is the psd cut. -/
theorem qf_eq_frob (X : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    qf X v = frob (vecMulVec v v) X := by
  rw [qf_eq_sum, frob]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp only [vecMulVec_apply]; ring

/-- For a symmetric `X` the Frobenius pairing *is* the matrix trace `tr (C X)`: the brief's
`tr (A cX)` and the pairing `⟪A, cX⟫` are the same function on the algorithm's symmetric points. -/
theorem frob_eq_trace {X : Matrix (Fin n) (Fin n) K} (hX : Xᵀ = X)
    (C : Matrix (Fin n) (Fin n) K) : frob C X = (C * X).trace := by
  simp only [frob, Matrix.trace, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : X i j = X j i := by
    have := congr_fun (congr_fun hX j) i
    simpa using this
  rw [h]

/-! ## 1.  The threshold body -/

/-- Rational PSD: the infinite test the `CertPSD` certificate replaces by a finite one. -/
def PSD (X : Matrix (Fin n) (Fin n) K) : Prop := ∀ x : Fin n → K, 0 ≤ qf X x

/-- The Max-Cut SDP's diagonal constraint. -/
def unitDiag (X : Matrix (Fin n) (Fin n) K) : Prop := ∀ i, X i i = 1

/-- **The threshold body**: positive semidefinite, unit diagonal, objective at least `t`.

Note on looseness: `qf` sees only the symmetric part of its argument, so `PSD` as defined here is
the *symmetrised* PSD cone — a superset of the SDP's feasible set.  That is the safe direction for
the cuts (a halfspace containing the superset contains the body), and the engine's ambient space is
the symmetric slice anyway, so the superset is not reached.  The *affirmative* verdict never relies
on it: `okReport_of_cert` produces the finalization's ledger from an actual `GramCert`, which forces
genuine symmetry (`symm_of_check`) and genuine positive semidefiniteness.

The GLS engine decides `Body A t` nonempty by shrinking an ellipsoid around it; both the cut
validity below and `EllipsoidStep`'s containment are stated against this predicate. -/
def Body (A : Matrix (Fin n) (Fin n) K) (t : K) (X : Matrix (Fin n) (Fin n) K) : Prop :=
  PSD X ∧ unitDiag X ∧ t ≤ frob A X

theorem Body.psd {A : Matrix (Fin n) (Fin n) K} {t : K} {X : Matrix (Fin n) (Fin n) K}
    (h : Body A t X) : PSD X := h.1

theorem Body.unitDiag {A : Matrix (Fin n) (Fin n) K} {t : K} {X : Matrix (Fin n) (Fin n) K}
    (h : Body A t X) : unitDiag X := h.2.1

theorem Body.threshold {A : Matrix (Fin n) (Fin n) K} {t : K} {X : Matrix (Fin n) (Fin n) K}
    (h : Body A t X) : t ≤ frob A X := h.2.2

/-! ## 2.  The oracle's negative verdict: a valid cut with an exact margin

A cut is a normal and a margin.  `Cut.Separates` is the whole contract; `GoodCut` bundles the
data with the two facts the geometry needs from it (`margin_pos` and `separates`).  The engine's
`EllipsoidStep.stepMatrix n A c δ` consumes `normal` as `c` and `margin` as `δ` verbatim — see §6. -/

variable {A : Matrix (Fin n) (Fin n) K} {t : K} {cX : Matrix (Fin n) (Fin n) K}

/-- The unit vector `e_j ∈ K^n`. -/
def delta (j : Fin n) : Fin n → K := fun i => if i = j then 1 else 0

theorem dotProduct_delta (b : Fin n → K) (j : Fin n) : b ⬝ᵥ delta j = b j := by
  rw [dotProduct, Finset.sum_eq_single j]
  · simp [delta]
  · intro i _ hij
    simp [delta, hij]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem qf_delta (M : Matrix (Fin n) (Fin n) K) (j : Fin n) : qf M (delta j) = M j j := by
  rw [qf_eq_sum]
  have h1 : ∀ i, ∑ x, delta j i * (M i x * delta j x) = delta j i * M i j := by
    intro i
    rw [Finset.sum_eq_single j]
    · simp [delta]
    · intro b _ hbj
      simp [delta, hbj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  simp only [h1]
  rw [Finset.sum_eq_single j]
  · simp [delta]
  · intro b _ hbj
    simp [delta, hbj]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- A cut: exact rational data, no proof. -/
structure Cut (K : Type*) (n : ℕ) where
  normal : Matrix (Fin n) (Fin n) K
  margin : K

/-- **Cut validity**: the halfspace `{X | -δ ≤ ⟪N, X - cX⟫}` contains the whole threshold body.
This is the matrix-space form of `EllipsoidStep.containment`'s hypothesis
`Ell A a ∩ {x | -δ ≤ c ⬝ᵥ (x - a)} ⊆ Ell (stepMatrix n A c δ) (stepCenter n A c a δ)`. -/
def Cut.Separates (C : Cut K n) (A : Matrix (Fin n) (Fin n) K) (t : K)
    (cX : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ X, Body A t X → -C.margin ≤ frob C.normal (X - cX)

/-- A cut together with the proof obligations the engine consumes. -/
structure GoodCut (A : Matrix (Fin n) (Fin n) K) (t : K)
    (cX : Matrix (Fin n) (Fin n) K) where
  normal : Matrix (Fin n) (Fin n) K
  margin : K
  margin_pos : 0 < margin
  separates : ∀ X, Body A t X → -margin ≤ frob normal (X - cX)

/-- A `GoodCut` is a `Cut` with the same data satisfying both contracts. -/
theorem GoodCut.valid {G : GoodCut A t cX} :
    (⟨G.normal, G.margin⟩ : Cut K n).Separates A t cX ∧ 0 < G.margin :=
  ⟨G.separates, G.margin_pos⟩

/-! ### 2.1  The psd cut: a violated quadratic form is a violated halfspace

The identity `qf X v = ⟪v vᵀ, X⟫` (`qf_eq_frob`) is the whole content: the rank-one matrix `v vᵀ`
is a *linear* functional in the dual, so a PSD test failing at `v` is a separation certified by
`v` alone.  This is the branch the brief calls `negative Gram factor-rank1-selection`. -/

/-- **psd cut, strict form.**  If `qf cX v = -μ` then every PSD `X` satisfies
`⟪v vᵀ, X - cX⟫ ≥ μ`; the margin is the exact violation `μ`. -/
theorem psdCut_separates {v : Fin n → K} {μ : K} (hq : qf cX v = -μ) :
    ∀ X, Body A t X → μ ≤ frob (vecMulVec v v) (X - cX) := by
  intro X hX
  have h1 : frob (vecMulVec v v) (X - cX) = qf X v - qf cX v := by
    rw [frob_sub, ← qf_eq_frob X v, ← qf_eq_frob cX v]
  rw [h1, hq]
  have h2 : 0 ≤ qf X v := hX.psd v
  linarith

/-- **The psd cut.**  A violated direction with exact violation `μ > 0` yields a valid cut with
normal `v vᵀ` and margin `μ`. -/
def psdCut {v : Fin n → K} {μ : K} (hq : qf cX v = -μ) (hμ : 0 < μ) : GoodCut A t cX where
  normal := vecMulVec v v
  margin := μ
  margin_pos := hμ
  separates := fun X hX => by
    have h := psdCut_separates (cX := cX) (A := A) (t := t) hq X hX
    linarith

/-- The psd cut's normal is nonzero (a violated direction cannot be `0`), so it is a legal
direction for `EllipsoidStep.containment` (`hc : c ≠ 0`). -/
theorem psdCut_normal_ne_zero {v : Fin n → K} {μ : K} (hq : qf cX v = -μ) (hμ : 0 < μ) :
    vecMulVec v v ≠ (0 : Matrix (Fin n) (Fin n) K) := by
  intro h0
  have h1 : qf cX v = 0 := by
    rw [qf_eq_frob, h0]
    simp [frob]
  rw [hq] at h1
  linarith

/-! ### 2.2  The diagonal cut

The diagonal constraint `Xᵢᵢ = 1` is linear, so an off-diagonal centre is separated by `±eᵢeᵢᵀ`
with margin the exact slack `|cXᵢᵢ - 1|`.  The cut *grazes* the body (equality), which is why the
shallow-cut scheme is the right one: the surviving volume is still almost half. -/

/-- `⟪v vᵀ, X - cX⟫` for the unit vector `v = eᵢ`. -/
theorem frob_delta_sub (X Y : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    frob (vecMulVec (delta i) (delta i)) (X - Y) = X i i - Y i i := by
  rw [frob_sub, ← qf_eq_frob X (delta i), ← qf_eq_frob Y (delta i), qf_delta, qf_delta]

/-- **Diag cut, upper side**: `1 < cXᵢᵢ` gives normal `eᵢeᵢᵀ` and margin `cXᵢᵢ - 1`. -/
theorem diagCut_up_separates {i : Fin n} (h : 1 < cX i i) :
    ∀ X, Body A t X → -(cX i i - 1) ≤ frob (vecMulVec (delta i) (delta i)) (X - cX) := by
  intro X hX
  rw [frob_delta_sub, hX.unitDiag i]
  linarith

/-- **Diag cut, lower side**: `cXᵢᵢ < 1` gives normal `-(eᵢeᵢᵀ)` and margin `1 - cXᵢᵢ`. -/
theorem diagCut_down_separates {i : Fin n} (h : cX i i < 1) :
    ∀ X, Body A t X → -(1 - cX i i) ≤ frob (-(vecMulVec (delta i) (delta i))) (X - cX) := by
  intro X hX
  rw [frob_neg_left, frob_delta_sub, hX.unitDiag i]

def diagCut_up {i : Fin n} (h : 1 < cX i i) : GoodCut A t cX where
  normal := vecMulVec (delta i) (delta i)
  margin := cX i i - 1
  margin_pos := by linarith
  separates := diagCut_up_separates h

def diagCut_down {i : Fin n} (h : cX i i < 1) : GoodCut A t cX where
  normal := -(vecMulVec (delta i) (delta i))
  margin := 1 - cX i i
  margin_pos := by linarith
  separates := diagCut_down_separates h

theorem diagCut_up_normal_ne_zero {i : Fin n} :
    (vecMulVec (delta i) (delta i)) ≠ (0 : Matrix (Fin n) (Fin n) K) := by
  intro h0
  have h1 : (vecMulVec (delta i) (delta i) : Matrix (Fin n) (Fin n) K) i i = 0 := by
    rw [h0]
    simp
  rw [vecMulVec_apply] at h1
  have hd : delta i i = (1 : K) := by simp [delta]
  simp only [hd, one_mul] at h1
  exact one_ne_zero h1

theorem diagCut_down_normal_ne_zero {i : Fin n} :
    (-(vecMulVec (delta i) (delta i))) ≠ (0 : Matrix (Fin n) (Fin n) K) := by
  intro h0
  exact diagCut_up_normal_ne_zero (i := i) (neg_eq_zero.mp h0)

/-! ### 2.3  The threshold cut

If the centre's objective is short of `t`, the objective itself is the separating functional.
The margin `t - ⟪A, cX⟫` is the exact deficit. -/

/-- **Threshold cut, strict form.** -/
theorem traceCut_separates (h : frob A cX < t) :
    ∀ X, Body A t X → t - frob A cX ≤ frob A (X - cX) := by
  intro X hX
  rw [frob_sub]
  have := hX.threshold
  linarith

def traceCut (h : frob A cX < t) : GoodCut A t cX where
  normal := A
  margin := t - frob A cX
  margin_pos := by linarith
  separates := fun X hX => by
    have h2 := traceCut_separates (A := A) (t := t) (cX := cX) h X hX
    linarith

/-! ### 2.4  Totality: the oracle never fails

Exactly one of the three branches applies to any centre, so the oracle is **total**.  No symmetry
assumption is needed (`PSD` is stated on the quadratic form alone), and the psd witness is the
only place where classical choice enters. -/

/-- The oracle's affirmative verdict: the centre itself is a feasible threshold point. -/
def Ok (A : Matrix (Fin n) (Fin n) K) (t : K) (cX : Matrix (Fin n) (Fin n) K) : Prop :=
  PSD cX ∧ unitDiag cX ∧ t ≤ frob A cX

/-- **Totality.**  For every centre and threshold, either the centre is a feasible threshold point
or a valid cut with strictly positive margin exists. -/
theorem ok_or_cut (A : Matrix (Fin n) (Fin n) K) (t : K) (cX : Matrix (Fin n) (Fin n) K) :
    Ok A t cX ∨ Nonempty (GoodCut A t cX) := by
  by_cases hpsd : PSD cX
  · by_cases hdiag : unitDiag cX
    · by_cases htr : t ≤ frob A cX
      · exact Or.inl ⟨hpsd, hdiag, htr⟩
      · simp only [not_le] at htr
        exact Or.inr ⟨traceCut htr⟩
    · simp only [unitDiag, not_forall] at hdiag
      obtain ⟨i, hi⟩ := hdiag
      rcases lt_or_gt_of_ne hi with h | h
      · exact Or.inr ⟨diagCut_down h⟩
      · exact Or.inr ⟨diagCut_up h⟩
  · simp only [PSD, not_forall, not_le] at hpsd
    obtain ⟨v, hv⟩ := hpsd
    exact Or.inr ⟨psdCut (μ := -qf cX v) (by ring) (by linarith)⟩

/-- The oracle's verdict type: `ok` carries the three facts, `cut` carries a proved cut. -/
inductive Response (A : Matrix (Fin n) (Fin n) K) (t : K) (cX : Matrix (Fin n) (Fin n) K) :
    Type _ where
  | ok (hpsd : PSD cX) (hdiag : unitDiag cX) (htr : t ≤ frob A cX) : Response A t cX
  | cut (c : GoodCut A t cX) : Response A t cX

/-- Every query has an answer: the separation oracle is total. -/
theorem response_total (A : Matrix (Fin n) (Fin n) K) (t : K) (cX : Matrix (Fin n) (Fin n) K) :
    Nonempty (Response A t cX) := by
  rcases ok_or_cut A t cX with h | h
  · exact ⟨Response.ok h.1 h.2.1 h.2.2⟩
  · obtain ⟨G⟩ := h
    exact ⟨Response.cut G⟩

/-- The oracle as a function (classical choice over the totality theorem). -/
noncomputable def oracle (A : Matrix (Fin n) (Fin n) K) (t : K)
    (cX : Matrix (Fin n) (Fin n) K) : Response A t cX :=
  Classical.choice (response_total A t cX)

/-! ## 3.  The `ok` verdict's margin ledger

The `ok` branch is what the iteration loop extracts its primal point from, so it has to carry
*margins*, not exact equations: the loop only ever knows its centre to within the accumulated
step error, and the finalization has to accept a point that is `δ`-feasible rather than feasible.

`OkReport A t cX` is that ledger: a rational tolerance `δ > 0`, the PSD margin `-δ/2·∑x²`
(the exact output shape of `CertPSD.premise_of_check_shifted`), the diagonal closeness
`|cXᵢᵢ - 1| ≤ δ/4` and the objective closeness `t - δ/2 ≤ ⟪A, cX⟫`.  `okReport_of_cert` closes the
PSD margin from a passing `GramCert` outright, and `okReport_of_shifted_cert` from a certificate
for a *nearby* matrix — the engine's `ε`-degradation path, with `δ = 2εn` the exchange rate. -/

/-- The `ok` branch's obligation bundle.  Every field is a rational, machine-checkable margin. -/
structure OkReport (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (t : ℚ)
    (cX : Matrix (Fin n) (Fin n) ℚ) where
  /-- the feasibility/optimality tolerance -/
  δ : ℚ
  δ_pos : 0 < δ
  /-- PSD with a margin: the shape `CertPSD.premise_of_check_shifted` produces -/
  psd_margin : ∀ x : Fin n → ℚ, -(δ / 2) * (∑ i, x i ^ 2) ≤ qf cX x
  /-- diagonal closeness to the constraint -/
  diag_near : ∀ i, |cX i i - 1| ≤ δ / 4
  /-- objective closeness to the threshold -/
  trace_near : t - δ / 2 ≤ frob A cX

/-- The trivial exchange rate: an exact `ok` centre satisfies the ledger with `δ = 1`. -/
def okReport_of_ok {A : Matrix (Fin n) (Fin n) ℚ} {t : ℚ} {cX : Matrix (Fin n) (Fin n) ℚ}
    (h : Ok (K := ℚ) A t cX) : OkReport n A t cX where
  δ := 1
  δ_pos := one_pos
  psd_margin := fun x => by
    have h0 : 0 ≤ qf cX x := h.1 x
    have h1 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    nlinarith
  diag_near := fun i => by
    have h0 : cX i i = 1 := h.2.1 i
    rw [h0]
    norm_num
  trace_near := by
    have h0 : t ≤ frob A cX := h.2.2
    linarith

/-- A rational Gram certificate: `V diag c Vᵀ` with `c ≥ 0`.  (Recap of `QMCLeafB.CertPSD`,
repeated so that this brick stands alone; the names and statements coincide.) -/
structure GramCert (n m : ℕ) where
  V : Matrix (Fin n) (Fin m) ℚ
  c : Fin m → ℚ

namespace GramCert

variable {n m : ℕ} (C : GramCert n m)

/-- The certified matrix `V diag c Vᵀ`. -/
def mat : Matrix (Fin n) (Fin n) ℚ := C.V * diagonal C.c * C.Vᵀ

theorem mat_apply (i j : Fin n) : C.mat i j = ∑ k, C.V i k * (C.c k * C.V j k) := by
  rw [mat, Matrix.mul_apply]
  simp only [mul_diagonal, transpose_apply]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem mat_transpose : C.matᵀ = C.mat := by
  ext i j
  simp only [transpose_apply, mat_apply]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem diagonal_mulVec (c y : Fin m → ℚ) : diagonal c *ᵥ y = fun k => c k * y k := by
  funext k
  exact Matrix.mulVec_diagonal c y k

/-- The sum-of-squares identity: the certified quadratic form is a nonnegative combination of
squares of linear forms.  Pure `ℚ`-algebra. -/
theorem qf_mat (x : Fin n → ℚ) :
    qf C.mat x = ∑ k, C.c k * (∑ i, x i * C.V i k) ^ 2 := by
  rw [qf, mat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose,
    diagonal_mulVec, Matrix.dotProduct_mulVec]
  simp only [dotProduct, vecMul]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem qf_mat_nonneg (hc : ∀ k, 0 ≤ C.c k) (x : Fin n → ℚ) : 0 ≤ qf C.mat x := by
  rw [qf_mat]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hc k) (sq_nonneg _))

/-- The executable check: `n²` exact rational equalities and `m` exact sign tests. -/
def check (X : Matrix (Fin n) (Fin n) ℚ) : Bool :=
  decide (C.mat = X ∧ ∀ k, 0 ≤ C.c k)

theorem check_spec (X : Matrix (Fin n) (Fin n) ℚ) :
    C.check X = true ↔ C.mat = X ∧ ∀ k, 0 ≤ C.c k := by
  simp [check]

end GramCert

/-- **Soundness**: a passing check gives the infinite PSD premise. -/
theorem premise_of_check {n m : ℕ} (C : GramCert n m) (X : Matrix (Fin n) (Fin n) ℚ)
    (h : C.check X = true) : ∀ x : Fin n → ℚ, 0 ≤ qf X x := by
  obtain ⟨rfl, hc⟩ := (GramCert.check_spec C X).mp h
  exact GramCert.qf_mat_nonneg C hc

/-- A passing check also gives symmetry for free. -/
theorem symm_of_check {n m : ℕ} (C : GramCert n m) (X : Matrix (Fin n) (Fin n) ℚ)
    (h : C.check X = true) : Xᵀ = X := by
  obtain ⟨rfl, -⟩ := (GramCert.check_spec C X).mp h
  exact GramCert.mat_transpose C

/-- **The `ok` ledger from an exact certificate**: `δ = 1` and the PSD margin is free, because
the certified form is nonnegative on the nose while `-δ/2·∑x² ≤ 0`. -/
def okReport_of_cert {n m : ℕ} {C : GramCert n m}
    {A : Matrix (Fin n) (Fin n) ℚ} {t : ℚ} {cX : Matrix (Fin n) (Fin n) ℚ}
    (hcheck : C.check cX = true) (hdiag : ∀ i, cX i i = 1) (htr : t ≤ frob A cX) :
    OkReport n A t cX where
  δ := 1
  δ_pos := one_pos
  psd_margin := fun x => by
    have h0 : 0 ≤ qf cX x := premise_of_check C cX hcheck x
    have h1 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    nlinarith
  diag_near := fun i => by
    rw [hdiag i]
    norm_num
  trace_near := by linarith

/-! ### 3.1  The robust margin: entrywise perturbation of a certified matrix

`premise_of_check_shifted` says a certificate for `X₀` bounds the quadratic form of anything
entrywise `ε`-close to it by `-ε·n·∑x²`.  That is exactly `OkReport.psd_margin` with
`δ = 2εn`; the transfer is below, and it is the only place the oracle's arithmetic touches a
real-analytic quantity. -/

/-- Entrywise perturbation bound `|qf R x| ≤ ε·n·∑x²` (recap of `CertPSD`, re-proved here so the
brick stands alone). -/
theorem abs_qf_le_of_entrywise_le (R : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) {ε : ℚ}
    (hR : ∀ i j, |R i j| ≤ ε) (hε : 0 ≤ ε) :
    |qf R x| ≤ ε * (n : ℚ) * ∑ i, x i ^ 2 := by
  rw [qf_eq_sum]
  have h1 : |∑ i, ∑ j, x i * (R i j * x j)| ≤ ∑ i, ∑ j, |x i| * (ε * |x j|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    calc |x i * (R i j * x j)| = |x i| * (|R i j| * |x j|) := by rw [abs_mul, abs_mul]
      _ ≤ |x i| * (ε * |x j|) := by gcongr; exact hR i j
  have h2 : ∑ i, ∑ j, |x i| * (ε * |x j|) = ε * (∑ i, |x i|) * (∑ i, |x i|) := by
    have hinner : ∀ i, ∑ j, |x i| * (ε * |x j|) = |x i| * (ε * ∑ j, |x j|) := by
      intro i
      rw [Finset.mul_sum, Finset.mul_sum]
    simp only [hinner]
    rw [← Finset.sum_mul]
    ring
  have h3 : (∑ i, |x i|) * (∑ i, |x i|) ≤ (n : ℚ) * ∑ i, x i ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun i => |x i|) (fun _ => (1 : ℚ))
    have hsq : (∑ i, |x i|) ^ 2 ≤ (n : ℚ) * ∑ i, x i ^ 2 := by
      simpa [Finset.sum_const, sq_abs, mul_comm] using h
    nlinarith [hsq]
  rw [h2] at h1
  have h4 : ε * (∑ i, |x i|) * (∑ i, |x i|) ≤ ε * ((n : ℚ) * ∑ i, x i ^ 2) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h3 hε
  have h5 : |∑ i, ∑ j, x i * (R i j * x j)| ≤ ε * ((n : ℚ) * ∑ i, x i ^ 2) :=
    le_trans h1 h4
  calc |∑ i, ∑ j, x i * (R i j * x j)| ≤ ε * ((n : ℚ) * ∑ i, x i ^ 2) := h5
    _ = ε * (n : ℚ) * ∑ i, x i ^ 2 := by ring

/-- **Robust soundness**: a certificate for `X₀` bounds the quadratic form of `X₀ + R`. -/
theorem psd_of_cert_shifted {n m : ℕ} (C : GramCert n m) {X₀ X R : Matrix (Fin n) (Fin n) ℚ}
    (hX : C.check X₀ = true) (hXR : X = X₀ + R) {ε : ℚ}
    (hR : ∀ i j, |R i j| ≤ ε) (hε : 0 ≤ ε) :
    ∀ x : Fin n → ℚ, -(ε * (n : ℚ) * ∑ i, x i ^ 2) ≤ qf X x := by
  intro x
  have h0 := premise_of_check C X₀ hX x
  have h1 := abs_qf_le_of_entrywise_le R x hR hε
  have h2 : qf X x = qf X₀ x + qf R x := by rw [hXR, qf_add]
  rw [h2]
  have := neg_abs_le (qf R x)
  linarith

/-- **The PSD margin at tolerance `δ`** from a shifted certificate, with the exchange rate
`2εn ≤ δ`. -/
theorem psdMargin_of_shifted_cert {n m : ℕ} (C : GramCert n m)
    {X₀ cX R : Matrix (Fin n) (Fin n) ℚ} (hcheck : C.check X₀ = true) (hXR : cX = X₀ + R)
    {ε δ : ℚ} (hR : ∀ i j, |R i j| ≤ ε) (hε : 0 ≤ ε) (hδ : 2 * (ε * (n : ℚ)) ≤ δ) :
    ∀ x : Fin n → ℚ, -(δ / 2) * (∑ i, x i ^ 2) ≤ qf cX x := by
  intro x
  have h0 : -(ε * (n : ℚ) * ∑ i, x i ^ 2) ≤ qf cX x :=
    psd_of_cert_shifted C hcheck hXR hR hε x
  have h1 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h2 : (ε * (n : ℚ)) * (∑ i, x i ^ 2) ≤ (δ / 2) * (∑ i, x i ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ h1
    linarith
  nlinarith

/-- **The `ok` ledger assembled from three independent margin sources** with a common tolerance
`δ`: a shifted certificate gives the PSD margin, and the diagonal/objective closeness are measured
(by the loop) in the same currency. -/
def okReport_of_shifted_cert {n m : ℕ} {C : GramCert n m}
    {A X₀ cX R : Matrix (Fin n) (Fin n) ℚ} {t : ℚ} (hcheck : C.check X₀ = true)
    (hXR : cX = X₀ + R) {ε δ : ℚ} (hR : ∀ i j, |R i j| ≤ ε) (hε : 0 ≤ ε)
    (hδ2 : 2 * (ε * (n : ℚ)) ≤ δ) (hδ : 0 < δ)
    (hdiag : ∀ i, |cX i i - 1| ≤ δ / 4) (htr : t - δ / 2 ≤ frob A cX) :
    OkReport n A t cX where
  δ := δ
  δ_pos := hδ
  psd_margin := psdMargin_of_shifted_cert C hcheck hXR hR hε hδ2
  diag_near := hdiag
  trace_near := htr

/-- `OkReport` in the brief's own notation: for a symmetric centre the objective test is
`tr (A cX)`, and the ledger says `t - δ/2 ≤ tr (A cX)`. -/
theorem OkReport.trace_near_trace {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {t : ℚ}
    {cX : Matrix (Fin n) (Fin n) ℚ} (G : OkReport n A t cX) (hs : cXᵀ = cX) :
    t - G.δ / 2 ≤ (A * cX).trace := by
  rw [← frob_eq_trace hs A]
  exact G.trace_near

/-! ## 4.  The ℝ instances: what the ellipsoid geometry consumes

Everything in §2 is stated over an arbitrary linear ordered field, so the geometric side of the
campaign (`Ell A a`, `stepMatrix n A c δ`, `stepCenter`, all over `ℝ`) instantiates the *same*
theorems with the rational data cast by `Rat.castHom ℝ`.  This section records the two cast
transports that are not definitional (`qf` and `frob` commute with a ring hom) and the three
worked ℝ corollaries. -/

section CastLayer

variable {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]

/-- `qf` commutes with ring homs: casting a rational quadratic form is the real one. -/
theorem qf_map (f : K →+* L) (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    qf (M.map f) (fun i => f (x i)) = f (qf M x) := by
  simp only [qf_eq_sum, map_sum, map_mul, Matrix.map_apply]

/-- `frob` commutes with ring homs. -/
theorem frob_map (f : K →+* L) (C X : Matrix (Fin n) (Fin n) K) :
    frob (C.map f) (X.map f) = f (frob C X) := by
  simp only [frob, map_sum, map_mul, Matrix.map_apply]

end CastLayer

/-- Cast a rational matrix to the reals. -/
noncomputable def castMat (M : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  M.map (Rat.castHom ℝ)

theorem castMat_apply (M : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    castMat M i j = (M i j : ℝ) := rfl

theorem castMat_vecMulVec (v : Fin n → ℚ) :
    castMat (vecMulVec v v) = vecMulVec (fun i => (v i : ℝ)) (fun i => (v i : ℝ)) := by
  ext i j
  simp [castMat, vecMulVec_apply]

theorem castMat_delta (i : Fin n) :
    castMat (vecMulVec (delta (K := ℚ) i) (delta (K := ℚ) i))
      = vecMulVec (delta (K := ℝ) i) (delta (K := ℝ) i) := by
  ext a b
  by_cases h1 : a = i <;> by_cases h2 : b = i <;> simp [castMat, vecMulVec_apply, delta, h1, h2]

/-- **The psd cut over ℝ**: rational violation `qf cX v = -μ` separates the *real* threshold body
with the same rational margin. -/
theorem psdCut_separates_R {A cX : Matrix (Fin n) (Fin n) ℚ} {t : ℚ} {v : Fin n → ℚ} {μ : ℚ}
    (hq : qf cX v = -μ) :
    ∀ X : Matrix (Fin n) (Fin n) ℝ, Body (K := ℝ) (castMat A) (t : ℝ) X →
      (μ : ℝ) ≤ frob (castMat (vecMulVec v v)) (X - castMat cX) := by
  intro X hX
  have hq' : qf (castMat cX) (fun i => (v i : ℝ)) = -((μ : ℝ)) := by
    have h := qf_map (Rat.castHom ℝ) cX v
    rw [hq] at h
    simpa [castMat] using h
  rw [castMat_vecMulVec]
  exact psdCut_separates (K := ℝ) (cX := castMat cX) (A := castMat A) (t := (t : ℝ)) hq' X hX

/-- **The diagonal cut over ℝ** (upper side). -/
theorem diagCut_up_separates_R {A cX : Matrix (Fin n) (Fin n) ℚ} {t : ℚ} {i : Fin n}
    (h : 1 < cX i i) :
    ∀ X : Matrix (Fin n) (Fin n) ℝ, Body (K := ℝ) (castMat A) (t : ℝ) X →
      -(((cX i i : ℚ) : ℝ) - 1) ≤
        frob (castMat (vecMulVec (delta (K := ℚ) i) (delta (K := ℚ) i))) (X - castMat cX) := by
  intro X hX
  rw [castMat_delta]
  refine diagCut_up_separates (K := ℝ) (cX := castMat cX) (A := castMat A) (t := (t : ℝ)) ?_ X hX
  have h' : ((1 : ℚ) : ℝ) < ((cX i i : ℚ) : ℝ) := by exact_mod_cast h
  simpa [castMat] using h'

/-- **The threshold cut over ℝ.** -/
theorem traceCut_separates_R {A cX : Matrix (Fin n) (Fin n) ℚ} {t : ℚ}
    (h : frob A cX < t) :
    ∀ X : Matrix (Fin n) (Fin n) ℝ, Body (K := ℝ) (castMat A) (t : ℝ) X →
      (t : ℝ) - frob (castMat A) (castMat cX) ≤ frob (castMat A) (X - castMat cX) := by
  intro X hX
  have h' : frob (castMat A) (castMat cX) < (t : ℝ) := by
    have h2 : ((frob A cX : ℚ) : ℝ) < (t : ℝ) := by exact_mod_cast h
    have h3 : frob (castMat A) (castMat cX) = ((frob A cX : ℚ) : ℝ) :=
      frob_map (Rat.castHom ℝ) A cX
    rw [h3]
    exact h2
  have h2 := traceCut_separates (K := ℝ) (A := castMat A) (t := (t : ℝ)) (cX := castMat cX) h' X hX
  linarith

/-! ## 5.  Companion report: the margin as `EllipsoidStep`'s `δ`

`EllipsoidStep` works in the `A`-form: the ellipsoid is `Ell A a = {x | (x-a)ᵀ A (x-a) ≤ 1}`,
`stepMatrix n A c δ = α • (A + (β/σ) • c cᵀ)` and `stepCenter n A c a δ = a + (γ/r) • A⁻¹c`, and
its containment theorem is

  `Ell A a ∩ {x | -δ ≤ c ⬝ᵥ (x - a)} ⊆ Ell (stepMatrix n A c δ) (stepCenter n A c a δ)`,

under exactly two side conditions on the pair `(c, δ)`: `c ≠ 0` and `0 ≤ δ`.  The mapping is
therefore *verbatim*:

| oracle branch | `EllipsoidStep`'s `c` | `EllipsoidStep`'s `δ` | side conditions |
|---|---|---|---|
| psd        | `v vᵀ` (vectorised) | `μ = -qf cX v` | `psdCut_normal_ne_zero`, `0 < μ` |
| diag       | `± eᵢeᵢᵀ`          | `|cXᵢᵢ - 1|`   | `diagCut_up/down_normal_ne_zero`, margin `> 0` |
| threshold  | `A`               | `t - ⟪A, cX⟫` | requires `A ≠ 0` (the engine's `A` is the nonzero QMC matrix) |

and `GoodCut.separates` is precisely the halfspace-containment hypothesis of the theorem above:
`∀ X ∈ Body, -δ ≤ ⟪N, X - cX⟫`.  Two remarks that the iterate loop depends on:

1. **The depth is scale invariant.**  Replacing the normal `c` by `λ • c` (`λ > 0`) does not change
   the relative depth `δ̂ = δ/√(cᵀA⁻¹c)` provided the margin is scaled by `λ` too
   (`depth_scale_invariant`).  So the *off-diagonal* normalisation discussed in remark 2 costs
   nothing.
2. **Coordinate reduction.**  The engine runs in the affine slice `{X | ∀ i, Xᵢᵢ = 1}`
   (dimension `n(n-1)/2`), on which the pairings above collapse to
   `⟪C, X - cX⟫ = ∑_{i<j} (Cᵢⱼ + Cⱼᵢ) (Xᵢⱼ - cXᵢⱼ)` (the diagonal terms vanish because both
   points have unit diagonal).  In particular the diag branch *cannot fire* inside a unit-diagonal
   slice — its whole content is the constraint that the slice built in — and for symmetric normals
   the effective coordinate direction is `2·Cᵢⱼ` (`i < j`), which by remark 1 is the same
   direction with margin `2δ`.  The loop should therefore maintain `unitDiag` as an invariant and
   keep `(coordinate normal, 2 * margin)`. -/

/-- **Depth is invariant under positive rescaling of the cut normal**: if `c` becomes `λ • c` then
`σ = cᵀA⁻¹c` becomes `λ²σ` and `δ̂ = δ/√σ` is unchanged when `δ` is scaled by `λ` as well. -/
theorem depth_scale_invariant {σ δ lam : ℝ} (hlam : 0 < lam) (hσ : 0 < σ) :
    (lam * δ) / Real.sqrt (lam ^ 2 * σ) = δ / Real.sqrt σ := by
  have h : Real.sqrt (lam ^ 2 * σ) = lam * Real.sqrt σ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hlam.le]
  rw [h]
  field_simp

/-- The margin of a `GoodCut` is a genuine `EllipsoidStep` depth numerator: nonnegative. -/
theorem GoodCut.margin_nonneg {A : Matrix (Fin n) (Fin n) K} {t : K}
    {cX : Matrix (Fin n) (Fin n) K} (G : GoodCut A t cX) : 0 ≤ G.margin := G.margin_pos.le


end Generic

variable {n : ℕ}

/-! ## 5.5  The computable PSD split: exact rational LDLᵀ with a witness

`response_total` is a *classical* totality statement: the psd witness comes from `Classical.choice`
over `¬∀x, 0 ≤ qf cX x`.  For the oracle to be a `PolyProgram` it has to be a **computation**, so
this section replaces the choice by an exact rational pivot recursion (`split`), which is a `def`:
no `Classical.choice` appears in its *data* (only in the proofs that its output is correct).

The recursion is the `L D Lᵀ` decomposition of `CertPSD.exists_gram`, run as a decision procedure:

* `X₀₀ < 0`  ⟹ `e₀` is violated on the nose (`qf_delta`).
* `X₀₀ = 0` and the first row `b` vanishes ⟹ `qf X (0, y) = qf (tail X) y`, so recurse on the tail.
* `X₀₀ = 0` and `b ≠ 0` ⟹ the explicit rational vector `v = (t, b)` with
  `t = -(qf (tail X) b + 1) / (2·bᵀb)` has `qf X v = -1 < 0`; no search for a nonzero coordinate is
  needed in the *data* (only in the proof that `bᵀb > 0`).
* `X₀₀ > 0` ⟹ recurse on the Schur complement `schur X a`: a violated `y` lifts by `qf_schur`, and a
  certificate `W` lifts by `liftCert` — the same block computation as `exists_gram`, with `a⁻¹ ≥ 0`
  guaranteeing the weight sign.

The output type `Split n X` carries either the `GramCert` (checked, so `∀x, 0 ≤ qf X x` follows) or a
genuinely violated rational vector.  `sepOracle` then reads it off, and `#eval` at the end shows the
computation running. -/

section Computable

variable {k : ℕ}

/-- Scaling the matrix scales the quadratic form (the `qf_schur` ingredient). -/
theorem qf_smulQ (c : ℚ) (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    qf (c • M) x = c * qf M x := by
  rw [qf, Matrix.smul_mulVec, qf]
  simp only [dotProduct, Pi.smul_apply, Finset.mul_sum, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- A rank-one matrix's quadratic form is the product of the two linear forms. -/
theorem qf_vecMulVecQ (u v x : Fin n → ℚ) :
    qf (vecMulVec u v) x = (u ⬝ᵥ x) * (v ⬝ᵥ x) := by
  rw [qf_eq_sum]
  simp only [vecMulVec_apply, dotProduct]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- The trailing `k × k` block. -/
def tail (X : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) : Matrix (Fin k) (Fin k) ℚ :=
  X.submatrix Fin.succ Fin.succ

/-- The first row, dropped at the corner. -/
def headRow (X : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) : Fin k → ℚ := fun j => X 0 j.succ

/-- The leading-coordinate split of the quadratic form. -/
theorem qf_cons (X : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) (hsym : ∀ i j, X i j = X j i)
    (x0 : ℚ) (y : Fin k → ℚ) :
    qf X (Fin.cons x0 y) = X 0 0 * x0 ^ 2 + 2 * x0 * (headRow X ⬝ᵥ y) + qf (tail X) y := by
  rw [qf_eq_sum, qf_eq_sum]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ, tail, submatrix_apply,
    headRow, dotProduct]
  rw [Finset.sum_add_distrib]
  have h1 : (∑ i, x0 * (X 0 i.succ * y i)) = x0 * ∑ i, X 0 i.succ * y i := by
    rw [Finset.mul_sum]
  have h2 : (∑ i, y i * (X i.succ 0 * x0)) = x0 * ∑ i, X 0 i.succ * y i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [hsym i.succ 0]; ring)
  rw [h1, h2]
  ring

/-- The Schur complement `tail X - a⁻¹ • b bᵀ`. -/
def schur (X : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) (a : ℚ) : Matrix (Fin k) (Fin k) ℚ :=
  tail X - a⁻¹ • vecMulVec (headRow X) (headRow X)

/-- **The Schur transfer**: the lifted vector `(-(b ⬝ y)/a, y)` has the Schur complement's form. -/
theorem qf_schur (X : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) (hsym : ∀ i j, X i j = X j i)
    {a : ℚ} (ha : X 0 0 = a) (ha0 : a ≠ 0) (y : Fin k → ℚ) :
    qf X (Fin.cons (-(headRow X ⬝ᵥ y) / a) y) = qf (schur X a) y := by
  rw [qf_cons X hsym, schur, qf_sub, qf_smulQ, qf_vecMulVecQ, ha]
  field_simp
  ring

theorem schur_symm (X : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) (hsym : ∀ i j, X i j = X j i)
    (a : ℚ) : ∀ p q, schur X a p q = schur X a q p := by
  intro p q
  simp only [schur, tail, headRow, submatrix_apply, vecMulVec_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hsym p.succ q.succ]
  ring

theorem tail_symm (X : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) (hsym : ∀ i j, X i j = X j i) :
    ∀ p q, tail X p q = tail X q p := by
  intro p q
  simp only [tail, submatrix_apply]
  exact hsym _ _

/-- `b ⬝ b > 0` for a nonzero `b` (the search for a nonzero coordinate happens only in the proof). -/
theorem dotProduct_self_pos {v : Fin k → ℚ} (h : v ≠ 0) : 0 < v ⬝ᵥ v := by
  have h1 : ∑ i, v i * v i = ∑ i, (v i) ^ 2 := Finset.sum_congr rfl (fun i _ => by ring)
  rw [dotProduct, h1]
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hc
    exact h (funext fun j => by by_contra h2; exact hc ⟨j, h2⟩)
  exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ j, by
    rw [pow_two]; exact mul_self_pos.mpr hj⟩

/-- **The zero-pivot witness**: with `X₀₀ = 0` and a nonzero first row `b`, the explicit rational
vector `(t, b)` with `t = -(qf (tail X) b + 1)/(2 bᵀb)` violates the quadratic form by exactly `1`. -/
theorem zeroPivot_witness (X : Matrix (Fin (k+1)) (Fin (k+1)) ℚ) (hsym : ∀ i j, X i j = X j i)
    (h00 : X 0 0 = 0) (hb : headRow X ≠ 0) :
    qf X (Fin.cons (-(qf (tail X) (headRow X) + 1) / (2 * (headRow X ⬝ᵥ headRow X))) (headRow X))
      < 0 := by
  have hpos : 0 < headRow X ⬝ᵥ headRow X := dotProduct_self_pos hb
  have h2 : 2 * (-(qf (tail X) (headRow X) + 1) / (2 * (headRow X ⬝ᵥ headRow X)))
      * (headRow X ⬝ᵥ headRow X) = -(qf (tail X) (headRow X) + 1) := by
    field_simp
  rw [qf_cons X hsym, h00, h2]
  simp

/-- Add a leading rank-one term to a certificate. -/
def liftCert (v : Fin (k+1) → ℚ) (c0 : ℚ) {m : ℕ} (W : GramCert k m) : GramCert (k+1) (m+1) :=
  ⟨fun i l => Fin.cases (v i) (fun l' => Fin.cases 0 (fun i' => W.V i' l') i) l,
   Fin.cons c0 W.c⟩

theorem liftCert_mat_00 (v : Fin (k+1) → ℚ) (c0 : ℚ) {m : ℕ} (W : GramCert k m) :
    (liftCert v c0 W).mat 0 0 = c0 * (v 0 * v 0) := by
  rw [GramCert.mat_apply, Fin.sum_univ_succ]
  simp [liftCert, Fin.cases_zero, Fin.cases_succ]
  ring

theorem liftCert_mat_0s (v : Fin (k+1) → ℚ) (c0 : ℚ) {m : ℕ} (W : GramCert k m) (q : Fin k) :
    (liftCert v c0 W).mat 0 q.succ = c0 * (v 0 * v q.succ) := by
  rw [GramCert.mat_apply, Fin.sum_univ_succ]
  simp [liftCert, Fin.cases_zero, Fin.cases_succ]
  ring

theorem liftCert_mat_s0 (v : Fin (k+1) → ℚ) (c0 : ℚ) {m : ℕ} (W : GramCert k m) (p : Fin k) :
    (liftCert v c0 W).mat p.succ 0 = c0 * (v p.succ * v 0) := by
  rw [GramCert.mat_apply, Fin.sum_univ_succ]
  simp [liftCert, Fin.cases_zero, Fin.cases_succ]
  ring

theorem liftCert_mat_ss (v : Fin (k+1) → ℚ) (c0 : ℚ) {m : ℕ} (W : GramCert k m)
    (p q : Fin k) :
    (liftCert v c0 W).mat p.succ q.succ = c0 * (v p.succ * v q.succ) + W.mat p q := by
  rw [GramCert.mat_apply, Fin.sum_univ_succ, GramCert.mat_apply]
  simp [liftCert, Fin.cases_zero, Fin.cases_succ]
  ring

theorem liftCert_c_nonneg (v : Fin (k+1) → ℚ) {c0 : ℚ} (hc0 : 0 ≤ c0) {m : ℕ} {W : GramCert k m}
    (hc : ∀ l, 0 ≤ W.c l) : ∀ l, 0 ≤ (liftCert v c0 W).c l := by
  intro l
  refine Fin.cases ?_ ?_ l
  · simpa [liftCert] using hc0
  · intro l'
    simpa [liftCert] using hc l'

/-- The split's output: a checked certificate, or an explicit violated rational vector. -/
inductive Split (n : ℕ) (X : Matrix (Fin n) (Fin n) ℚ) : Type where
  | psd (m : ℕ) (C : GramCert n m) (h : C.check X = true) : Split n X
  | violated (v : Fin n → ℚ) (h : qf X v < 0) : Split n X

/-- **The computable split.**  Exact rational pivot recursion on the dimension: no `Classical.choice`
in the returned data. -/
def split : (n : ℕ) → (X : Matrix (Fin n) (Fin n) ℚ) → (∀ i j, X i j = X j i) → Split n X
  | 0, X, _ =>
      Split.psd 0 ⟨(fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩
        ((GramCert.check_spec _ X).mpr ⟨Subsingleton.elim _ _, fun l => Fin.elim0 l⟩)
  | (k+1), X, hsym =>
      if hneg : X 0 0 < 0 then
        Split.violated (delta 0) (by rw [qf_delta]; exact hneg)
      else if hz : X 0 0 = 0 then
        if hb : headRow X = 0 then
          match split k (tail X) (tail_symm X hsym) with
          | Split.psd m W hW =>
              Split.psd (m+1) (liftCert (fun i => X i 0) 0 W) (by
                obtain ⟨hWmat, hWc⟩ := (GramCert.check_spec W (tail X)).mp hW
                refine (GramCert.check_spec _ X).mpr ⟨?_, ?_⟩
                · ext i j
                  refine Fin.cases ?_ ?_ i
                  · refine Fin.cases ?_ ?_ j
                    · rw [liftCert_mat_00]; simp [hz]
                    · intro q
                      rw [liftCert_mat_0s]
                      have hbq : X 0 q.succ = 0 := by
                        have := congrFun hb q
                        simpa [headRow] using this
                      simp [hbq]
                  · intro p
                    refine Fin.cases ?_ ?_ j
                    · rw [liftCert_mat_s0]
                      have hbp : X p.succ 0 = 0 := by rw [hsym p.succ 0]; exact congrFun hb p
                      simp [hbp]
                    · intro q
                      rw [liftCert_mat_ss, hWmat]
                      simp [tail, submatrix_apply]
                · exact liftCert_c_nonneg _ le_rfl hWc)
          | Split.violated w hw =>
              Split.violated (Fin.cons 0 w) (by
                rw [qf_cons X hsym, hz]
                simpa using hw)
        else
          Split.violated _ (zeroPivot_witness X hsym hz hb)
      else
        match split k (schur X (X 0 0)) (schur_symm X hsym (X 0 0)) with
        | Split.psd m W hW =>
            Split.psd (m+1) (liftCert (fun i => X i 0) (X 0 0)⁻¹ W) (by
              obtain ⟨hWmat, hWc⟩ := (GramCert.check_spec W (schur X (X 0 0))).mp hW
              have ha : 0 < X 0 0 := by
                rcases lt_trichotomy (X 0 0) 0 with h | h | h
                · exact absurd h hneg
                · exact absurd h hz
                · exact h
              refine (GramCert.check_spec _ X).mpr ⟨?_, ?_⟩
              · ext i j
                refine Fin.cases ?_ ?_ i
                · refine Fin.cases ?_ ?_ j
                  · rw [liftCert_mat_00]
                    field_simp
                  · intro q
                    rw [liftCert_mat_0s, hsym q.succ 0]
                    field_simp
                · intro p
                  refine Fin.cases ?_ ?_ j
                  · rw [liftCert_mat_s0]
                    field_simp
                  · intro q
                    rw [liftCert_mat_ss, hWmat]
                    simp only [schur, tail, headRow, submatrix_apply, Matrix.sub_apply,
                      Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
                    rw [hsym p.succ 0, hsym q.succ 0]
                    field_simp
                    ring
              · exact liftCert_c_nonneg _ (inv_nonneg.mpr ha.le) hWc)
        | Split.violated y hy =>
            Split.violated (Fin.cons (-(headRow X ⬝ᵥ y) / (X 0 0)) y) (by
              rw [qf_schur X hsym rfl (by
                rcases lt_trichotomy (X 0 0) 0 with h | h | h
                · exact absurd h hneg
                · exact absurd h hz
                · exact ne_of_gt h)]
              exact hy)

/-- The split from a transpose hypothesis. -/
def splitOfTranspose (n : ℕ) (X : Matrix (Fin n) (Fin n) ℚ) (hs : Xᵀ = X) : Split n X :=
  split n X (fun i j => by
    have h := congrFun (congrFun hs i) j
    simpa [Matrix.transpose_apply] using h.symm)

/-- **The trichotomy, computably**: a symmetric rational matrix is either certified PSD or has an
explicit violated rational direction.  (This is `CertPSD.premise_iff_exists_cert` with the direction
of the dichotomy computed rather than chosen.) -/
theorem split_trichotomy (X : Matrix (Fin n) (Fin n) ℚ) (hs : Xᵀ = X) :
    (∃ (m : ℕ) (C : GramCert n m), C.check X = true) ∨ ∃ v : Fin n → ℚ, qf X v < 0 := by
  rcases splitOfTranspose n X hs with ⟨m, C, h⟩ | ⟨v, h⟩
  · exact Or.inl ⟨m, C, h⟩
  · exact Or.inr ⟨v, h⟩

/-- The certificate side of the split gives the infinite premise. -/
theorem Split.psd_premise {X : Matrix (Fin n) (Fin n) ℚ} {m : ℕ} {C : GramCert n m}
    (h : C.check X = true) : ∀ x : Fin n → ℚ, 0 ≤ qf X x :=
  premise_of_check C X h

/-- The violated side of the split gives a `GoodCut` with the exact violation as margin. -/
def Split.violated_cut {A : Matrix (Fin n) (Fin n) ℚ} {t : ℚ} {cX : Matrix (Fin n) (Fin n) ℚ}
    {v : Fin n → ℚ} (h : qf cX v < 0) : GoodCut A t cX :=
  psdCut (μ := -qf cX v) (by ring) (by linarith)

end Computable

/-! ## 5.6  The summed diagonal cut, and the oracle as a computation

The single-coordinate diagonal cut of §2.2 needs a *found* index `i`, which is not computable data.
The **summed** form is: take the diagonal matrix of signs `sᵢ = sign(1 - cXᵢᵢ)`; then for a
unit-diagonal `X`,

    ⟪diagonal s, X - cX⟫ = ∑ᵢ sᵢ (1 - cXᵢᵢ) = ∑ᵢ |cXᵢᵢ - 1| =: δ,

so the margin is the *sum* of the slacks — computed by a `decide`-free rational expression, and
strictly positive exactly when some diagonal entry is off.  With this, every branch of the oracle
is computable data and `sepOracle` below is a genuine `def`: the psd branch from `split`, the
diagonal branch from `diagSign`, the threshold branch from `A` itself. -/

/-- The sign of a rational, computed by comparisons only. -/
def signOf (q : ℚ) : ℚ := if 0 < q then 1 else if q < 0 then -1 else 0

theorem signOf_mul_self (q : ℚ) : signOf q * q = |q| := by
  unfold signOf
  split_ifs with h1 h2
  · rw [abs_of_pos h1]; ring
  · rw [abs_of_neg h2]; ring
  · have hq : q = 0 := le_antisymm (le_of_not_gt h1) (le_of_not_gt h2)
    rw [hq]; simp

/-- The sign vector of the diagonal slack `1 - cXᵢᵢ`. -/
def diagSign (cX : Matrix (Fin n) (Fin n) ℚ) : Fin n → ℚ := fun i => signOf (1 - cX i i)

/-- The Frobenius pairing with a diagonal matrix reads off the diagonal. -/
theorem frob_diagonal (s : Fin n → ℚ) (Y : Matrix (Fin n) (Fin n) ℚ) :
    frob (diagonal s) Y = ∑ i, s i * Y i i := by
  rw [frob]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Matrix.diagonal_apply_ne, Ne.symm hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **The summed diagonal cut is exact**: on the unit-diagonal slice the pairing with
`diagonal (diagSign cX)` is the total slack `∑ᵢ |cXᵢᵢ - 1|`. -/
theorem frob_diagSign {cX X : Matrix (Fin n) (Fin n) ℚ} (hX : unitDiag X) :
    frob (diagonal (diagSign cX)) (X - cX) = ∑ i, |cX i i - 1| := by
  rw [frob_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.sub_apply, hX i, diagSign]
  rw [signOf_mul_self, abs_sub_comm]

variable {A : Matrix (Fin n) (Fin n) ℚ} {t : ℚ} {cX : Matrix (Fin n) (Fin n) ℚ}

/-- **The summed diagonal cut.** -/
def diagCutSum (hpos : 0 < ∑ i, |cX i i - 1|) : GoodCut A t cX where
  normal := diagonal (diagSign cX)
  margin := ∑ i, |cX i i - 1|
  margin_pos := hpos
  separates := by
    intro X hX
    rw [frob_diagSign hX.unitDiag]
    have hnn : 0 ≤ ∑ i, |cX i i - 1| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    linarith

/-- **The computable separation oracle.**  All branches are decided by rational comparisons and
the exact pivot split; the `Response` carries the machine-checked obligations.  No `Classical.choice`
occurs in the computed data. -/
def sepOracle (A : Matrix (Fin n) (Fin n) ℚ) (t : ℚ) (cX : Matrix (Fin n) (Fin n) ℚ)
    (hs : cXᵀ = cX) : Response A t cX :=
  if hdiag : (∑ i, |cX i i - 1|) = 0 then
    if htr : t ≤ frob A cX then
      match splitOfTranspose n cX hs with
      | Split.psd m C hC =>
          Response.ok (premise_of_check C cX hC)
            (fun i => by
              have hsum := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
                abs_nonneg (cX j j - 1))
              have hterm : |cX i i - 1| = 0 := by
                by_contra hne
                have hpos : 0 < |cX i i - 1| := by
                  rw [abs_pos]
                  intro h0
                  exact hne (by simp [h0])
                have : 0 < ∑ j, |cX j j - 1| :=
                  Finset.sum_pos' (fun j _ => abs_nonneg _) ⟨i, Finset.mem_univ i, hpos⟩
                linarith
              have := abs_eq_zero.mp hterm
              linarith)
            htr
      | Split.violated v hv => Response.cut (psdCut (μ := -qf cX v) (by ring) (by linarith))
    else
      Response.cut (traceCut (by
        simp only [not_le] at htr
        exact htr))
  else
    Response.cut (diagCutSum (by
      have hnn : 0 ≤ ∑ i, |cX i i - 1| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
      exact lt_of_le_of_ne hnn (Ne.symm hdiag)))

/-- **The computable oracle is total, for free.** -/
theorem sepOracle_total (A : Matrix (Fin n) (Fin n) ℚ) (t : ℚ) (cX : Matrix (Fin n) (Fin n) ℚ)
    (hs : cXᵀ = cX) : Nonempty (Response A t cX) :=
  ⟨sepOracle A t cX hs⟩

/-- A computable tag for the split's verdict (used by `#eval` to display the computation). -/
def Split.tag {n : ℕ} {X : Matrix (Fin n) (Fin n) ℚ} : Split n X → String
  | Split.psd _ _ _ => "psd"
  | Split.violated _ _ => "violated"

/-- The split's violated direction, as a printable list. -/
def Split.witness {n : ℕ} {X : Matrix (Fin n) (Fin n) ℚ} : Split n X → List ℚ
  | Split.psd _ _ _ => []
  | Split.violated v _ => List.ofFn v

section Demos

/-- `1 2 / 2 1`: not PSD (leading pivot `1`, Schur complement `1 - 4 = -3`). -/
def bad2 : Matrix (Fin 2) (Fin 2) ℚ := !![1, 2; 2, 1]

/-- `0 1 / 1 0`: the zero-pivot case (the first row does not vanish). -/
def badZ : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]

/-- `1 0 / 0 1`: PSD, certified. -/
def good2 : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 1]

/-- A 3×3 whose tail is not PSD: exercises the recursion. -/
def bad3 : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; 0, 1, 2; 0, 2, 1]


end Demos

/-- **The consumer-facing verdict**: every oracle answer is either the finalization's `OkReport`
ledger or a cut with an exact positive margin.  This is the form the iterate loop and the
finalization branch on. -/
def Response.toReport {A : Matrix (Fin n) (Fin n) ℚ} {t : ℚ} {cX : Matrix (Fin n) (Fin n) ℚ}
    (r : Response A t cX) : OkReport n A t cX ⊕ GoodCut A t cX :=
  match r with
  | Response.ok hp hd ht => Sum.inl (okReport_of_ok ⟨hp, hd, ht⟩)
  | Response.cut G => Sum.inr G

/-- The computable oracle's verdict, in consumer form. -/
def sepOracle_toReport (A : Matrix (Fin n) (Fin n) ℚ) (t : ℚ)
    (cX : Matrix (Fin n) (Fin n) ℚ) (hs : cXᵀ = cX) :
    OkReport n A t cX ⊕ GoodCut A t cX :=
  (sepOracle A t cX hs).toReport


/-- **The diagonal contributes nothing on the unit-diagonal slice**: the pairing of a difference of
two unit-diagonal matrices sees only the off-diagonal entries.  This is the first half of the
coordinate reduction in §5 (remark 2); the reindexing onto `{Xᵢⱼ | i < j}` is bookkeeping for the
loop. -/
theorem frob_zero_diag_of_unitDiag {X Y : Matrix (Fin n) (Fin n) ℚ} (hX : unitDiag X)
    (hY : unitDiag Y) (C : Matrix (Fin n) (Fin n) ℚ) :
    frob C (X - Y) = ∑ i, ∑ j, if i = j then 0 else C i j * (X i j - Y i j) := by
  rw [frob]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i = j
  · subst h
    simp [hX i, hY i]
  · simp [Matrix.sub_apply, h]

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.SepOracle.qf_eq_frob
#print axioms QMCLeafB.SepOracle.frob_eq_trace
#print axioms QMCLeafB.SepOracle.psdCut_separates
#print axioms QMCLeafB.SepOracle.psdCut
#print axioms QMCLeafB.SepOracle.psdCut_normal_ne_zero
#print axioms QMCLeafB.SepOracle.diagCut_up_separates
#print axioms QMCLeafB.SepOracle.diagCut_down_separates
#print axioms QMCLeafB.SepOracle.traceCut_separates
#print axioms QMCLeafB.SepOracle.ok_or_cut
#print axioms QMCLeafB.SepOracle.response_total
#print axioms QMCLeafB.SepOracle.okReport_of_ok
#print axioms QMCLeafB.SepOracle.okReport_of_cert
#print axioms QMCLeafB.SepOracle.abs_qf_le_of_entrywise_le
#print axioms QMCLeafB.SepOracle.psd_of_cert_shifted
#print axioms QMCLeafB.SepOracle.psdMargin_of_shifted_cert
#print axioms QMCLeafB.SepOracle.okReport_of_shifted_cert
#print axioms QMCLeafB.SepOracle.qf_map
#print axioms QMCLeafB.SepOracle.frob_map
#print axioms QMCLeafB.SepOracle.psdCut_separates_R
#print axioms QMCLeafB.SepOracle.diagCut_up_separates_R
#print axioms QMCLeafB.SepOracle.traceCut_separates_R
#print axioms QMCLeafB.SepOracle.depth_scale_invariant
#print axioms QMCLeafB.SepOracle.qf_cons
#print axioms QMCLeafB.SepOracle.qf_schur
#print axioms QMCLeafB.SepOracle.zeroPivot_witness
#print axioms QMCLeafB.SepOracle.dotProduct_self_pos
#print axioms QMCLeafB.SepOracle.split
#print axioms QMCLeafB.SepOracle.split_trichotomy
#print axioms QMCLeafB.SepOracle.signOf_mul_self
#print axioms QMCLeafB.SepOracle.frob_diagSign
#print axioms QMCLeafB.SepOracle.diagCutSum
#print axioms QMCLeafB.SepOracle.sepOracle
#print axioms QMCLeafB.SepOracle.sepOracle_total
#print axioms QMCLeafB.SepOracle.sepOracle_toReport
#print axioms QMCLeafB.SepOracle.Response.toReport
#print axioms QMCLeafB.SepOracle.frob_zero_diag_of_unitDiag


