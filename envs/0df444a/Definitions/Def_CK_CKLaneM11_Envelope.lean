-- Prove2me | Definitions.Def_CK_CKLaneM11_Envelope
-- name    : CK_CKLaneM11_Envelope
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T18:26:18.786535+00:00
-- url     : https://prove2.me/theorems/46e44c77-72c7-48da-8b5e-d1772b52091f
-- title:
--   Courtade–Kumar proof module `CKLaneM11.Envelope` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM11.Envelope` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM11.Envelope` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM11.Envelope (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM11/Envelope.lean)

import Definitions.Def_CK_CKLaneD_FleetBase

-- ===== source module CKLaneM11.Envelope =====
section

/-!
# Lane M11: archived method `global_parent_envelope` (parent envelope comparison)

Archive: `opposite/compact/OUTER_OPPOSITE.py` lines 56–62 (source sha256 a8ac3a0f…03a1) and
`PROOF.md` item 6: "The parent envelope `R_B ≤ eta(E + C(q))` in the psi-active branch. Feasible
children have `B ≥ 0`. Directed monotonicity bounds it above by `eta(E_lower + C(q_lower))`;
`j(a,b)` is bounded below by `j(a_upper, b_lower)`."  The archived acceptance test is
`j(a_hi, b_lo) - eta(E_lo + 1 - H((1 - q_lo)/2)) ≥ 0`, i.e. it certifies `gap ≤ cost`
(owner form, psi-active parent), not parent dominance.

Lean form proved here (branch-free, hence stronger):
`candidateGap psi a b e f ≤ P(H m - E) - P(C0 - E) ≤ P(H m - E) ≤ (1 - 2 xa) J(xa)
   ≤ (b_lo - a_hi) (J(a_hi) - J(b_lo)) / 2 ≤ interiorCost a b ≤ cost`,
where `P(H m - E) = eta(E + 1 - H m) = psi(m, E)` and `xa` is a certified lower bracket of the
entropy inverse at level `1 + E_lo - H_hi(m)`.

`checkEnvCell B c = true → Sem B` (the Lane D law-level statement `CKLaneD.Sem`) with no other
hypotheses.  Every numerical quantity is recomputed from the witness in exact `ℚ` arithmetic.
-/

namespace CKLaneM11

open GeneralCK CKLaneD

/-- Untrusted per-cell certificate data for the parent envelope comparison. -/
structure EnvCell where
  /-- log certificates at `alo` (lower bound of `H a`) -/
  pA0 : PtCert
  /-- log certificates at `ahi` (lower bound of `J a`) -/
  pA1 : PtCert
  /-- log certificates at `blo` (upper bound of `J b`) -/
  pB0 : PtCert
  /-- log certificates at `bhi` (lower bound of `H b`) -/
  pB1 : PtCert
  /-- log certificates at `mhi` (upper bound of `H m`); only used when `2 mhi < 1` -/
  pM : PtCert
  /-- lower bracket of the entropy inverse -/
  xa : ℚ
  pxa : PtCert
  deriving Repr, DecidableEq

/-! ## Derived quantities (all recomputed by the checker) -/

/-- Lower bound of `C0 = (H a + H b) / 2`. -/
def eC0Lo (B : Box) (c : EnvCell) : ℚ := (Hlo B.alo c.pA0 + Hlo B.bhi c.pB1) / 2
/-- Lower bound of the mean entropy `E`. -/
def eELo (B : Box) (c : EnvCell) : ℚ := EMIN + B.t0 * (eC0Lo B c - EMIN)
/-- Upper bound of `H m`, `m = (a + b) / 2`. -/
def eHmHi (B : Box) (c : EnvCell) : ℚ := if 2 * mhi B < 1 then Hhi (mhi B) c.pM else 1
/-- Upper bound of `eta(E + 1 - H m) = P(H m - E)`. -/
def eUB (c : EnvCell) : ℚ := (1 - 2 * c.xa) * Jhi c.xa c.pxa
/-- Lower bound of `J a - J b`. -/
def eJL (B : Box) (c : EnvCell) : ℚ := Jlo B.ahi c.pA1 - Jhi B.blo c.pB0
/-- Lower bound of `j(a, b) = interiorCost a b`. -/
def eJLo (B : Box) (c : EnvCell) : ℚ := (B.blo - B.ahi) * eJL B c / 2

/-- Point certificate at `mhi` (only needed when `mhi < 1/2`). -/
def mOK (B : Box) (c : EnvCell) : Bool := if 2 * mhi B < 1 then checkPt (mhi B) c.pM else true

/-- The Boolean cell checker: binds the box and every log/entropy/inverse enclosure. -/
def checkEnvCell (B : Box) (c : EnvCell) : Bool :=
  decide (0 < B.alo ∧ B.alo ≤ B.ahi ∧ 2 * B.ahi ≤ 1 ∧ 1 ≤ 2 * B.blo ∧ B.blo ≤ B.bhi ∧
    B.bhi < 1 ∧ 0 ≤ B.t0 ∧ B.t0 ≤ B.t1 ∧ B.t1 ≤ 1) &&
  checkPt B.alo c.pA0 &&
  checkPt B.ahi c.pA1 &&
  checkPt B.blo c.pB0 &&
  checkPt B.bhi c.pB1 &&
  mOK B c &&
  checkPt c.xa c.pxa &&
  decide (2 * c.xa ≤ 1) &&
  decide (Hhi c.xa c.pxa + eHmHi B c ≤ 1 + eELo B c) &&
  decide (0 ≤ eJL B c) &&
  decide (eUB c ≤ eJLo B c)

/-! ## Analytic lemmas -/

/-- `J` is antitone on `[1/2, 1)` (complement of `J_antitone`). -/
theorem J_anti_right {x y : ℝ} (hx : 1 / 2 ≤ x) (hxy : x ≤ y) (hy : y < 1) : J y ≤ J x := by
  have h := J_antitone (u := 1 - y) (v := 1 - x) (by linarith) (by linarith) (by linarith)
  have e1 := J_complement (1 - y)
  have e2 := J_complement (1 - x)
  rw [sub_sub_cancel] at e1 e2
  linarith

/-- The mean-edge cost is at least the edge cost of the means (log-sum / Jensen). -/
theorem law_cost_ge_interiorCost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) :
    interiorCost μ.a μ.b ≤ μ.cost := by
  have h := LogSum.cost_lower_bound μ
  have hV := LogSum.V_pos μ.a_interior μ.b_interior
  have hd1 := μ.e_le_cap
  have hd2 := μ.f_le_cap
  have hnn : 0 ≤ (μ.a - μ.b) ^ 2 / (4 * LogSum.V μ.a μ.b) * ((H μ.a - μ.e) + (H μ.b - μ.f)) :=
    mul_nonneg (div_nonneg (sq_nonneg _) (by linarith)) (by linarith)
  linarith

theorem mOK_sound {B : Box} {c : EnvCell} (h : mOK B c = true) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : m ≤ ((mhi B : ℚ) : ℝ)) : H m ≤ ((eHmHi B c : ℚ) : ℝ) := by
  unfold mOK at h
  unfold eHmHi
  split_ifs at h ⊢ with hlt
  · obtain ⟨_, _, _, hu, _, _⟩ := checkPt_bounds h
    have hlt' : 2 * ((mhi B : ℚ) : ℝ) < 1 := by exact_mod_cast hlt
    exact (H_mono_left hm0 hm (by linarith)).trans hu
  · push_cast
    exact H_le_one m

/-! ## Soundness -/

theorem checkEnvCell_sound {B : Box} {c : EnvCell} (h : checkEnvCell B c = true) : Sem B := by
  intro k μ hbox
  unfold checkEnvCell at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8, hB9, hpA0, hpA1, hpB0, hpB1, hM, hpxa,
    hxa2, hbr, hJL, hfin⟩ := h
  obtain ⟨ha0, ha1, hb0, hb1, hE0, hE1⟩ := hbox
  -- casts of box facts
  have rB1 : (0 : ℝ) < B.alo := by exact_mod_cast hB1
  have rB3 : 2 * (B.ahi : ℝ) ≤ 1 := by exact_mod_cast hB3
  have rB4 : 1 ≤ 2 * (B.blo : ℝ) := by exact_mod_cast hB4
  have rB6 : (B.bhi : ℝ) < 1 := by exact_mod_cast hB6
  have rB7 : (0 : ℝ) ≤ B.t0 := by exact_mod_cast hB7
  -- point enclosures
  obtain ⟨_, _, hA0l, _, _, _⟩ := checkPt_bounds hpA0
  obtain ⟨_, _, _, _, hA1Jl, _⟩ := checkPt_bounds hpA1
  obtain ⟨_, _, _, _, _, hB0Ju⟩ := checkPt_bounds hpB0
  obtain ⟨_, _, hB1l, _, _, _⟩ := checkPt_bounds hpB1
  obtain ⟨hxa0, _, _, hxaHu, _, hxaJu⟩ := checkPt_bounds hpxa
  -- entropy floor: E ≥ ELo
  have hHa_lo : H (B.alo : ℝ) ≤ H μ.a := H_mono_left rB1.le ha0 (by linarith only [ha1, rB3])
  have hHb_lo : H (B.bhi : ℝ) ≤ H μ.b :=
    H_anti_right (by linarith only [hb0, rB4]) hb1 (by linarith only [rB6])
  have hC0lo : (eC0Lo B c : ℝ) ≤ (H μ.a + H μ.b) / 2 := by
    have e : (eC0Lo B c : ℝ) = ((Hlo B.alo c.pA0 : ℝ) + (Hlo B.bhi c.pB1 : ℝ)) / 2 := by
      unfold eC0Lo; push_cast; try ring
    rw [e]; linarith only [hA0l, hB1l, hHa_lo, hHb_lo]
  have hElo : (eELo B c : ℝ) ≤ μ.meanEntropy := by
    have e : (eELo B c : ℝ) = (EMIN : ℝ) + (B.t0 : ℝ) * ((eC0Lo B c : ℝ) - EMIN) := by
      unfold eELo; push_cast; try ring
    have := mul_le_mul_of_nonneg_left
      (show (eC0Lo B c : ℝ) - EMIN ≤ (H μ.a + H μ.b) / 2 - EMIN by linarith only [hC0lo]) rB7
    rw [e]; linarith only [this, hE0]
  -- parent mean: H m ≤ HmHi
  have emhi : ((mhi B : ℚ) : ℝ) = ((B.ahi : ℝ) + (B.bhi : ℝ)) / 2 := by
    unfold mhi; push_cast; try ring
  have hmhi : (μ.a + μ.b) / 2 ≤ ((mhi B : ℚ) : ℝ) := by rw [emhi]; linarith only [ha1, hb1]
  have hm0 : 0 ≤ (μ.a + μ.b) / 2 := by linarith only [rB1, ha0, hb0, rB4]
  have hHm : H ((μ.a + μ.b) / 2) ≤ (eHmHi B c : ℝ) := mOK_sound hM hm0 hmhi
  -- information I = H m - E ∈ [0, 1)
  have hdef := law_deficit_mem μ
  have hdrop := μ.entropyDrop_nonneg
  unfold InteriorLaw.entropyDrop InteriorLaw.midpoint at hdrop
  have hI0 : 0 ≤ H ((μ.a + μ.b) / 2) - μ.meanEntropy := by linarith only [hdrop, hdef.1]
  have hEpos := law_meanEntropy_pos μ
  have hI1 : H ((μ.a + μ.b) / 2) - μ.meanEntropy < 1 := by
    linarith only [H_le_one ((μ.a + μ.b) / 2), hEpos]
  -- entropy-inverse bracket: P(I) ≤ (1 - 2 xa) J xa ≤ UB
  have rxa2 : 2 * (c.xa : ℝ) ≤ 1 := by exact_mod_cast hxa2
  have rbr : (Hhi c.xa c.pxa : ℝ) + (eHmHi B c : ℝ) ≤ 1 + (eELo B c : ℝ) := by
    exact_mod_cast hbr
  have hxa0' : (0 : ℝ) < c.xa := by exact_mod_cast hxa0
  have hHxa : H (c.xa : ℝ) ≤ 1 - (H ((μ.a + μ.b) / 2) - μ.meanEntropy) := by
    linarith only [hxaHu, rbr, hHm, hElo]
  have hP := P_le_bracket hI0 hI1 hxa0' (by linarith only [rxa2]) hHxa
  have hPU : Scalar.P (H ((μ.a + μ.b) / 2) - μ.meanEntropy) ≤ (eUB c : ℝ) := by
    have e : (eUB c : ℝ) = (1 - 2 * (c.xa : ℝ)) * (Jhi c.xa c.pxa : ℝ) := by
      unfold eUB; push_cast; try ring
    have := mul_le_mul_of_nonneg_left hxaJu
      (by linarith only [rxa2] : (0 : ℝ) ≤ 1 - 2 * (c.xa : ℝ))
    rw [e]; linarith only [hP, this]
  -- Jensen split with nonnegative children: candidateGap psi ≤ P(I)
  have hjen := law_gap_le_P μ
  have hPs := P_nonneg hdef.1 hdef.2
  -- edge cost of the means: j(a,b) ≥ (blo - ahi) (J ahi - J blo) / 2
  have hJa : (Jlo B.ahi c.pA1 : ℝ) ≤ J μ.a :=
    hA1Jl.trans (J_antitone (rB1.trans_le ha0) (by linarith only [rB3]) ha1)
  have hJb : J μ.b ≤ (Jhi B.blo c.pB0 : ℝ) :=
    (J_anti_right (by linarith only [rB4]) hb0 μ.b_interior.2).trans hB0Ju
  have rJL : (0 : ℝ) ≤ (eJL B c : ℝ) := by exact_mod_cast hJL
  have eJL' : (eJL B c : ℝ) = (Jlo B.ahi c.pA1 : ℝ) - (Jhi B.blo c.pB0 : ℝ) := by
    unfold eJL; push_cast; try ring
  have hd : (B.blo : ℝ) - B.ahi ≤ μ.b - μ.a := by linarith only [ha1, hb0]
  have hd0 : (0 : ℝ) ≤ (B.blo : ℝ) - B.ahi := by linarith only [rB3, rB4]
  have hJd : (eJL B c : ℝ) ≤ J μ.a - J μ.b := by rw [eJL']; linarith only [hJa, hJb]
  have hprod : ((B.blo : ℝ) - B.ahi) * (eJL B c : ℝ) ≤ (μ.b - μ.a) * (J μ.a - J μ.b) :=
    mul_le_mul hd hJd rJL (hd0.trans hd)
  have hj : (eJLo B c : ℝ) ≤ interiorCost μ.a μ.b := by
    have e : (eJLo B c : ℝ) = ((B.blo : ℝ) - B.ahi) * (eJL B c : ℝ) / 2 := by
      unfold eJLo; push_cast; try ring
    rw [e]; unfold interiorCost; linarith only [hprod]
  have hcost := law_cost_ge_interiorCost μ
  have rfin : (eUB c : ℝ) ≤ (eJLo B c : ℝ) := by exact_mod_cast hfin
  linarith only [hjen, hPs, hPU, rfin, hj, hcost]

/-! ## Certificate trees, witnesses, archived-leaf binding -/

/-- A certificate tree: a single cell or a binary split of the box along `a`, `b` or `t`. -/
inductive EnvCert where
  | cell (c : EnvCell)
  | splitA (m : ℚ) (l r : EnvCert)
  | splitB (m : ℚ) (l r : EnvCert)
  | splitT (m : ℚ) (l r : EnvCert)
  deriving Repr

def checkEnvTree : Box → EnvCert → Bool
  | B, .cell c => checkEnvCell B c
  | B, .splitA m l r =>
      decide (B.alo ≤ m ∧ m ≤ B.ahi) && checkEnvTree { B with ahi := m } l &&
        checkEnvTree { B with alo := m } r
  | B, .splitB m l r =>
      decide (B.blo ≤ m ∧ m ≤ B.bhi) && checkEnvTree { B with bhi := m } l &&
        checkEnvTree { B with blo := m } r
  | B, .splitT m l r =>
      decide (B.t0 ≤ m ∧ m ≤ B.t1) && checkEnvTree { B with t1 := m } l &&
        checkEnvTree { B with t0 := m } r

theorem checkEnvTree_sound : ∀ (B : Box) (t : EnvCert), checkEnvTree B t = true → Sem B
  | B, .cell c, h => checkEnvCell_sound h
  | B, .splitA m l r, h => by
      simp only [checkEnvTree, Bool.and_eq_true] at h
      exact sem_splitA (checkEnvTree_sound _ l h.1.2) (checkEnvTree_sound _ r h.2)
  | B, .splitB m l r, h => by
      simp only [checkEnvTree, Bool.and_eq_true] at h
      exact sem_splitB (checkEnvTree_sound _ l h.1.2) (checkEnvTree_sound _ r h.2)
  | B, .splitT m l r, h => by
      simp only [checkEnvTree, Bool.and_eq_true] at h
      exact sem_splitT (checkEnvTree_sound _ l h.1.2) (checkEnvTree_sound _ r h.2)

/-- A parent-envelope witness: the exact box together with its certificate tree. -/
structure EnvWitness where
  box : Box
  cert : EnvCert
  deriving Repr

/-- The Boolean parent-envelope checker. -/
def checkEnv (w : EnvWitness) : Bool := checkEnvTree w.box w.cert

/-- Unconditional semantic soundness of the parent-envelope checker. -/
theorem env_check_sound (w : EnvWitness) (hw : checkEnv w = true) : Sem w.box :=
  checkEnvTree_sound w.box w.cert hw

/-- Per-leaf acceptance: certificate valid and bound to the archived `(u,v,t)` path. -/
def checkEnvLeaf (p : List ℕ) (w : EnvWitness) : Bool :=
  imageCheck (uvtBox p) w.box && checkEnv w

theorem checkEnvLeaf_sound {p : List ℕ} {w : EnvWitness} (h : checkEnvLeaf p w = true) :
    SemUVT (uvtBox p) := by
  unfold checkEnvLeaf at h
  rw [Bool.and_eq_true] at h
  exact imageCheck_sound h.1 (env_check_sound w h.2)

theorem checkEnvLeaves_sound (L : List (List ℕ × EnvWitness))
    (h : (L.all fun x => checkEnvLeaf x.1 x.2) = true) :
    ∀ x ∈ L, SemUVT (uvtBox x.1) := by
  intro x hx
  rw [List.all_eq_true] at h
  exact checkEnvLeaf_sound (h x hx)

/-- Owner form on an archived leaf: when psi is (weakly) active at the parent, `gap ≤ cost`. -/
theorem semUVT_gap_le_cost {U : UVT} (hU : SemUVT U) {k : ℕ} (μ : InteriorLaw (Fin k))
    (hin : InUVT U μ.a μ.b μ.meanEntropy)
    (hact : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  (hybrid_gap_le_psi hact).trans (hU k μ hin)

end CKLaneM11

end


