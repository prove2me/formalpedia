-- Prove2me | Definitions.Def_QMCLeafB_runparts_dilate_m5
-- name    : QMCLeafB_runparts_dilate_m5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:29:47.483716+00:00
-- url     : https://prove2.me/theorems/b8e27c9f-3a73-41ce-a6fe-20b28c6854cb
-- title:
--   QMCLeafB runparts_dilate_m5
-- statement:
--   # leaf B phase 14 — brick `runparts-dilate` (swarm `smw1a99tp`, member m5, direction d1, retry)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_runparts_m5
/-
# leaf B phase 14 — brick `runparts-dilate` (swarm `smw1a99tp`, member m5, direction d1, retry)

`Check_runparts_m5` reduced `RunParts o G t P` (for an arbitrary `RunParams G`) to eight
oracle-side hypotheses, the only analytic one being the **shallow-depth ledger**

    hdepth : (3·m_k/2)² ≤ ρ_k² · σ_k,     ρ_k ≤ rmax,     σ_k = c_k ⬝ p_k,  A_k p_k = c_k.

This file removes that hypothesis.  The mechanism (the design sketched in `Check_runparts_m5` §10):
`RelaxCut` is an *existential* over `(normal, margin)`, so a cut can be re-presented on a **dilated**
normal

    c'_k = c_k + λ_k · d,      margin = m_k (unchanged),

for any direction `d` in which the relaxed body lies *above* the query centre
(`0 ≤ d ⬝ (z − q_k)` for every `z` of the body): the dilated normal still separates the body at
margin `m_k`, while its squared norm `σ'_k = qf A_k (p_k + λ_k q_k)` grows **quadratically** in
`λ_k`:

    σ'_k = σ_k + λ_k·e_k + λ_k²·δ_k,   σ_k = c_k ⬝ p_k ≥ 0,   δ_k = d ⬝ q_k > 0,
    e_k = c_k ⬝ q_k + d ⬝ p_k.

So `σ'_k` exceeds any prescribed target as soon as `λ_k` does — and no square root, no
Cauchy–Schwarz and no estimate on the oracle's own margin is needed: the *explicit* rational
condition

    1 ≤ λ_k   and   |e_k| + |σ_k| + T_k + 1 ≤ λ_k · δ_k,     T_k := 9·m_k²/(4·rmax²),

already forces `T_k ≤ σ'_k`, hence the ledger (`depth_of_dilation`).  The program can compute
`σ_k, δ_k, e_k` from its own state (three rational numbers) and pick such a `λ_k`; that is the whole
residual of the depth ledger.

What is *proved* here:

* §1 the two algebraic facts: `A p = c` is determined by `c` when `A` is `PosQ` (`mulVec_inj_of_posQ`),
  and `(A p) ⬝ q = p ⬝ (A q)` for symmetric `A` (`dotProduct_mulVec_symm`);
* §2 `depth_of_dilation` — the quadratic growth and the ledger;
* §3 the engine's own iterate stream at the *recorded* (dilated) normals and the ceiling depth `rmax`
  (`runShape`, `runCut`, `runCut_wit`);
* §4 the centre-mismatch bookkeeping for the dilated cut: the dilated normal's drift is
  `θ_c + λ·θ_d ≤ m/2` whenever the oracle normal's drift is `≤ m/2` and the `d`-direction's drift is
  `≤ 0` (`dilated_drift`);
* §5 the assembly `runParts_of_dilated : RunParts o G t P` with **no** depth hypothesis.

The residual hypothesis list of §5 is the eight-item oracle interface of `Check_runparts_m5` with
item 7 (the depth ledger) replaced by:

* `hbody` — the body lies above the query centre in direction `d` (a fact about the relaxed body and
  the program's centre, dischargeable from the diagonal clause `|Xᵢᵢ − 1| ≤ dq/4` for
  `d = flat(diagonal ones)` whenever the centre's diagonal is `≤ 1 − dq/4`);
* `hdriftd` — `d ⬝ (Cat k − q_k) ≤ 0` (the engine's centre is not above the query centre in
  direction `d`);
* `hlam1`, `hlam2` — the explicit rational lower bound on the dilation parameter `λ_k` above.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace QMCLeafB.RunPartsDilate

open QuantumMaxCutEnergy

/-! ## 1.  Two algebraic facts about a `PosQ` shape -/

/-- **The witness is unique**: on a `PosQ` shape, `A p = c` determines `p`. -/
theorem mulVec_inj_of_posQ {N : ℕ} {A : Matrix (Fin N) (Fin N) ℚ}
    (h : QMCLeafB.EngineIterates.PosQ A) {x y : Fin N → ℚ} (hxy : A *ᵥ x = A *ᵥ y) : x = y := by
  have hz : A *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  by_contra hne
  have hzne : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < QMCLeafB.EngineIterates.qf A (x - y) := h.2 (x - y) hzne
  have hzero : QMCLeafB.EngineIterates.qf A (x - y) = 0 := by
    show (x - y) ⬝ᵥ (A *ᵥ (x - y)) = 0
    rw [hz, dotProduct_zero]
  rw [hzero] at hpos
  exact lt_irrefl _ hpos

/-- **The `A`-form is symmetric**: `(A p) ⬝ q = p ⬝ (A q)` for `Aᵀ = A`. -/
theorem dotProduct_mulVec_symm {N : ℕ} {A : Matrix (Fin N) (Fin N) ℚ} (hA : Aᵀ = A)
    (p q : Fin N → ℚ) : (A *ᵥ p) ⬝ᵥ q = p ⬝ᵥ (A *ᵥ q) := by
  rw [show p ⬝ᵥ (A *ᵥ q) = p ᵥ* A ⬝ᵥ q from Matrix.dotProduct_mulVec p A q,
    ← Matrix.mulVec_transpose, hA]

/-! ## 2.  The dilation makes the squared cut norm grow quadratically -/

/-- **The depth ledger from a dilated normal.**  If `c = A p`, `d = A q` with `d ≠ 0` and `A` `PosQ`,
then `σ(λ) = (c + λd) ⬝ (p + λq)` satisfies `T ≤ σ(λ)` as soon as `1 ≤ λ` and
`|e| + |σ| + T + 1 ≤ λ·δ`, where `σ = c ⬝ p`, `δ = d ⬝ q`, `e = c ⬝ q + d ⬝ p`.  No square root, no
Cauchy–Schwarz: only the exact expansion and `λ ≥ 1`. -/
theorem depth_of_dilation {N : ℕ} {A : Matrix (Fin N) (Fin N) ℚ}
    (hA : QMCLeafB.EngineIterates.PosQ A) {c d p q : Fin N → ℚ}
    (hp : A *ᵥ p = c) (hq : A *ᵥ q = d) (hd : d ≠ 0) {lam T : ℚ}
    (hT0 : 0 ≤ T) (hlam1 : 1 ≤ lam)
    (hlam2 : |(c ⬝ᵥ q) + (d ⬝ᵥ p)| + |c ⬝ᵥ p| + T + 1 ≤ lam * (d ⬝ᵥ q)) :
    T ≤ (c + lam • d) ⬝ᵥ (p + lam • q) := by
  have hδpos : 0 < d ⬝ᵥ q := by
    have hqne : q ≠ 0 := by
      intro h
      exact hd (by rw [← hq, h, Matrix.mulVec_zero])
    have hqpos : 0 < QMCLeafB.EngineIterates.qf A q := hA.2 q hqne
    have hq' : QMCLeafB.EngineIterates.qf A q = d ⬝ᵥ q := by
      show q ⬝ᵥ (A *ᵥ q) = d ⬝ᵥ q
      rw [hq, dotProduct_comm]
    simpa [hq'] using hqpos
  have hσ0 : 0 ≤ c ⬝ᵥ p := by
    have hp' : c ⬝ᵥ p = QMCLeafB.EngineIterates.qf A p := by
      rw [← hp, dotProduct_comm]
      rfl
    rw [hp']
    by_cases hp0 : p = 0
    · rw [hp0]
      simp [QMCLeafB.EngineIterates.qf]
    · exact (hA.2 p hp0).le
  have hexp : (c + lam • d) ⬝ᵥ (p + lam • q)
      = c ⬝ᵥ p + lam * ((c ⬝ᵥ q) + (d ⬝ᵥ p)) + lam * (lam * (d ⬝ᵥ q)) := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  rw [hexp]
  set e : ℚ := (c ⬝ᵥ q) + (d ⬝ᵥ p) with he
  have hlam0 : (0 : ℚ) ≤ lam := by linarith
  have hkey : lam * (lam * (d ⬝ᵥ q)) ≥ lam * |e| + (|c ⬝ᵥ p| + T + 1) := by
    have h1 : lam * (|e| + |c ⬝ᵥ p| + T + 1) ≤ lam * (lam * (d ⬝ᵥ q)) := by
      exact mul_le_mul_of_nonneg_left hlam2 hlam0
    have h2 : lam * |e| + (|c ⬝ᵥ p| + T + 1) ≤ lam * (|e| + |c ⬝ᵥ p| + T + 1) := by
      have h3 : (|c ⬝ᵥ p| + T + 1) ≤ lam * (|c ⬝ᵥ p| + T + 1) := by
        have h4 : (0 : ℚ) ≤ |c ⬝ᵥ p| + T + 1 := by positivity
        nlinarith
      nlinarith [h3]
    linarith
  have hlow : -(lam * |e|) ≤ lam * e := by
    have h5 : -|e| ≤ e := neg_abs_le e
    nlinarith [mul_le_mul_of_nonneg_left h5 hlam0]
  have hσle : -( |c ⬝ᵥ p|) ≤ c ⬝ᵥ p := neg_abs_le _
  linarith

/-! ## 3.  The engine's own iterate stream at an arbitrary `P` -/

/-- The initial shape of the run at `P` (`RunParts`' own `initShapeOf (2n² + 2dq²)`). -/
noncomputable def A0P (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) :
    Matrix (Fin (G.n * G.n)) (Fin (G.n * G.n)) ℚ :=
  QMCLeafB.Boundary.initShapeOf (G.n * G.n) (QMCLeafB.RundataArith.capOf G P.dq)

theorem A0P_posDef (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) :
    (QMCLeafB.EngineIterates.castM (A0P G P)).PosDef :=
  QMCLeafB.Boundary.initShapeOf_cast_posDef
    (QMCLeafB.RundataArith.capOf_pos G P.dq P.hdq)

/-- The engine's iterate chain at the normal stream `c` and the ceiling depth `P.rmax`. -/
noncomputable def runChain (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) :
    ℕ → { A : Matrix (Fin (G.n * G.n)) (Fin (G.n * G.n)) ℚ //
      (QMCLeafB.EngineIterates.castM A).PosDef } :=
  QMCLeafB.RunPartsShallow.shapeChain (N := G.n * G.n) (by
    have h := Nat.mul_le_mul hn hn
    omega) (A0P G P) (A0P_posDef G P) c hc (fun _ => P.rmax) (fun _ => P.hrmax)

/-- The shape at round `k`. -/
noncomputable def runShape (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    Matrix (Fin (G.n * G.n)) (Fin (G.n * G.n)) ℚ :=
  (runChain G P hn c hc k).1

theorem runShape_posQ (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    QMCLeafB.EngineIterates.PosQ (runShape G P hn c hc k) :=
  QMCLeafB.EngineIterates.posQ_of_cast (runChain G P hn c hc k).2

/-- The witness of the normal stream at round `k`. -/
noncomputable def runWit (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    Fin (G.n * G.n) → ℚ :=
  QMCLeafB.RunPartsShallow.witOf (runShape_posQ G P hn c hc k) (c k)

/-- The witness of the dilation direction at round `k`. -/
noncomputable def dirWit (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (d : Fin (G.n * G.n) → ℚ) (k : ℕ) :
    Fin (G.n * G.n) → ℚ :=
  QMCLeafB.RunPartsShallow.witOf (runShape_posQ G P hn c hc k) d

/-- The recorded cut stream: normals `c k`, chosen witnesses, ceiling depth. -/
noncomputable def runCut (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) :
    ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n) :=
  fun k => ⟨c k, runWit G P hn c hc k, P.rmax⟩

theorem runCut_wit (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) :
    ∀ k, QMCLeafB.EngineIterates.Aat (G.n * G.n) (A0P G P) (runCut G P hn c hc) k
        *ᵥ (runCut G P hn c hc k).p = (runCut G P hn c hc k).c := by
  have h := QMCLeafB.RunPartsShallow.hwit_cdStream (N := G.n * G.n) (by
    have hh := Nat.mul_le_mul hn hn
    omega) (A0P G P) (A0P_posDef G P) c hc (fun _ => P.rmax) (fun _ => P.hrmax)
  intro k
  exact h k

theorem runCut_c (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    (runCut G P hn c hc k).c = c k := rfl

theorem runCut_rho (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    (runCut G P hn c hc k).rho = P.rmax := rfl

/-- The witness relation, in the form `depth_of_dilation` consumes. -/
theorem runShape_mulVec_wit (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    runShape G P hn c hc k *ᵥ runWit G P hn c hc k = c k :=
  QMCLeafB.RunPartsShallow.witOf_spec (runShape_posQ G P hn c hc k) (c k)

theorem runShape_mulVec_dirWit (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (d : Fin (G.n * G.n) → ℚ) (k : ℕ) :
    runShape G P hn c hc k *ᵥ dirWit G P hn c hc d k = d :=
  QMCLeafB.RunPartsShallow.witOf_spec (runShape_posQ G P hn c hc k) d

/-! ## 4.  The dilated cut stream and its flat normal -/

theorem flatQ_add {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.RelaxOracle.flatQ (M + N) = QMCLeafB.RelaxOracle.flatQ M + QMCLeafB.RelaxOracle.flatQ N := by
  funext k
  simp [QMCLeafB.RelaxOracle.flatQ]

theorem flatQ_smul {n : ℕ} (c : ℚ) (M : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.RelaxOracle.flatQ (c • M) = c • QMCLeafB.RelaxOracle.flatQ M := by
  funext k
  simp [QMCLeafB.RelaxOracle.flatQ]

/-- **The dilated cut stream.**  Each of the oracle's cuts is re-presented on the normal
`normal + λ_k·dM` with its margin unchanged; `hbody` is the only geometric input (the relaxed body
lies above the query centre in direction `dM` with `β = 0`). -/
noncomputable def dilCut (G : Input) (t δ : ℚ) (ok : ℕ → Bool)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (dM : Matrix (Fin G.n) (Fin G.n) ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) δ)
    (lam : ℕ → ℚ) (hlam0 : ∀ k, 0 ≤ lam k)
    (hbody : ∀ k (hok : ok k = false), ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat
          (QMCLeafB.Finalization.wMatrixQ G)) (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ)
        ((δ : ℚ) : ℝ) X →
      -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat dM)
        (X - QMCLeafB.SepOracle.castMat (cX k))) :
    ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) δ :=
  fun k hok => QMCLeafB.RunPartsShallow.RelaxCut.dilate (C k hok) dM (lam k) 0 le_rfl
    (hlam0 k) (hbody k hok)

/-- The margin of the dilated cut is the oracle's margin. -/
theorem dilCut_margin (G : Input) (t δ : ℚ) (ok : ℕ → Bool)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (dM : Matrix (Fin G.n) (Fin G.n) ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) δ)
    (lam : ℕ → ℚ) (hlam0 : ∀ k, 0 ≤ lam k)
    (hbody : ∀ k (hok : ok k = false), ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat
          (QMCLeafB.Finalization.wMatrixQ G)) (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ)
        ((δ : ℚ) : ℝ) X →
      -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat dM)
        (X - QMCLeafB.SepOracle.castMat (cX k)))
    (k : ℕ) (hok : ok k = false) :
    (dilCut G t δ ok cX dM C lam hlam0 hbody k hok).margin = (C k hok).margin := by
  simp [dilCut, QMCLeafB.RunPartsShallow.RelaxCut.dilate]

/-- The flat normal of the dilated cut. -/
theorem dilCut_normal (G : Input) (t δ : ℚ) (ok : ℕ → Bool)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (dM : Matrix (Fin G.n) (Fin G.n) ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) δ)
    (lam : ℕ → ℚ) (hlam0 : ∀ k, 0 ≤ lam k)
    (hbody : ∀ k (hok : ok k = false), ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat
          (QMCLeafB.Finalization.wMatrixQ G)) (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ)
        ((δ : ℚ) : ℝ) X →
      -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat dM)
        (X - QMCLeafB.SepOracle.castMat (cX k)))
    (k : ℕ) (hok : ok k = false) :
    QMCLeafB.RelaxOracle.flatQ (dilCut G t δ ok cX dM C lam hlam0 hbody k hok).normal
      = QMCLeafB.RelaxOracle.flatQ (C k hok).normal
        + lam k • QMCLeafB.RelaxOracle.flatQ dM := by
  simp only [dilCut, QMCLeafB.RunPartsShallow.RelaxCut.dilate]
  rw [flatQ_add, flatQ_smul]

/-- The witness of an arbitrary vector at round `k` (same shape chain). -/
noncomputable def witAt (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0) (v : Fin (G.n * G.n) → ℚ) (k : ℕ) :
    Fin (G.n * G.n) → ℚ :=
  QMCLeafB.RunPartsShallow.witOf (runShape_posQ G P hn cn hcne k) v

theorem witAt_spec (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0) (v : Fin (G.n * G.n) → ℚ) (k : ℕ) :
    runShape G P hn cn hcne k *ᵥ witAt G P hn cn hcne v k = v :=
  QMCLeafB.RunPartsShallow.witOf_spec (runShape_posQ G P hn cn hcne k) v

theorem runCut_eq_witAt (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0) (k : ℕ) :
    (runCut G P hn cn hcne k).p = witAt G P hn cn hcne (cn k) k := rfl

theorem flatQ_eq_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ}
    (h : QMCLeafB.RelaxOracle.flatQ M = 0) : M = 0 := by
  ext i j
  have h1 := congrFun h (finProdFinEquiv (i, j))
  simpa [QMCLeafB.RelaxOracle.flatQ] using h1

/-! ## 5.  The assembly: `RunParts` with the depth ledger *proved* -/

/-- **`RunParts o G t P` from the oracle's verdicts, with no depth hypothesis.**  Compared with
`RunPartsShallow.runParts_shallow_of_oracle`, item 7 (the shallow-depth ledger) is gone: every cut of
the oracle is re-presented on the dilated normal `normal + λ_k·dM`, whose squared cut norm is made as
large as needed (`depth_of_dilation`), and the geometric side conditions of the dilation are

* `hbody`  — the relaxed body lies above the query centre in direction `dM`;
* `hdriftd` — `dM`'s centre mismatch is nonpositive;
* `hlam1`, `hlam2` — the explicit rational lower bound on `λ_k`.

The rest is the oracle interface of `runParts_of_relaxRun`. -/
noncomputable def runParts_of_dilated
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (hrmax : 0 < P.rmax)
    (hbud : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (dM : Matrix (Fin G.n) (Fin G.n) ℚ) (hdM : dM ≠ 0)
    (lam : ℕ → ℚ) (c : ℕ → Fin (G.n * G.n) → ℚ) (cn : ℕ → Fin (G.n * G.n) → ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < P.K * P.m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k (hok : ok k = false),
      cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ dM)
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hbody : ∀ k (hok : ok k = false), ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat
          (QMCLeafB.Finalization.wMatrixQ G)) (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ)
        ((P.dq : ℚ) : ℝ) X →
      -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat dM)
        (X - QMCLeafB.SepOracle.castMat (cX k)))
    (hdriftc : ∀ k (hok : ok k = false),
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (runCut G P hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k (hok : ok k = false),
      (fun i => ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (runCut G P hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0)
    (hlam1 : ∀ k (hok : ok k = false), 1 ≤ lam k)
    (hlam2 : ∀ k (hok : ok k = false),
      |(c k ⬝ᵥ witAt G P hn cn hcne (QMCLeafB.RelaxOracle.flatQ dM) k)
          + (QMCLeafB.RelaxOracle.flatQ dM ⬝ᵥ witAt G P hn cn hcne (c k) k)|
        + |c k ⬝ᵥ witAt G P hn cn hcne (c k) k|
        + 9 * (marg k) ^ 2 / (4 * (P.rmax) ^ 2) + 1
        ≤ lam k * (QMCLeafB.RelaxOracle.flatQ dM
            ⬝ᵥ witAt G P hn cn hcne (QMCLeafB.RelaxOracle.flatQ dM) k))
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)) :
    QMCLeafB.FinalStroke.RunParts o G t P := by
  classical
  have hN : 2 ≤ G.n * G.n := by
    have h := Nat.mul_le_mul hn hn
    omega
  -- the dilated cut stream
  have hbody' := hbody
  -- the recorded stream is `runCut` at `cn`
  refine QMCLeafB.RunPartsShallow.runParts_of_relaxRun o G t P hn hbud ok
    (runCut G P hn cn hcne) marg cX
    (dilCut G t P.dq ok cX dM C lam hlam0 hbody') ?_ hmem hCsym ?_ ?_ ?_ ?_ ?_ ?_ ?_ hverdict
  · -- `hmarg`
    intro k hok
    rw [dilCut_margin G t P.dq ok cX dM C lam hlam0 hbody' k hok]
    exact hmarg k hok
  · -- `hnorm`
    intro k hok
    rw [runCut_c G P hn cn hcne k, hcn k hok, hcEq k hok,
      dilCut_normal G t P.dq ok cX dM C lam hlam0 hbody' k hok]
  · -- `happr`: the dilated normal's centre mismatch
    intro k hok
    set a := QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
      (runCut G P hn cn hcne) k with ha
    set q := QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)) with hq
    have hsplit : QMCLeafB.EngineIterates.cutCR (runCut G P hn cn hcne) k
        = (fun i => ((c k i : ℚ) : ℝ))
          + (fun i => ((lam k : ℚ) : ℝ)
              * ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ)) := by
      funext i
      simp only [QMCLeafB.EngineIterates.cutCR, runCut_c, hcn k hok, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Rat.cast_add, Rat.cast_mul]
    have hmul : (fun i => ((lam k : ℚ) : ℝ)
        * ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ))
        ⬝ᵥ (a - q) = ((lam k : ℚ) : ℝ)
          * ((fun i => ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ)) ⬝ᵥ (a - q)) := by
      rw [show (fun i => ((lam k : ℚ) : ℝ) * ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ))
          = ((lam k : ℚ) : ℝ)
            • (fun i => ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ)) from rfl,
        smul_dotProduct, smul_eq_mul]
    have h1 : (fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ (a - q) ≤ ((marg k : ℚ) : ℝ) / 2 :=
      hdriftc k hok
    have h2 : (fun i => ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ)) ⬝ᵥ (a - q) ≤ 0 :=
      hdriftd k hok
    have h3 : (0 : ℝ) ≤ ((lam k : ℚ) : ℝ) := by exact_mod_cast hlam0 k
    have h4 : ((lam k : ℚ) : ℝ)
        * ((fun i => ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ)) ⬝ᵥ (a - q)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h3 h2
    rw [hsplit, add_dotProduct, hmul]
    have hmg : ((dilCut G t P.dq ok cX dM C lam hlam0 hbody' k hok).margin : ℚ) = marg k := by
      rw [dilCut_margin G t P.dq ok cX dM C lam hlam0 hbody' k hok]
      exact (hmarg k hok).symm
    rw [hmg]
    push_cast
    linarith
  · -- `hdepth`: the ledger, from the dilation
    intro k hok
    have hT0 : (0 : ℚ) ≤ 9 * (marg k) ^ 2 / (4 * (P.rmax) ^ 2) := by positivity
    have hstep := depth_of_dilation (runShape_posQ G P hn cn hcne k)
      (witAt_spec G P hn cn hcne (c k) k)
      (witAt_spec G P hn cn hcne (QMCLeafB.RelaxOracle.flatQ dM) k)
      (fun hzero => hdM (flatQ_eq_zero hzero))
      hT0 (hlam1 k hok) (hlam2 k hok)
    -- identify the recorded σ with the dilated one
    have hinj : witAt G P hn cn hcne (cn k) k
        = witAt G P hn cn hcne (c k) k
          + lam k • witAt G P hn cn hcne (QMCLeafB.RelaxOracle.flatQ dM) k := by
      refine QMCLeafB.RunPartsDilate.mulVec_inj_of_posQ (runShape_posQ G P hn cn hcne k) ?_
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, witAt_spec, witAt_spec, witAt_spec, hcn k hok]
    have hσ : QMCLeafB.EngineIterates.sigmaQ (runCut G P hn cn hcne k).c
        (runCut G P hn cn hcne k).p
        = (c k + lam k • QMCLeafB.RelaxOracle.flatQ dM)
          ⬝ᵥ (witAt G P hn cn hcne (c k) k
            + lam k • witAt G P hn cn hcne (QMCLeafB.RelaxOracle.flatQ dM) k) := by
      rw [runCut_c, runCut_eq_witAt]
      simp only [QMCLeafB.EngineIterates.sigmaQ]
      rw [hinj, hcn k hok]
    rw [hσ, runCut_rho]
    have hquad : (P.rmax) ^ 2 * (9 * (marg k) ^ 2 / (4 * (P.rmax) ^ 2))
        = (3 * marg k / 2) ^ 2 := by
      field_simp
      ring
    have hpos : (0 : ℚ) ≤ (P.rmax) ^ 2 := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hstep hpos
    rw [hquad] at hmul
    exact hmul
  · -- `hwit`
    exact runCut_wit G P hn cn hcne
  · -- `hρ0`
    intro k
    exact P.hrmax
  · -- `hρmax`
    intro k
    exact le_refl _
  · -- `hcne`
    exact hcne

/-! ## 6.  The shallow parameters: the previous headline with the depth ledger *proved* -/

/-- `0 < rmax` at the shallow parameters. -/
theorem runParamsShallow_rmax_pos (G : Input) (hn : 2 ≤ G.n) :
    0 < (QMCLeafB.RundataParams.runParamsShallow G hn).rmax :=
  QMCLeafB.RundataHalving.rmaxOf_pos (G.n * G.n) (by
    have h := Nat.mul_le_mul hn hn
    omega)

/-- **`RunParts` at the shallow parameters, depth ledger proved.**  This is
`RunPartsShallow.runParts_shallow_bracket` with its `hdepthR` hypothesis replaced by the three
geometric/dilation conditions of `runParts_of_dilated` (`hbody`, `hdriftd`, `hlam1`, `hlam2`); the
oracle's margin depth is no longer constrained at all. -/
noncomputable def runParts_shallow_dilated
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (dM : Matrix (Fin G.n) (Fin G.n) ℚ) (hdM : dM ≠ 0)
    (lam : ℕ → ℚ) (c : ℕ → Fin (G.n * G.n) → ℚ) (cn : ℕ → Fin (G.n * G.n) → ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < (QMCLeafB.RundataParams.runParamsShallow G hn).K
        * (QMCLeafB.RundataParams.runParamsShallow G hn).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k (hok : ok k = false),
      cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ dM)
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hbody : ∀ k (hok : ok k = false), ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat
          (QMCLeafB.Finalization.wMatrixQ G)) (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ)
        (((QMCLeafB.RundataParams.dqShallow G : ℚ)) : ℝ) X →
      -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat dM)
        (X - QMCLeafB.SepOracle.castMat (cX k)))
    (hdriftc : ∀ k (hok : ok k = false),
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (runCut G (QMCLeafB.RundataParams.runParamsShallow G hn) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k (hok : ok k = false),
      (fun i => ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (runCut G (QMCLeafB.RundataParams.runParamsShallow G hn) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0)
    (hlam1 : ∀ k (hok : ok k = false), 1 ≤ lam k)
    (hlam2 : ∀ k (hok : ok k = false),
      |(c k ⬝ᵥ witAt G (QMCLeafB.RundataParams.runParamsShallow G hn) hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ dM) k)
          + (QMCLeafB.RelaxOracle.flatQ dM ⬝ᵥ witAt G (QMCLeafB.RundataParams.runParamsShallow G hn)
              hn cn hcne (c k) k)|
        + |c k ⬝ᵥ witAt G (QMCLeafB.RundataParams.runParamsShallow G hn) hn cn hcne (c k) k|
        + 9 * (marg k) ^ 2
            / (4 * ((QMCLeafB.RundataParams.runParamsShallow G hn).rmax) ^ 2) + 1
        ≤ lam k * (QMCLeafB.RelaxOracle.flatQ dM
            ⬝ᵥ witAt G (QMCLeafB.RundataParams.runParamsShallow G hn) hn cn hcne
              (QMCLeafB.RelaxOracle.flatQ dM) k))
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((QMCLeafB.RundataParams.runParamsShallow G hn).K
        * (QMCLeafB.RundataParams.runParamsShallow G hn).m)) :
    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.RundataParams.runParamsShallow G hn) :=
  runParts_of_dilated o G t (QMCLeafB.RundataParams.runParamsShallow G hn) hn
    (runParamsShallow_rmax_pos G hn) (QMCLeafB.RunPartsShallow.runParamsShallow_budget G hn hRq)
    ok marg cX dM hdM lam c cn C hmarg hmem hCsym hcEq hcn hcne hlam0 hbody hdriftc hdriftd
    hlam1 hlam2 hverdict

#print axioms QMCLeafB.RunPartsDilate.runParamsShallow_rmax_pos
#print axioms QMCLeafB.RunPartsDilate.runParts_shallow_dilated

end QMCLeafB.RunPartsDilate


