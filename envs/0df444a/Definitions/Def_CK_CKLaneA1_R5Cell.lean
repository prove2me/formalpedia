-- Prove2me | Definitions.Def_CK_CKLaneA1_R5Cell
-- name    : CK_CKLaneA1_R5Cell
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T13:00:58.698719+00:00
-- url     : https://prove2.me/theorems/8cadffda-61da-488f-afa0-16081943a3a6
-- title:
--   Courtade–Kumar proof module `CKLaneA1.R5Cell` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.R5Cell` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.R5Cell` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.R5Cell (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/R5Cell.lean)

import Definitions.Def_CK_CKLaneA1_R5PsiMono

-- ===== source module CKLaneA1.R5Cell =====
section

/-!
# CKLaneA1.R5Cell — the `(t, A)` cell checker of CE-stat row 5 and its soundness

A strip `[t1, t2] = [N1, N2]/2^40` of contacts and a chain of `A`-cells `[A1, A2]` (data scale `2^-48`)
from `A0` up to `4`.  Cell kinds (all bound `D(A, W, λ) = Θ(A) + Θ(W) − Θ(A + 2λW)` from below):
* `N` (kind 0, `A`-normalized): Case-E exclusion `λ < (1+κA)/2`, `W₂ = (1+κA)W`, and
  `D > Θ(A) − [Θ(A+W₂) − Θ(W₂)] − [Θ(W₂) − Θ(W)] ≥ A · value`;
* `G` (kind 1, direct): `D ≥ Slo(A1) + Slo(t2) − Shi(A2 + 2λ̄W_hi)`;
* `W` (kind 2, `W`-normalized): `D ≥ W · (Θ(W_t)/W_t − 2λ̄ · Θ'max)`.
`cover_sound`: a checked, chained strip list rules out every chart point with
`t ∈ [⌊2^40/100⌋/2^40, 1/2)`, `A < 4` and `t < 11/32 + 2A`.
-/

set_option autoImplicit false

namespace CKLaneA1.R5

open GeneralCK GeneralCK.Certificates.Mixed CKLaneP Set

/-! ## Data and checker -/

/-- Cell data scale: `dq n = n / 2^48`. -/
def dq (n : ℕ) : ℚ := (n : ℚ) / 281474976710656

/-- A cell `[A1, A2]` (`A1` = previous `A2`). -/
structure Cell where
  kind : ℕ
  A2n : ℕ
  ex : ℕ
  kapn : ℕ
  sig : List ℕ
  th : List ℕ
  br : List (ℕ × ℕ)
  Wtn : ℕ
  kq : ℕ

/-- A strip of contacts `[N1, N2]/2^40` with its cells from `A0 = dq A0n`. -/
structure Strip where
  N1 : ℕ
  N2 : ℕ
  A0n : ℕ
  cells : List Cell

/-- Strip context. -/
structure Ctx where
  t1 : ℚ
  t2 : ℚ
  Hl : ℚ
  Hh : ℚ
  Wlo : ℚ
  Whi : ℚ
  S2 : ℚ

def mkCtx (N1 N2 : ℕ) : Ctx :=
  ⟨dyq N1, dyq N2, (vd N1).Hlo, (vd N2).Hhi, (1 - 2 * dyq N2) / (2 * (vd N2).Hhi),
    (1 - 2 * dyq N1) / (2 * (vd N1).Hlo), (vd N2).Slo⟩

/-- Riemann points: `σ_i ≤ t1 − umax (1 − i/m)`. -/
def sigOK (t1 umax : ℚ) (m : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | i, N :: rest => okN N && decide (dyq N ≤ t1 - umax * (1 - (i : ℚ) / m)) &&
      sigOK t1 umax m (i + 1) rest

def jSum : List ℕ → ℚ
  | [] => 0
  | N :: rest => (vd N).Jhi + jSum rest

def umaxOf (c : Ctx) (A1 A2 kap : ℚ) : ℚ := 2 * A2 * c.Hh / (1 + kap * A1)

def exclRiem (c : Ctx) (A1 A2 kap : ℚ) (sig : List ℕ) : Bool :=
  decide (0 < sig.length) && sigOK c.t1 (umaxOf c A1 A2 kap) sig.length 0 sig &&
    decide (jSum sig ≤ sig.length * kap)

def exclDir (c : Ctx) (A1 A2 kap : ℚ) (sig : List ℕ) : Bool :=
  decide (sig.length = 1) && decide (0 < A1) && okN (sig.headD 0) &&
    decide (dyq (sig.headD 0) ≤ c.t1 - umaxOf c A1 A2 kap) &&
    decide (c.Hh - (vd (sig.headD 0)).Hlo ≤ kap * (2 * A1 * c.Hl / (1 + kap * A2)))

/-- Case-E exclusion data `κ` for the cell `[A1, A2]`: Riemann (`ex = 1`) or direct (`ex = 2`). -/
def exclOK (c : Ctx) (A1 A2 : ℚ) (ex : ℕ) (kap : ℚ) (sig : List ℕ) : Bool :=
  decide (0 < kap) && decide (0 < c.t1 - umaxOf c A1 A2 kap) &&
    (if ex = 1 then exclRiem c A1 A2 kap sig else if ex = 2 then exclDir c A1 A2 kap sig else false)

/-- Upper bound `λ̄` for `λ` on the cell. -/
def lamBar (c : Ctx) (A1 A2 : ℚ) (ex : ℕ) (kap : ℚ) (sig : List ℕ) : ℚ :=
  if ex ≠ 0 ∧ exclOK c A1 A2 ex kap sig = true then min 1 ((1 + kap * A2) / 2) else 1

def fam1OK (W2lo W2hi A1 A2 : ℚ) (kq : ℕ) : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | i, p :: rest => brOK (W2lo + i * A1 / kq) (W2hi + (i + 1) * A2 / kq) p.1 p.2 &&
      fam1OK W2lo W2hi A1 A2 kq (i + 1) rest

def fam2OK (Wlo Whi kA1 kA2 : ℚ) (k : ℕ) : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | j, p :: rest => brOK (Wlo * (1 + j * kA1 / k)) (Whi * (1 + (j + 1) * kA2 / k)) p.1 p.2 &&
      fam2OK Wlo Whi kA1 kA2 k (j + 1) rest

def brSum : List (ℕ × ℕ) → ℚ
  | [] => 0
  | p :: rest => brB p.1 p.2 + brSum rest

/-- Kind `N` (A-normalized). -/
def nOK (c : Ctx) (A1 : ℚ) (cl : Cell) : Bool :=
  decide (A1 < dq cl.A2n) && decide (0 ≤ A1) && decide (c.t2 < 1 / 2) && decide (cl.ex ≠ 0) &&
    exclOK c A1 (dq cl.A2n) cl.ex (dq cl.kapn) cl.sig && thLoOK (dq cl.A2n) (cl.th.headD 0) &&
    decide (1 ≤ cl.kq) && decide (cl.kq + 1 ≤ cl.br.length) &&
    fam1OK ((1 + dq cl.kapn * A1) * c.Wlo) ((1 + dq cl.kapn * dq cl.A2n) * c.Whi) A1 (dq cl.A2n)
      cl.kq 0 (cl.br.take cl.kq) &&
    fam2OK c.Wlo c.Whi (dq cl.kapn * A1) (dq cl.kapn * dq cl.A2n) (cl.br.length - cl.kq) 0
      (cl.br.drop cl.kq) &&
    decide (0 < (vd (cl.th.headD 0)).Slo / dq cl.A2n - brSum (cl.br.take cl.kq) / cl.kq -
      dq cl.kapn * c.Whi * brSum (cl.br.drop cl.kq) / ((cl.br.length - cl.kq : ℕ) : ℚ))

/-- Kind `G` (direct). -/
def gOK (c : Ctx) (A1 : ℚ) (cl : Cell) : Bool :=
  decide (A1 < dq cl.A2n) && decide (0 < A1) && decide (c.t2 < 1 / 2) &&
    thLoOK A1 (cl.th.getD 0 0) &&
    thHiOK (dq cl.A2n + 2 * lamBar c A1 (dq cl.A2n) cl.ex (dq cl.kapn) cl.sig * c.Whi)
      (cl.th.getD 1 0) &&
    decide (0 < (vd (cl.th.getD 0 0)).Slo + c.S2 - (vd (cl.th.getD 1 0)).Shi)

/-- Kind `W` (W-normalized). -/
def wOK (c : Ctx) (A1 : ℚ) (cl : Cell) : Bool :=
  decide (A1 < dq cl.A2n) && decide (0 < A1) && decide (c.Whi ≤ dq cl.Wtn) &&
    thLoOK (dq cl.Wtn) (cl.th.headD 0) &&
    brOK A1 (dq cl.A2n + 2 * lamBar c A1 (dq cl.A2n) cl.ex (dq cl.kapn) cl.sig * c.Whi)
      (cl.br.headD (0, 0)).1 (cl.br.headD (0, 0)).2 &&
    decide (0 < (vd (cl.th.headD 0)).Slo / dq cl.Wtn -
      2 * lamBar c A1 (dq cl.A2n) cl.ex (dq cl.kapn) cl.sig *
        brB (cl.br.headD (0, 0)).1 (cl.br.headD (0, 0)).2)

def cellOK (c : Ctx) (A1 : ℚ) (cl : Cell) : Bool :=
  if cl.kind = 0 then nOK c A1 cl else if cl.kind = 1 then gOK c A1 cl
  else if cl.kind = 2 then wOK c A1 cl else false

def cellsOK (c : Ctx) : ℚ → List Cell → Bool
  | A1, [] => decide (4 ≤ A1)
  | A1, cl :: rest => cellOK c A1 cl && cellsOK c (dq cl.A2n) rest

def stripOK (s : Strip) : Bool :=
  okN s.N1 && okN s.N2 && decide (s.N1 < s.N2) && decide (0 < (vd s.N1).Hlo) &&
    decide (dq s.A0n = 0 ∨ 2 * dq s.A0n + 11 / 32 ≤ dyq s.N1) &&
    cellsOK (mkCtx s.N1 s.N2) (dq s.A0n) s.cells

/-- `⌊2^40/100⌋`. -/
def T0N : ℕ := 10995116277
/-- `2^39` (`t = 1/2`). -/
def THN : ℕ := 549755813888

def chainOK : ℕ → List Strip → Bool
  | n, [] => n == THN
  | n, s :: rest => (n == s.N1) && chainOK s.N2 rest

/-! ## Soundness: point facts and the strip context -/

/-- Facts about a row-5 chart point used by the cell checker. -/
structure PtFacts (a t A W lam : ℝ) : Prop where
  ha : 0 < a
  hat : a < t
  ht2 : t < 1 / 2
  hA : 0 < A
  hlam0 : 0 < lam
  hlam1 : lam < 1
  hW : W = Xf t
  hL : Lf a = (1 - lam) / (A + lam * W)
  hcase : lam * (t - a) < A * H t

theorem PtFacts.t0 {a t A W lam : ℝ} (P : PtFacts a t A W lam) : 0 < t := P.ha.trans P.hat

theorem PtFacts.Ht0 {a t A W lam : ℝ} (P : PtFacts a t A W lam) : 0 < H t :=
  H_pos P.t0 (by linarith [P.ht2])

theorem PtFacts.W0 {a t A W lam : ℝ} (P : PtFacts a t A W lam) : 0 < W := by
  rw [P.hW]; unfold Xf
  exact div_pos (by linarith [P.ht2]) (by linarith [P.Ht0])

theorem PtFacts.HW {a t A W lam : ℝ} (P : PtFacts a t A W lam) : H t * W = (1 - 2 * t) / 2 := by
  rw [P.hW]; unfold Xf
  rw [mul_div_assoc', mul_comm (H t) (1 - 2 * t), mul_div_mul_right _ _ P.Ht0.ne']

/-- Facts about the strip context at the point. -/
structure CtxOK (c : Ctx) (t W : ℝ) : Prop where
  ht1 : (c.t1 : ℝ) ≤ t
  hHl : (c.Hl : ℝ) ≤ H t
  hHh : H t ≤ (c.Hh : ℝ)
  hHl0 : (0 : ℝ) < c.Hl
  hWlo : (c.Wlo : ℝ) ≤ W
  hWhi : W ≤ (c.Whi : ℝ)
  hS2 : c.t2 < 1 / 2 → ((c.S2 : ℚ) : ℝ) ≤ e8Theta W

open ZeroCapLeftStationaryThetaBracket in
/-- `Θ(W) ≥ Slo(t2)` for `W = X(t)`, `t ≤ t2 < 1/2`. -/
theorem theta_W_ge {N2 : ℕ} (h2 : okN N2 = true) (hv : dyq N2 < 1 / 2) {t : ℝ} (ht0 : 0 < t)
    (ht2 : t ≤ ((dyq N2 : ℚ) : ℝ)) : (((vd N2).Slo : ℚ) : ℝ) ≤ e8Theta (Xf t) := by
  have d2 := vd_sound h2
  have hv0 : (0 : ℝ) < ((dyq N2 : ℚ) : ℝ) := dyq_pos h2
  have hvh : ((dyq N2 : ℚ) : ℝ) < 1 / 2 := VD.cast_lt_half hv
  have hth : t < 1 / 2 := ht2.trans_lt hvh
  have hHt : 0 < H t := H_pos ht0 (by linarith)
  have hX : 0 < Xf t := by unfold Xf; exact div_pos (by linarith) (by linarith)
  have hXH : Xf t * H t = (1 - 2 * t) / 2 := by
    unfold Xf; rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hHt.ne']
  have hres : 1 - 2 * ((dyq N2 : ℚ) : ℝ) ≤ 2 * Xf t * H ((dyq N2 : ℚ) : ℝ) := by
    have hm := H_mono ht0.le ht2 hvh.le
    have := mul_le_mul_of_nonneg_left hm hX.le
    linarith
  have hcont := contact_upper_of_entropy_lower hX hv0.le hvh.le le_rfl hres
  have hs := e8Theta_lower_of_contact_upper hX hv0 hvh hcont
  have hS := VD.Slo_le d2
  rw [vd_v] at hS
  exact hS.trans hs

theorem ctx_sound {N1 N2 : ℕ} (h1 : okN N1 = true) (h2 : okN N2 = true) (hHl : 0 < (vd N1).Hlo)
    {a t A W lam : ℝ} (P : PtFacts a t A W lam) (ht1 : ((dyq N1 : ℚ) : ℝ) ≤ t)
    (ht2 : t ≤ ((dyq N2 : ℚ) : ℝ)) : CtxOK (mkCtx N1 N2) t W := by
  have d1 := vd_sound h1
  have d2 := vd_sound h2
  have ht0 := P.t0
  have hth := P.ht2
  have hq1 : (0 : ℝ) ≤ ((dyq N1 : ℚ) : ℝ) := (dyq_pos h1).le
  have hq2 : ((dyq N2 : ℚ) : ℝ) ≤ 1 / 2 := dyq_le_half h2
  have hHlo : (((vd N1).Hlo : ℚ) : ℝ) ≤ H t := by
    have := VD.Hlo_le d1
    rw [vd_v] at this
    exact this.trans (H_mono hq1 ht1 hth.le)
  have hHhi : H t ≤ (((vd N2).Hhi : ℚ) : ℝ) := by
    have := VD.le_Hhi d2
    rw [vd_v] at this
    exact (H_mono ht0.le ht2 hq2).trans this
  have hHl0 : (0 : ℝ) < (((vd N1).Hlo : ℚ) : ℝ) := by exact_mod_cast hHl
  have hHt : 0 < H t := hHl0.trans_le hHlo
  refine ⟨ht1, hHlo, hHhi, hHl0, ?_, ?_, ?_⟩
  · show ((((1 - 2 * dyq N2) / (2 * (vd N2).Hhi)) : ℚ) : ℝ) ≤ W
    rw [P.hW]
    push_cast
    unfold Xf
    exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
  · show W ≤ ((((1 - 2 * dyq N1) / (2 * (vd N1).Hlo)) : ℚ) : ℝ)
    rw [P.hW]
    push_cast
    unfold Xf
    exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
  · intro hv
    show (((vd N2).Slo : ℚ) : ℝ) ≤ e8Theta W
    rw [P.hW]
    exact theta_W_ge h2 hv ht0 ht2

/-! ## Soundness: the exclusion -/

/-- Riemann points `L j = t − u(1 − j/m)`. -/
noncomputable def Lp (t u : ℝ) (m j : ℕ) : ℝ := t - u * (1 - (j : ℝ) / m)

theorem sig_riemann {t1 umax : ℚ} {m : ℕ} {t u : ℝ} (hm : 0 < m) (ht1 : (t1 : ℝ) ≤ t)
    (hth : t < 1 / 2) (hu0 : 0 ≤ u) (humax : u ≤ (umax : ℝ)) :
    ∀ (l : List ℕ) (i : ℕ), sigOK t1 umax m i l = true → i + l.length ≤ m →
      H (Lp t u m (i + l.length)) - H (Lp t u m i) ≤ u / m * ((jSum l : ℚ) : ℝ)
  | [], i, _, _ => by simp [jSum]
  | N :: rest, i, h, hlen => by
    simp only [sigOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hN, hle⟩, hrest⟩ := h
    have hlen' : (i + 1) + rest.length ≤ m := by simp only [List.length_cons] at hlen; omega
    have ih := sig_riemann hm ht1 hth hu0 humax rest (i + 1) hrest hlen'
    have e : i + (N :: rest).length = (i + 1) + rest.length := by
      simp only [List.length_cons]; omega
    rw [e]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have him : (i : ℝ) + 1 ≤ m := by exact_mod_cast (show i + 1 ≤ m by omega)
    have hσ0 : (0 : ℝ) < ((dyq N : ℚ) : ℝ) := dyq_pos hN
    have hfac : 0 ≤ 1 - (i : ℝ) / m := by
      rw [sub_nonneg, div_le_one hmR]; linarith
    have hfac1 : 0 ≤ 1 - ((i + 1 : ℕ) : ℝ) / m := by
      rw [sub_nonneg, div_le_one hmR]; push_cast; linarith
    have hleR : ((dyq N : ℚ) : ℝ) ≤ (t1 : ℝ) - (umax : ℝ) * (1 - (i : ℝ) / m) := by
      have h' := (Rat.cast_le (K := ℝ)).mpr hle
      push_cast at h'
      linarith
    have hσL : ((dyq N : ℚ) : ℝ) ≤ Lp t u m i := by
      unfold Lp
      have : u * (1 - (i : ℝ) / m) ≤ (umax : ℝ) * (1 - (i : ℝ) / m) :=
        mul_le_mul_of_nonneg_right humax hfac
      linarith
    have hLi0 : 0 < Lp t u m i := hσ0.trans_le hσL
    have hum : 0 ≤ u / m := div_nonneg hu0 hmR.le
    have hstep : Lp t u m (i + 1) = Lp t u m i + u / m := by
      unfold Lp; push_cast; ring
    have hLi1 : Lp t u m (i + 1) ≤ t := by
      unfold Lp
      have : 0 ≤ u * (1 - ((i + 1 : ℕ) : ℝ) / m) := mul_nonneg hu0 hfac1
      linarith
    have hLi_lt : Lp t u m i < 1 := by linarith
    have htan := H_le_tangent (x := Lp t u m (i + 1)) (y := Lp t u m i)
      (by linarith) (by linarith) hLi0 hLi_lt
    have hJ := J_anti hσ0 hσL hLi_lt
    have hJhi : J ((dyq N : ℚ) : ℝ) ≤ (((vd N).Jhi : ℚ) : ℝ) := by
      have := VD.le_Jhi (vd_sound hN); rw [vd_v] at this; exact this
    have hd : Lp t u m (i + 1) - Lp t u m i = u / m := by rw [hstep]; ring
    rw [hd] at htan
    have h1 : J (Lp t u m i) * (u / m) ≤ (((vd N).Jhi : ℚ) : ℝ) * (u / m) :=
      mul_le_mul_of_nonneg_right (hJ.trans hJhi) hum
    have hsum : ((jSum (N :: rest) : ℚ) : ℝ) = (((vd N).Jhi : ℚ) : ℝ) + ((jSum rest : ℚ) : ℝ) := by
      simp only [jSum]; push_cast; ring
    rw [hsum, mul_add]
    linarith

theorem exclOK_parts {c : Ctx} {A1 A2 : ℚ} {ex : ℕ} {kap : ℚ} {sig : List ℕ}
    (h : exclOK c A1 A2 ex kap sig = true) :
    0 < kap ∧ 0 < c.t1 - umaxOf c A1 A2 kap ∧
      (exclRiem c A1 A2 kap sig = true ∨ exclDir c A1 A2 kap sig = true) := by
  unfold exclOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨of_decide_eq_true h1, of_decide_eq_true h2, ?_⟩
  split_ifs at h3
  · exact Or.inl h3
  · exact Or.inr h3

theorem lam_lt_of_exclOK {c : Ctx} {A1 A2 : ℚ} {ex : ℕ} {kap : ℚ} {sig : List ℕ}
    (h : exclOK c A1 A2 ex kap sig = true) {a t A W lam : ℝ} (P : PtFacts a t A W lam)
    (C : CtxOK c t W) (hA1 : (A1 : ℝ) ≤ A) (hA2 : A ≤ (A2 : ℝ)) (hA1nn : (0 : ℝ) ≤ A1) :
    lam < (1 + (kap : ℝ) * A) / 2 := by
  obtain ⟨hk, hU, hcase⟩ := exclOK_parts h
  have hkR : (0 : ℝ) < kap := by exact_mod_cast hk
  have hUR' : (0 : ℝ) < (c.t1 : ℝ) - ((umaxOf c A1 A2 kap : ℚ) : ℝ) := by exact_mod_cast hU
  have hUR : ((umaxOf c A1 A2 kap : ℚ) : ℝ) =
      2 * (A2 : ℝ) * (c.Hh : ℝ) / (1 + (kap : ℝ) * (A1 : ℝ)) := by
    unfold umaxOf; push_cast; ring
  have hA0 : 0 < A := P.hA
  have hHt := P.Ht0
  have h1k1 : (0 : ℝ) < 1 + (kap : ℝ) * A1 := by have := mul_nonneg hkR.le hA1nn; linarith
  have h1k : (0 : ℝ) < 1 + (kap : ℝ) * A := by have := mul_pos hkR hA0; linarith
  have hnum0 : 0 ≤ 2 * A * H t := mul_nonneg (mul_nonneg (by norm_num) hA0.le) hHt.le
  set u : ℝ := 2 * A * H t / (1 + (kap : ℝ) * A) with hu_def
  have hu0 : 0 ≤ u := div_nonneg hnum0 h1k.le
  have hu_le : u ≤ ((umaxOf c A1 A2 kap : ℚ) : ℝ) := by
    rw [hUR, hu_def]
    have hnum : 2 * A * H t ≤ 2 * (A2 : ℝ) * (c.Hh : ℝ) := by
      have := mul_le_mul hA2 C.hHh hHt.le (hA0.le.trans hA2)
      linarith
    have hden : 1 + (kap : ℝ) * A1 ≤ 1 + (kap : ℝ) * A := by
      have := mul_le_mul_of_nonneg_left hA1 hkR.le; linarith
    calc 2 * A * H t / (1 + (kap : ℝ) * A) ≤ 2 * A * H t / (1 + (kap : ℝ) * A1) :=
          div_le_div_of_nonneg_left hnum0 h1k1 hden
      _ ≤ 2 * (A2 : ℝ) * (c.Hh : ℝ) / (1 + (kap : ℝ) * A1) := div_le_div_of_nonneg_right hnum h1k1.le
  have htu : 0 < t - u := by linarith [C.ht1]
  have hH : H t - H (t - u) ≤ u * kap := by
    rcases hcase with hR | hD
    · unfold exclRiem at hR
      rw [Bool.and_eq_true, Bool.and_eq_true] at hR
      obtain ⟨⟨hm, hsig⟩, hJ⟩ := hR
      have hm' : 0 < sig.length := of_decide_eq_true hm
      have hJ' : jSum sig ≤ sig.length * kap := of_decide_eq_true hJ
      have hr := sig_riemann hm' C.ht1 P.ht2 hu0 hu_le sig 0 hsig (by simp)
      have hmR : (0 : ℝ) < sig.length := by exact_mod_cast hm'
      have hLm : Lp t u sig.length (0 + sig.length) = t := by
        unfold Lp; simp only [zero_add]; rw [div_self hmR.ne']; ring
      have hL0 : Lp t u sig.length 0 = t - u := by unfold Lp; simp
      rw [hLm, hL0] at hr
      have hJR : ((jSum sig : ℚ) : ℝ) ≤ (sig.length : ℝ) * (kap : ℝ) := by exact_mod_cast hJ'
      calc H t - H (t - u) ≤ u / sig.length * ((jSum sig : ℚ) : ℝ) := hr
        _ ≤ u / sig.length * ((sig.length : ℝ) * (kap : ℝ)) :=
            mul_le_mul_of_nonneg_left hJR (div_nonneg hu0 hmR.le)
        _ = u * kap := by field_simp
    · unfold exclDir at hD
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hD
      obtain ⟨⟨⟨⟨-, hA1p⟩, hN⟩, hle⟩, hgap⟩ := hD
      set N := sig.headD 0
      have hσ0 : (0 : ℝ) < ((dyq N : ℚ) : ℝ) := dyq_pos hN
      have hleR : ((dyq N : ℚ) : ℝ) ≤ (c.t1 : ℝ) - ((umaxOf c A1 A2 kap : ℚ) : ℝ) := by
        exact_mod_cast hle
      have hσtu : ((dyq N : ℚ) : ℝ) ≤ t - u := by linarith [C.ht1]
      have hHσ : (((vd N).Hlo : ℚ) : ℝ) ≤ H (t - u) := by
        have h1 := VD.Hlo_le (vd_sound hN)
        rw [vd_v] at h1
        exact h1.trans (H_mono hσ0.le hσtu (by linarith [P.ht2]))
      have hgapR : ((c.Hh : ℚ) : ℝ) - (((vd N).Hlo : ℚ) : ℝ) ≤
          (kap : ℝ) * (2 * (A1 : ℝ) * (c.Hl : ℝ) / (1 + (kap : ℝ) * (A2 : ℝ))) := by
        exact_mod_cast hgap
      have h1k2 : (0 : ℝ) < 1 + (kap : ℝ) * A2 := by
        have := mul_nonneg hkR.le (hA0.le.trans hA2); linarith
      have humin : 2 * (A1 : ℝ) * (c.Hl : ℝ) / (1 + (kap : ℝ) * (A2 : ℝ)) ≤ u := by
        rw [hu_def]
        have hnum : 2 * (A1 : ℝ) * (c.Hl : ℝ) ≤ 2 * A * H t := by
          have := mul_le_mul hA1 C.hHl C.hHl0.le hA0.le
          linarith
        have hden : 1 + (kap : ℝ) * A ≤ 1 + (kap : ℝ) * A2 := by
          have := mul_le_mul_of_nonneg_left hA2 hkR.le; linarith
        calc 2 * (A1 : ℝ) * (c.Hl : ℝ) / (1 + (kap : ℝ) * (A2 : ℝ))
            ≤ 2 * A * H t / (1 + (kap : ℝ) * (A2 : ℝ)) := div_le_div_of_nonneg_right hnum h1k2.le
          _ ≤ 2 * A * H t / (1 + (kap : ℝ) * A) := div_le_div_of_nonneg_left hnum0 h1k hden
      have hk2 := mul_le_mul_of_nonneg_left humin hkR.le
      have hHh := C.hHh
      linarith
  exact exclusion P.ha P.hat P.ht2 hA0 P.W0 P.HW P.hlam0 P.hL P.hcase hkR htu hH

theorem lamBar_sound {c : Ctx} {A1 A2 : ℚ} {ex : ℕ} {kap : ℚ} {sig : List ℕ} {a t A W lam : ℝ}
    (P : PtFacts a t A W lam) (C : CtxOK c t W) (hA1 : (A1 : ℝ) ≤ A) (hA2 : A ≤ (A2 : ℝ))
    (hA1nn : (0 : ℝ) ≤ A1) :
    lam ≤ ((lamBar c A1 A2 ex kap sig : ℚ) : ℝ) ∧ (0 : ℝ) < ((lamBar c A1 A2 ex kap sig : ℚ) : ℝ) := by
  unfold lamBar
  split_ifs with hc
  · obtain ⟨-, hex⟩ := hc
    have hl := lam_lt_of_exclOK hex P C hA1 hA2 hA1nn
    have hk : (0 : ℝ) < kap := by exact_mod_cast (exclOK_parts hex).1
    have hA0 := P.hA
    push_cast
    constructor
    · apply le_min P.hlam1.le
      have := mul_le_mul_of_nonneg_left hA2 hk.le
      linarith
    · apply lt_min one_pos
      have := mul_pos hk (hA0.trans_le hA2)
      linarith
  · push_cast
    exact ⟨P.hlam1.le, one_pos⟩

/-! ## Soundness: bracket families -/

theorem fam1_sound {W2lo W2hi A1 A2 : ℚ} {kq : ℕ} (hkq : 0 < kq) {W2 A : ℝ}
    (hW2lo : (W2lo : ℝ) ≤ W2) (hW2hi : W2 ≤ (W2hi : ℝ)) (hA1 : (A1 : ℝ) ≤ A) (hA2 : A ≤ (A2 : ℝ))
    (hA1nn : (0 : ℝ) ≤ A1) :
    ∀ (l : List (ℕ × ℕ)) (i : ℕ), fam1OK W2lo W2hi A1 A2 kq i l = true →
      e8Theta (W2 + ((i + l.length : ℕ) : ℝ) * A / kq) - e8Theta (W2 + (i : ℝ) * A / kq) ≤
        ((brSum l : ℚ) : ℝ) * (A / kq) ∧ (0 : ℝ) ≤ ((brSum l : ℚ) : ℝ)
  | [], i, _ => by simp [brSum]
  | p :: rest, i, h => by
    simp only [fam1OK, Bool.and_eq_true] at h
    obtain ⟨ih1, ih2⟩ := fam1_sound hkq hW2lo hW2hi hA1 hA2 hA1nn rest (i + 1) h.2
    have e : i + (p :: rest).length = (i + 1) + rest.length := by
      simp only [List.length_cons]; omega
    rw [e]
    have hkqR : (0 : ℝ) < kq := by exact_mod_cast hkq
    have hA0 : 0 ≤ A := hA1nn.trans hA1
    have hiR : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hb := brB_sound h.1 (x := W2 + (i : ℝ) * A / kq) (y := W2 + ((i + 1 : ℕ) : ℝ) * A / kq)
      ?_ ?_ ?_
    · have hbp := brB_pos h.1
      have hsum : ((brSum (p :: rest) : ℚ) : ℝ) = ((brB p.1 p.2 : ℚ) : ℝ) + ((brSum rest : ℚ) : ℝ) := by
        simp only [brSum]; push_cast; ring
      have hd : W2 + ((i + 1 : ℕ) : ℝ) * A / kq - (W2 + (i : ℝ) * A / kq) = A / kq := by
        push_cast; ring
      rw [hd] at hb
      refine ⟨?_, ?_⟩
      · rw [hsum, add_mul]; linarith
      · rw [hsum]; linarith
    · push_cast
      have : (i : ℝ) * A1 / kq ≤ (i : ℝ) * A / kq :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA1 hiR) hkqR.le
      linarith
    · push_cast
      have : (i : ℝ) * A / kq ≤ ((i : ℝ) + 1) * A / kq :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hA0) hkqR.le
      linarith
    · push_cast
      have : ((i : ℝ) + 1) * A / kq ≤ ((i : ℝ) + 1) * A2 / kq :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA2 (by positivity)) hkqR.le
      linarith

theorem fam2_sound {Wlo Whi kA1 kA2 : ℚ} {k : ℕ} (hk : 0 < k) {W kA : ℝ}
    (hW0 : 0 ≤ W) (hWlo : (Wlo : ℝ) ≤ W) (hWhi : W ≤ (Whi : ℝ)) (hkA1 : (kA1 : ℝ) ≤ kA)
    (hkA2 : kA ≤ (kA2 : ℝ)) (hkA1nn : (0 : ℝ) ≤ kA1) :
    ∀ (l : List (ℕ × ℕ)) (j : ℕ), fam2OK Wlo Whi kA1 kA2 k j l = true →
      e8Theta (W * (1 + ((j + l.length : ℕ) : ℝ) * kA / k)) - e8Theta (W * (1 + (j : ℝ) * kA / k)) ≤
        ((brSum l : ℚ) : ℝ) * (W * kA / k) ∧ (0 : ℝ) ≤ ((brSum l : ℚ) : ℝ)
  | [], j, _ => by simp [brSum]
  | p :: rest, j, h => by
    simp only [fam2OK, Bool.and_eq_true] at h
    obtain ⟨ih1, ih2⟩ := fam2_sound hk hW0 hWlo hWhi hkA1 hkA2 hkA1nn rest (j + 1) h.2
    have e : j + (p :: rest).length = (j + 1) + rest.length := by
      simp only [List.length_cons]; omega
    rw [e]
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hkA0 : 0 ≤ kA := hkA1nn.trans hkA1
    have hWhi0 : (0 : ℝ) ≤ Whi := hW0.trans hWhi
    have hjR : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hb := brB_sound h.1 (x := W * (1 + (j : ℝ) * kA / k))
      (y := W * (1 + ((j + 1 : ℕ) : ℝ) * kA / k)) ?_ ?_ ?_
    · have hbp := brB_pos h.1
      have hsum : ((brSum (p :: rest) : ℚ) : ℝ) = ((brB p.1 p.2 : ℚ) : ℝ) + ((brSum rest : ℚ) : ℝ) := by
        simp only [brSum]; push_cast; ring
      have hd : W * (1 + ((j + 1 : ℕ) : ℝ) * kA / k) - W * (1 + (j : ℝ) * kA / k) = W * kA / k := by
        push_cast; ring
      rw [hd] at hb
      refine ⟨?_, ?_⟩
      · rw [hsum, add_mul]; linarith
      · rw [hsum]; linarith
    · push_cast
      apply mul_le_mul hWlo _ _ hW0
      · have : (j : ℝ) * kA1 / k ≤ (j : ℝ) * kA / k :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkA1 hjR) hkR.le
        linarith
      · have : (0 : ℝ) ≤ (j : ℝ) * kA1 / k := div_nonneg (mul_nonneg hjR hkA1nn) hkR.le
        linarith
    · apply mul_le_mul_of_nonneg_left _ hW0
      push_cast
      have : (j : ℝ) * kA / k ≤ ((j : ℝ) + 1) * kA / k :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hkA0) hkR.le
      linarith
    · push_cast
      apply mul_le_mul hWhi _ _ hWhi0
      · have : ((j : ℝ) + 1) * kA / k ≤ ((j : ℝ) + 1) * kA2 / k :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkA2 (by positivity)) hkR.le
        linarith
      · have : (0 : ℝ) ≤ ((j : ℝ) + 1) * kA / k := div_nonneg (mul_nonneg (by positivity) hkA0) hkR.le
        linarith

/-! ## Soundness: the three cell kinds -/

theorem nOK_sound {c : Ctx} {A1 : ℚ} {cl : Cell} (h : nOK c A1 cl = true) {a t A W lam : ℝ}
    (P : PtFacts a t A W lam) (C : CtxOK c t W) (hA1 : (A1 : ℝ) ≤ A)
    (hA2 : A ≤ ((dq cl.A2n : ℚ) : ℝ)) : 0 < Dst A W lam := by
  unfold nOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, hA1nn, -, -, hexcl, hthlo, hkq, hlen, hf1, hf2, hval⟩ := h
  have hA1nnR : (0 : ℝ) ≤ A1 := by exact_mod_cast hA1nn
  have hk0 : 0 < cl.br.length - cl.kq := by omega
  have hkqR : (0 : ℝ) < cl.kq := by exact_mod_cast hkq
  have hkkR : (0 : ℝ) < ((cl.br.length - cl.kq : ℕ) : ℝ) := by exact_mod_cast hk0
  have hκ : (0 : ℝ) < ((dq cl.kapn : ℚ) : ℝ) := by exact_mod_cast (exclOK_parts hexcl).1
  have hlam := lam_lt_of_exclOK hexcl P C hA1 hA2 hA1nnR
  have hA0 := P.hA
  have hW0 := P.W0
  have hA2pos : (0 : ℝ) < ((dq cl.A2n : ℚ) : ℝ) := hA0.trans_le hA2
  have hκA : (0 : ℝ) ≤ ((dq cl.kapn : ℚ) : ℝ) * A := mul_nonneg hκ.le hA0.le
  -- `W₂ = (1+κA)W` and the λ̄-substitution
  have hW2pos : 0 < (1 + ((dq cl.kapn : ℚ) : ℝ) * A) * W := mul_pos (by linarith) hW0
  have hlt : A + 2 * lam * W < A + (1 + ((dq cl.kapn : ℚ) : ℝ) * A) * W := by
    have h2 : 2 * lam < 1 + ((dq cl.kapn : ℚ) : ℝ) * A := by linarith
    have := mul_lt_mul_of_pos_right h2 hW0
    linarith
  have hpos1 : 0 < A + 2 * lam * W := by
    have := mul_pos (mul_pos two_pos P.hlam0) hW0; linarith
  have hmono : e8Theta (A + 2 * lam * W) < e8Theta (A + (1 + ((dq cl.kapn : ℚ) : ℝ) * A) * W) :=
    strictMonoOn_e8Theta_pos hpos1 (show 0 < A + (1 + ((dq cl.kapn : ℚ) : ℝ) * A) * W by linarith) hlt
  -- Θ(A) ≥ A·Slo/A2
  have hth := thLoOK_sound hthlo (x := ((dq cl.A2n : ℚ) : ℝ)) le_rfl
  have hratio := theta_ge_ratio hA0 hA2
  have hTA : A * ((((vd (cl.th.headD 0)).Slo : ℚ) : ℝ) / ((dq cl.A2n : ℚ) : ℝ)) ≤ e8Theta A := by
    refine le_trans ?_ hratio
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hth hA2pos.le) hA0.le
  -- first family: Θ(A + W₂) − Θ(W₂)
  have hW2lo : ((((1 + dq cl.kapn * A1) * c.Wlo) : ℚ) : ℝ) ≤ (1 + ((dq cl.kapn : ℚ) : ℝ) * A) * W := by
    push_cast
    have h1 : (0 : ℝ) ≤ 1 + ((dq cl.kapn : ℚ) : ℝ) * A1 := by
      have := mul_nonneg hκ.le hA1nnR; linarith
    have h2 : 1 + ((dq cl.kapn : ℚ) : ℝ) * A1 ≤ 1 + ((dq cl.kapn : ℚ) : ℝ) * A := by
      have := mul_le_mul_of_nonneg_left hA1 hκ.le; linarith
    calc (1 + ((dq cl.kapn : ℚ) : ℝ) * A1) * (c.Wlo : ℝ)
        ≤ (1 + ((dq cl.kapn : ℚ) : ℝ) * A1) * W := mul_le_mul_of_nonneg_left C.hWlo h1
      _ ≤ (1 + ((dq cl.kapn : ℚ) : ℝ) * A) * W := mul_le_mul_of_nonneg_right h2 hW0.le
  have hW2hi : (1 + ((dq cl.kapn : ℚ) : ℝ) * A) * W ≤
      ((((1 + dq cl.kapn * dq cl.A2n) * c.Whi) : ℚ) : ℝ) := by
    push_cast
    have h2 : 1 + ((dq cl.kapn : ℚ) : ℝ) * A ≤ 1 + ((dq cl.kapn : ℚ) : ℝ) * ((dq cl.A2n : ℚ) : ℝ) := by
      have := mul_le_mul_of_nonneg_left hA2 hκ.le; linarith
    calc (1 + ((dq cl.kapn : ℚ) : ℝ) * A) * W
        ≤ (1 + ((dq cl.kapn : ℚ) : ℝ) * A) * (c.Whi : ℝ) := mul_le_mul_of_nonneg_left C.hWhi (by linarith)
      _ ≤ (1 + ((dq cl.kapn : ℚ) : ℝ) * ((dq cl.A2n : ℚ) : ℝ)) * (c.Whi : ℝ) :=
          mul_le_mul_of_nonneg_right h2 (hW0.le.trans C.hWhi)
  have hl1len : (cl.br.take cl.kq).length = cl.kq := by
    rw [List.length_take]; omega
  obtain ⟨hF1, hS1⟩ := fam1_sound hkq hW2lo hW2hi hA1 hA2 hA1nnR (cl.br.take cl.kq) 0 hf1
  rw [hl1len] at hF1
  have e1 : (1 + ((dq cl.kapn : ℚ) : ℝ) * A) * W + ((0 + cl.kq : ℕ) : ℝ) * A / cl.kq =
      A + (1 + ((dq cl.kapn : ℚ) : ℝ) * A) * W := by
    simp only [zero_add]; rw [mul_div_cancel_left₀ A hkqR.ne']; ring
  have e0 : (1 + ((dq cl.kapn : ℚ) : ℝ) * A) * W + ((0 : ℕ) : ℝ) * A / cl.kq =
      (1 + ((dq cl.kapn : ℚ) : ℝ) * A) * W := by simp
  rw [e1, e0] at hF1
  -- second family: Θ(W₂) − Θ(W)
  have hl2len : (cl.br.drop cl.kq).length = cl.br.length - cl.kq := List.length_drop ..
  have hkA1 : (((dq cl.kapn * A1 : ℚ)) : ℝ) ≤ ((dq cl.kapn : ℚ) : ℝ) * A := by
    push_cast; exact mul_le_mul_of_nonneg_left hA1 hκ.le
  have hkA2 : ((dq cl.kapn : ℚ) : ℝ) * A ≤ (((dq cl.kapn * dq cl.A2n : ℚ)) : ℝ) := by
    push_cast; exact mul_le_mul_of_nonneg_left hA2 hκ.le
  have hkA1nn : (0 : ℝ) ≤ ((dq cl.kapn * A1 : ℚ) : ℝ) := by
    push_cast; exact mul_nonneg hκ.le hA1nnR
  obtain ⟨hF2, hS2⟩ := fam2_sound hk0 hW0.le C.hWlo C.hWhi hkA1 hkA2 hkA1nn (cl.br.drop cl.kq) 0 hf2
  rw [hl2len] at hF2
  have e3 : W * (1 + ((0 + (cl.br.length - cl.kq) : ℕ) : ℝ) * (((dq cl.kapn : ℚ) : ℝ) * A) /
      ((cl.br.length - cl.kq : ℕ) : ℝ)) = (1 + ((dq cl.kapn : ℚ) : ℝ) * A) * W := by
    simp only [zero_add]; rw [mul_div_cancel_left₀ _ hkkR.ne']; ring
  have e4 : W * (1 + ((0 : ℕ) : ℝ) * (((dq cl.kapn : ℚ) : ℝ) * A) /
      ((cl.br.length - cl.kq : ℕ) : ℝ)) = W := by simp
  rw [e3, e4] at hF2
  -- assemble
  have hvalR : (0 : ℝ) < (((vd (cl.th.headD 0)).Slo : ℚ) : ℝ) / ((dq cl.A2n : ℚ) : ℝ) -
      ((brSum (cl.br.take cl.kq) : ℚ) : ℝ) / (cl.kq : ℝ) -
      ((dq cl.kapn : ℚ) : ℝ) * (c.Whi : ℝ) * ((brSum (cl.br.drop cl.kq) : ℚ) : ℝ) /
        ((cl.br.length - cl.kq : ℕ) : ℝ) := by
    exact_mod_cast hval
  have hT3 : ((brSum (cl.br.drop cl.kq) : ℚ) : ℝ) *
        (W * (((dq cl.kapn : ℚ) : ℝ) * A) / ((cl.br.length - cl.kq : ℕ) : ℝ)) ≤
      ((brSum (cl.br.drop cl.kq) : ℚ) : ℝ) *
        ((c.Whi : ℝ) * (((dq cl.kapn : ℚ) : ℝ) * A) / ((cl.br.length - cl.kq : ℕ) : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ hS2
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right C.hWhi hκA) hkkR.le
  have key : A * ((((vd (cl.th.headD 0)).Slo : ℚ) : ℝ) / ((dq cl.A2n : ℚ) : ℝ)) -
      ((brSum (cl.br.take cl.kq) : ℚ) : ℝ) * (A / cl.kq) -
      ((brSum (cl.br.drop cl.kq) : ℚ) : ℝ) *
        ((c.Whi : ℝ) * (((dq cl.kapn : ℚ) : ℝ) * A) / ((cl.br.length - cl.kq : ℕ) : ℝ)) =
      A * ((((vd (cl.th.headD 0)).Slo : ℚ) : ℝ) / ((dq cl.A2n : ℚ) : ℝ) -
        ((brSum (cl.br.take cl.kq) : ℚ) : ℝ) / (cl.kq : ℝ) -
        ((dq cl.kapn : ℚ) : ℝ) * (c.Whi : ℝ) * ((brSum (cl.br.drop cl.kq) : ℚ) : ℝ) /
          ((cl.br.length - cl.kq : ℕ) : ℝ)) := by ring
  have hprod := mul_pos hA0 hvalR
  unfold Dst
  linarith

theorem gOK_sound {c : Ctx} {A1 : ℚ} {cl : Cell} (h : gOK c A1 cl = true) {a t A W lam : ℝ}
    (P : PtFacts a t A W lam) (C : CtxOK c t W) (hA1 : (A1 : ℝ) ≤ A)
    (hA2 : A ≤ ((dq cl.A2n : ℚ) : ℝ)) : 0 < Dst A W lam := by
  unfold gOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, hA1p, ht2, hlo, hhi, hval⟩ := h
  have hA1pR : (0 : ℝ) < A1 := by exact_mod_cast hA1p
  obtain ⟨hlb, hlb0⟩ := lamBar_sound (ex := cl.ex) (kap := dq cl.kapn) (sig := cl.sig) P C hA1 hA2
    hA1pR.le
  have hW0 := P.W0
  have hx : A + 2 * lam * W ≤
      (((dq cl.A2n + 2 * lamBar c A1 (dq cl.A2n) cl.ex (dq cl.kapn) cl.sig * c.Whi) : ℚ) : ℝ) := by
    push_cast
    have := mul_le_mul hlb C.hWhi hW0.le hlb0.le
    linarith
  have hpos1 : 0 < A + 2 * lam * W := by
    have := mul_pos (mul_pos two_pos P.hlam0) hW0; linarith [P.hA]
  have hup := thHiOK_sound hhi hpos1 hx
  have hlo' := thLoOK_sound hlo hA1
  have hS2 := C.hS2 ht2
  have hvalR : (0 : ℝ) < (((vd (cl.th.getD 0 0)).Slo : ℚ) : ℝ) + ((c.S2 : ℚ) : ℝ) -
      (((vd (cl.th.getD 1 0)).Shi : ℚ) : ℝ) := by exact_mod_cast hval
  unfold Dst
  linarith

theorem wOK_sound {c : Ctx} {A1 : ℚ} {cl : Cell} (h : wOK c A1 cl = true) {a t A W lam : ℝ}
    (P : PtFacts a t A W lam) (C : CtxOK c t W) (hA1 : (A1 : ℝ) ≤ A)
    (hA2 : A ≤ ((dq cl.A2n : ℚ) : ℝ)) : 0 < Dst A W lam := by
  unfold wOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, hA1p, hWt, hthlo, hbr, hval⟩ := h
  have hA1pR : (0 : ℝ) < A1 := by exact_mod_cast hA1p
  obtain ⟨hlb, hlb0⟩ := lamBar_sound (ex := cl.ex) (kap := dq cl.kapn) (sig := cl.sig) P C hA1 hA2
    hA1pR.le
  have hW0 := P.W0
  have hWtR : (c.Whi : ℝ) ≤ ((dq cl.Wtn : ℚ) : ℝ) := by exact_mod_cast hWt
  have hWle : W ≤ ((dq cl.Wtn : ℚ) : ℝ) := C.hWhi.trans hWtR
  have hWt0 : (0 : ℝ) < ((dq cl.Wtn : ℚ) : ℝ) := hW0.trans_le hWle
  have hth := thLoOK_sound hthlo (x := ((dq cl.Wtn : ℚ) : ℝ)) le_rfl
  have hratio := theta_ge_ratio hW0 hWle
  have hTW : W * ((((vd (cl.th.headD 0)).Slo : ℚ) : ℝ) / ((dq cl.Wtn : ℚ) : ℝ)) ≤ e8Theta W := by
    refine le_trans ?_ hratio
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hth hWt0.le) hW0.le
  have hy : A + 2 * lam * W ≤
      (((dq cl.A2n + 2 * lamBar c A1 (dq cl.A2n) cl.ex (dq cl.kapn) cl.sig * c.Whi) : ℚ) : ℝ) := by
    push_cast
    have := mul_le_mul hlb C.hWhi hW0.le hlb0.le
    linarith
  have hxy : A ≤ A + 2 * lam * W := by
    have := mul_pos (mul_pos two_pos P.hlam0) hW0; linarith
  have hinc := brB_sound hbr hA1 hxy hy
  have hbp := brB_pos hbr
  have hvalR : (0 : ℝ) < (((vd (cl.th.headD 0)).Slo : ℚ) : ℝ) / ((dq cl.Wtn : ℚ) : ℝ) -
      2 * ((lamBar c A1 (dq cl.A2n) cl.ex (dq cl.kapn) cl.sig : ℚ) : ℝ) *
        ((brB (cl.br.headD (0, 0)).1 (cl.br.headD (0, 0)).2 : ℚ) : ℝ) := by
    exact_mod_cast hval
  have h2 : ((brB (cl.br.headD (0, 0)).1 (cl.br.headD (0, 0)).2 : ℚ) : ℝ) * (A + 2 * lam * W - A) ≤
      ((brB (cl.br.headD (0, 0)).1 (cl.br.headD (0, 0)).2 : ℚ) : ℝ) *
        (2 * ((lamBar c A1 (dq cl.A2n) cl.ex (dq cl.kapn) cl.sig : ℚ) : ℝ) * W) := by
    apply mul_le_mul_of_nonneg_left _ hbp.le
    have := mul_le_mul_of_nonneg_right hlb hW0.le
    linarith
  have key : W * ((((vd (cl.th.headD 0)).Slo : ℚ) : ℝ) / ((dq cl.Wtn : ℚ) : ℝ)) -
      ((brB (cl.br.headD (0, 0)).1 (cl.br.headD (0, 0)).2 : ℚ) : ℝ) *
        (2 * ((lamBar c A1 (dq cl.A2n) cl.ex (dq cl.kapn) cl.sig : ℚ) : ℝ) * W) =
      W * ((((vd (cl.th.headD 0)).Slo : ℚ) : ℝ) / ((dq cl.Wtn : ℚ) : ℝ) -
        2 * ((lamBar c A1 (dq cl.A2n) cl.ex (dq cl.kapn) cl.sig : ℚ) : ℝ) *
          ((brB (cl.br.headD (0, 0)).1 (cl.br.headD (0, 0)).2 : ℚ) : ℝ)) := by ring
  have hprod := mul_pos hW0 hvalR
  unfold Dst
  linarith

theorem cellOK_sound {c : Ctx} {A1 : ℚ} {cl : Cell} (h : cellOK c A1 cl = true) {a t A W lam : ℝ}
    (P : PtFacts a t A W lam) (C : CtxOK c t W) (hA1 : (A1 : ℝ) ≤ A)
    (hA2 : A ≤ ((dq cl.A2n : ℚ) : ℝ)) : 0 < Dst A W lam := by
  unfold cellOK at h
  split_ifs at h
  · exact nOK_sound h P C hA1 hA2
  · exact gOK_sound h P C hA1 hA2
  · exact wOK_sound h P C hA1 hA2

theorem cells_sound {c : Ctx} {a t A W lam : ℝ} (P : PtFacts a t A W lam) (C : CtxOK c t W)
    (hA4 : A < 4) : ∀ (cells : List Cell) (A1 : ℚ), cellsOK c A1 cells = true → (A1 : ℝ) ≤ A →
      0 < Dst A W lam
  | [], A1, h, hA1 => by
    simp only [cellsOK, decide_eq_true_eq] at h
    have : (4 : ℝ) ≤ A1 := by exact_mod_cast h
    linarith
  | cl :: rest, A1, h, hA1 => by
    simp only [cellsOK, Bool.and_eq_true] at h
    by_cases hA2 : A ≤ ((dq cl.A2n : ℚ) : ℝ)
    · exact cellOK_sound h.1 P C hA1 hA2
    · exact cells_sound P C hA4 rest (dq cl.A2n) h.2 (le_of_lt (not_le.mp hA2))

theorem strip_sound {s : Strip} (h : stripOK s = true) {a t A W lam : ℝ} (P : PtFacts a t A W lam)
    (ht1 : ((dyq s.N1 : ℚ) : ℝ) ≤ t) (ht2 : t ≤ ((dyq s.N2 : ℚ) : ℝ)) (hA4 : A < 4)
    (hnc : t < 11 / 32 + 2 * A) : 0 < Dst A W lam := by
  unfold stripOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨h1, h2, -, hHl, hA0, hcells⟩ := h
  have C := ctx_sound h1 h2 hHl P ht1 ht2
  apply cells_sound P C hA4 s.cells (dq s.A0n) hcells
  rcases hA0 with h0 | h0
  · rw [h0]; push_cast; exact P.hA.le
  · have h' := (Rat.cast_le (K := ℝ)).mpr h0
    push_cast at h'
    linarith

theorem chain_cover : ∀ (l : List Strip) (n : ℕ), chainOK n l = true →
    ∀ t : ℝ, ((dyq n : ℚ) : ℝ) ≤ t → t < 1 / 2 →
      ∃ s ∈ l, ((dyq s.N1 : ℚ) : ℝ) ≤ t ∧ t ≤ ((dyq s.N2 : ℚ) : ℝ)
  | [], n, h, t, ht, ht2 => by
    simp only [chainOK, beq_iff_eq] at h
    subst h
    have : ((dyq THN : ℚ) : ℝ) = 1 / 2 := by
      unfold dyq THN; push_cast; norm_num
    linarith
  | s :: rest, n, h, t, ht, ht2 => by
    simp only [chainOK, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hn, hr⟩ := h
    by_cases hts : t ≤ ((dyq s.N2 : ℚ) : ℝ)
    · exact ⟨s, List.mem_cons.mpr (Or.inl rfl), by rw [← hn]; exact ht, hts⟩
    · obtain ⟨s', hs', h1, h2⟩ := chain_cover rest s.N2 hr t (le_of_lt (not_le.mp hts)) ht2
      exact ⟨s', List.mem_cons.mpr (Or.inr hs'), h1, h2⟩

/-- **Cover soundness.**  A checked, chained strip list rules out every chart point with
`t ≥ ⌊2^40/100⌋/2^40`, `A < 4`, `t < 11/32 + 2A`. -/
theorem cover_sound (l : List Strip) (hall : l.all stripOK = true) (hch : chainOK T0N l = true)
    {a t A W lam : ℝ} (P : PtFacts a t A W lam) (ht : ((dyq T0N : ℚ) : ℝ) ≤ t) (hA4 : A < 4)
    (hnc : t < 11 / 32 + 2 * A) : 0 < Dst A W lam := by
  obtain ⟨s, hs, h1, h2⟩ := chain_cover l T0N hch t ht P.ht2
  exact strip_sound (List.all_eq_true.mp hall s hs) P h1 h2 hA4 hnc

#print axioms cover_sound

end CKLaneA1.R5

end


