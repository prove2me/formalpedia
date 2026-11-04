-- Prove2me | Definitions.Def_QMCLeafB_verdictok
-- name    : QMCLeafB_verdictok
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:24:56.853726+00:00
-- url     : https://prove2.me/theorems/6337965e-277c-45d8-a5ef-88cb20abd068
-- title:
--   QMCLeafB verdictok
-- statement:
--   # leaf B phase 20 — brick `verdict-true` (swarm `smw1kspvn`, member m8, direction d10)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_flags_m5
/-
# leaf B phase 20 — brick `verdict-true` (swarm `smw1kspvn`, member m8, direction d10)

`FlagsM5.ResidH` asks for one `BundleH` per interior `(G,t)`.  `BundleH`'s cut side (`C`, `marg`,
`c`, `cn`, `lam`, `hlam1`, `hlam2`, `hdriftc`, `hdriftd`) is conditioned on `ok k = false`, while the
`ok` stream, the centres and the normals are **free data**.  This file takes the one choice that
makes all of it vacuous: the all-`ok` stream with the pinched centre `diagPinch X dq` of a *single*
rational point `X` of the campaign's relaxation.  Then

* `hmem` is `relaxMem_diagPinch_of_diagNear` (§0 — the body's diagonal band `|X i i − 1| ≤ dq/4`
  *plus exact PSD*; this supersedes `CentreAdm.relaxMem_diagPinch`, which asked for a unit diagonal),
* `hTrc` is `CentreAdm.sum_diagPinch` (equality),
* `hCsym` is `CentreAdm.diagPinch_symm`,
* `hcn`/`hcne` are `flatQ 1 ≠ 0` and `lam = 1`,
* and `hverdict` is `o G t = anyOk (fun _ => true) (K*m) = true`.

So the only inputs that are not free choices are the verdict bit and one feasible point:

  `bundleH_of_verdict_true : o G t = true → Xᵀ = X → (∀ i, |X i i − 1| ≤ dq/4) → PSD X →
     frob (wMatrixQ G) X ≤ t − ε + dq/2 → BundleH o G t P hn`

— at the **actual** `o`, not a weakened one.  §2 lifts this to `ResidH` (hence, by
`FlagsM5.solution_of_residH`, to the verbatim `d9f601e5` sentence) from two slots: `o = true` on the
interior, and such a witness at each interior point.  §3 states the exact split: the witness slot
forces `frob ≤ t − ε + dq/2`, so it can only hold where the relaxation is nonempty at threshold
`t − ε`; the part of the bracket left to the cut branch (bricks 1/2) is exactly the part where no
such point exists.  §4 validates the construction against the banked occupant
`FlagsM5.bundleH_G₀_inhabited`: at `(G₀, −1/2)` the witness is `!![1,-1;-1,1]` (unit diagonal, PSD,
objective `−1 ≤ −1/2 − ε + dq/2`), i.e. the same point the phase-19 refutation used against the
all-`false` stream.

Consequence for the swarm: on the verdict-true part of the interior neither the LDLT PSD margin
(brick 1) nor the record zip (brick 2) is needed at all.

**Where that part is, exactly (and why §5's split is the usable form).**  The witness slot forces
`frob (wMatrixQ G) X ≤ t − ε + dq/2`, so it can hold only where the relaxation carries a point at
threshold `t − ε + dq/2` — i.e. only for `t ≥ opt(G) + ε − dq/2`, with `opt(G)` the body's minimum.
At the bottom of the bracket `t = −Rq G` that minimum is at least `−(1 + dq/4)·Rq` (for a band point
`|X i j|² ≤ X i i X j j ≤ (1 + dq/4)²`), while the slot would need `−(1 + dq/4)Rq ≤ −Rq − ε + dq/2`,
i.e. `ε ≤ dq(1/2 + Rq/4)` — false at `dq = dqShallow ≈ ε/(9 Rq + 1)`.  So `OkCover` on the **whole**
interior is not attainable near `t = −Rq`, and `solution_of_okCover` below must be read as the formal
whole-interior special case; the content is the split: §3's `bundleH_of_okCover_above` on `t ≥ T`
plus §5's `solution_of_split`, with the cut branch confined to `t < T`.  Near `t = −Rq` every round
is a cut round *by force* (no centre can be a member), which is precisely the regime bricks 1/2 own.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audits at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.VerdictOkM8

open QuantumMaxCutEnergy
open QMCLeafB.SepOracle
open QMCLeafB.RelaxOracle
open QMCLeafB.CentreAdm
open QMCLeafB.FlagsM5

/-! ## 0.  The pinch certificate at any point with the body's diagonal band

`CentreAdm.relaxMem_diagPinch` asks the witness to be *unit-diagonal*.  The pinch only spends the
diagonal shift `dq/4`, so the honest hypothesis is the body's own band `|Q i i - 1| ≤ dq/4` together
with **exact** PSD — which is what `RunInduction.runPiv_psd` supplies at a state, and what a
`RelaxMem` certificate does *not* (it only gives the margin form).  The unit-diagonal version is the
special case `Q i i = 1`. -/

/-- **The pinched `RelaxMem` certificate from the diagonal band and exact PSD.** -/
theorem relaxMem_diagPinch_of_diagNear {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (hdq : 0 < dq) (hdq4 : dq ≤ 4) (hA : ∀ i, A i i = 0)
    (hdiag : ∀ i, |Q i i - 1| ≤ dq / 4)
    (hpsd : ∀ x : Fin n → ℚ, 0 ≤ QMCLeafB.SepOracle.qf Q x)
    (htrace : QMCLeafB.SepOracle.frob A Q ≤ u + dq / 2) :
    QMCLeafB.RelaxOracle.RelaxMem A (diagPinch Q dq) u dq where
  δ_pos := hdq
  psd_margin := by
    intro x
    have hbound : -(dq / 2) * (∑ i, x i ^ 2)
        ≤ ∑ i, ((1 - dq / 4) - Q i i) * x i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ?_)
      have hb := abs_le.mp (hdiag i)
      have hsq : 0 ≤ x i ^ 2 := sq_nonneg (x i)
      have hfac : 0 ≤ 1 + dq / 4 - Q i i := by linarith [hb.2]
      nlinarith [mul_nonneg hfac hsq]
    rw [qf_diagPinch]
    have hp := hpsd x
    linarith
  diag_near := abs_diagPinch Q hdq hdq4
  trace_le := by
    rw [frob_diagPinch hA]
    exact htrace

#print axioms QMCLeafB.VerdictOkM8.relaxMem_diagPinch_of_diagNear

/-! ## 1.  The all-`ok` bundle at the actual verdict bit -/

/-- **`BundleH` from the verdict bit and one feasible point.**  The stream is the all-`ok` one, the
centres are the pinched centre `diagPinch X dq` of a single rational point, the dilation is
`lam = 1` on the identity direction and `c = 0`.  Every cut-side slot is vacuous, `hmem` is the
pinched `RelaxMem` certificate, and `hverdict` is `anyOk` of an all-`true` stream. -/
def bundleH_of_verdict_true
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (ho : o G t = true)
    (hKm : 0 < P.K * P.m)
    (h4 : P.dq ≤ 4)
    (X : Matrix (Fin G.n) (Fin G.n) ℚ)
    (hXsym : Xᵀ = X) (hXdiag : ∀ i, |X i i - 1| ≤ P.dq / 4)
    (hXpsd : ∀ x : Fin G.n → ℚ, 0 ≤ qf X x)
    (hfrob : frob (QMCLeafB.Finalization.wMatrixQ G) X
      ≤ (t - QMCLeafB.RundataCert.eps G) + P.dq / 2) :
    BundleH o G t P hn := by
  have hany : QMCLeafB.SimLoop.anyOk (fun _ : ℕ => true) (P.K * P.m) = true := by
    conv_lhs => rw [show P.K * P.m = (P.K * P.m - 1) + 1 from by omega]
    exact QMCLeafB.InhabitM5.anyOk_true_succ _
  have hfalse : ∀ k : ℕ, (fun _ : ℕ => true) k = false → False :=
    fun k hk => absurd hk (QMCLeafB.InhabitM5.okTrue_ne_false k)
  have hsymm : ∀ i j, X i j = X j i :=
    fun i j => by
      have h := congrFun (congrFun hXsym j) i
      rwa [Matrix.transpose_apply] at h
  have hne : QMCLeafB.RelaxOracle.flatQ
      (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ≠ 0 :=
    QMCLeafB.FlagsM5.flatQ_one_ne_zero' (by omega)
  exact { ok := (fun _ => true),
            marg := (fun _ => 1),
            cX := (fun _ => diagPinch X P.dq),
            lam := (fun _ => 1),
            c := (fun _ => 0),
            cn := (fun _ => QMCLeafB.RelaxOracle.flatQ
              (1 : Matrix (Fin G.n) (Fin G.n) ℚ)),
            C := (fun k hok => (hfalse k hok).elim),
            hmarg := (fun k hok => (hfalse k hok).elim),
            hmem := (fun k _ _ =>
              relaxMem_diagPinch_of_diagNear P.hdq h4
                (fun i => QMCLeafB.Finalization.wMatrixQ_apply_of_eq) hXdiag hXpsd hfrob),
            hCsym := (fun _ => Matrix.ext (fun i j => diagPinch_symm hsymm P.dq j i)),
            hcEq := (fun k hok => (hfalse k hok).elim),
            hcn := (fun _ => by
              show QMCLeafB.RelaxOracle.flatQ
                  (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
                = 0 + (1 : ℚ) • QMCLeafB.RelaxOracle.flatQ
                    (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
              simp),
            hcne := (fun _ => hne),
            hlam0 := (fun _ => by norm_num),
            hlam1 := (fun k hok => (hfalse k hok).elim),
            hlam2 := (fun k hok => (hfalse k hok).elim),
            hTrc := (fun _ => le_of_eq (sum_diagPinch X P.dq)),
            hdriftc := (fun k hok => (hfalse k hok).elim),
            hdriftd := (fun k hok => (hfalse k hok).elim),
            hverdict := ho.trans hany.symm }

#print axioms QMCLeafB.VerdictOkM8.bundleH_of_verdict_true

/-! ## 2.  `ResidH` from the two slots -/

/-- The two slots, verbatim: the program's bit is `true` on the interior bracket, and every interior
point admits a rational unit-diagonal PSD point under the round threshold's own slack. -/
def OkCover (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Prop :=
  (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) → o G t = true) ∧
  (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      ∃ X : Matrix (Fin G.n) (Fin G.n) ℚ, Xᵀ = X ∧
        (∀ i, |X i i - 1| ≤ (Pfam G).dq / 4) ∧
        (∀ x : Fin G.n → ℚ, 0 ≤ qf X x) ∧
        frob (QMCLeafB.Finalization.wMatrixQ G) X
          ≤ (t - QMCLeafB.RundataCert.eps G) + (Pfam G).dq / 2)

/-- **`ResidH` from `OkCover` and the two parameter side conditions.**  This is the whole leaf minus
the verdict read-out and one SDP witness per interior point: no LDLT margin and no record stream. -/
def residH_of_okCover
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hcov : OkCover o Pfam)
    (hKm : ∀ G, 0 < (Pfam G).K * (Pfam G).m)
    (h4 : ∀ G, (Pfam G).dq ≤ 4) :
    QMCLeafB.FlagsM5.ResidH o Pfam := by
  intro G t hn hlo hhi
  exact bundleH_of_verdict_true (hcov.1 G t hn hlo hhi) (hKm G) (h4 G)
    (Classical.choose (hcov.2 G t hn hlo hhi))
    (Classical.choose_spec (hcov.2 G t hn hlo hhi)).1
    (Classical.choose_spec (hcov.2 G t hn hlo hhi)).2.1
    (Classical.choose_spec (hcov.2 G t hn hlo hhi)).2.2.1
    (Classical.choose_spec (hcov.2 G t hn hlo hhi)).2.2.2

#print axioms QMCLeafB.VerdictOkM8.residH_of_okCover

/-- **The tolerance side condition holds unconditionally** — `dqShallow`'s `Rq = 0` fallback is `1`,
so `dq ≤ 4` needs no positivity of the weight sum.  (`CentreAdm.dqShallow_le_four` covers the other
branch.) -/
theorem dqShallow_le_four_all (G : QuantumMaxCutEnergy.Input) :
    (QMCLeafB.UnionShallow.paramsKbc2 G).dq ≤ 4 := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_dq]
  by_cases h : QMCLeafB.EngineRuntime.Rq G = 0
  · unfold QMCLeafB.RundataParams.dqShallow
    rw [if_pos h]
    norm_num
  · exact QMCLeafB.CentreAdm.dqShallow_le_four G
      (lt_of_le_of_ne (QMCLeafB.RundataArith.Rq_nonneg G) (Ne.symm h))

#print axioms QMCLeafB.VerdictOkM8.dqShallow_le_four_all

/-- **The verbatim `d9f601e5` sentence from `OkCover`** — the assembled chain, at the campaign's own
program `loopBit init0 round verdict Tbc2` and parameter family `paramsKbc2`, with no side
condition left. -/
theorem solution_of_okCover
    (hcov : OkCover
      (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
        QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
        QMCLeafB.ClosingAssembly.Tbc2)
      QMCLeafB.UnionShallow.paramsKbc2) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  QMCLeafB.FlagsM5.solution_of_residH
    (residH_of_okCover hcov
      (fun G => lt_of_lt_of_le Nat.zero_lt_one (QMCLeafB.UnionShallow.one_le_Kbc2_mul G))
      dqShallow_le_four_all)

#print axioms QMCLeafB.VerdictOkM8.solution_of_okCover

/-! ## 3.  The exact split: the cut branch lives only below the attainable threshold -/

/-- **The split.**  At any threshold family `T`, the ok-cover discharges `BundleH` on `t ≥ T G` and
leaves the cut branch on `t < T G`.  Taking `T G := -Rq G + eps G - dq/2` is the sharp choice: below
it the witness slot asks for a point strictly under the round threshold, i.e. for a nonempty
relaxation at `t − ε`, which is exactly what the cut branch is for. -/
def bundleH_of_okCover_above
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (T : QuantumMaxCutEnergy.Input → ℚ)
    (hT : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) → T G ≤ t →
      o G t = true ∧
      ∃ X : Matrix (Fin G.n) (Fin G.n) ℚ, Xᵀ = X ∧
        (∀ i, |X i i - 1| ≤ (Pfam G).dq / 4) ∧
        (∀ x : Fin G.n → ℚ, 0 ≤ qf X x) ∧
        frob (QMCLeafB.Finalization.wMatrixQ G) X
          ≤ (t - QMCLeafB.RundataCert.eps G) + (Pfam G).dq / 2)
    (hKm : ∀ G, 0 < (Pfam G).K * (Pfam G).m)
    (h4 : ∀ G, (Pfam G).dq ≤ 4)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {hn : 2 ≤ G.n}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (habove : T G ≤ t) :
    BundleH o G t (Pfam G) hn := by
  have h := hT G t hn hlo hhi habove
  exact bundleH_of_verdict_true h.1 (hKm G) (h4 G) (Classical.choose h.2)
    (Classical.choose_spec h.2).1 (Classical.choose_spec h.2).2.1
    (Classical.choose_spec h.2).2.2.1 (Classical.choose_spec h.2).2.2.2

#print axioms QMCLeafB.VerdictOkM8.bundleH_of_okCover_above

/-! ## 4.  Consistency with the banked occupant at `(G₀, −1/2)` -/

/-- The rank-one point of the two-vertex relaxation: unit diagonal and PSD. -/
def Z₀ : Matrix (Fin 2) (Fin 2) ℚ := !![1, -1; -1, 1]

theorem Z₀_diag (i : Fin 2) : Z₀ i i = 1 := by
  fin_cases i <;> simp [Z₀]

theorem Z₀_transpose : Z₀ᵀ = Z₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Z₀]

theorem Z₀_qf (x : Fin 2 → ℚ) : 0 ≤ QMCLeafB.SepOracle.qf Z₀ x := by
  rw [QMCLeafB.SepOracle.qf_eq_sum]
  simp only [Fin.sum_univ_two, Z₀, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.of_apply]
  nlinarith [sq_nonneg (x 0 - x 1)]

/-- **The objective at `Z₀`**: `frob (wMatrixQ G₀) Z₀ = -1` — the point is *deep* under the round
threshold `-1/2 - ε`, which is exactly why the all-`ok` stream is available there. -/
theorem frob_Z₀ :
    QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀) Z₀
      = -1 := by
  have e00 : QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀
      (0 : Fin QMCLeafB.ResidRefute.G₀.n) (0 : Fin QMCLeafB.ResidRefute.G₀.n) = 0 :=
    QMCLeafB.Finalization.wMatrixQ_apply_of_eq
  have e11 : QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀
      (1 : Fin QMCLeafB.ResidRefute.G₀.n) (1 : Fin QMCLeafB.ResidRefute.G₀.n) = 0 :=
    QMCLeafB.Finalization.wMatrixQ_apply_of_eq
  have e01 : QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀
      (0 : Fin QMCLeafB.ResidRefute.G₀.n) (1 : Fin QMCLeafB.ResidRefute.G₀.n) = 1 / 2 := by
    unfold QMCLeafB.Finalization.wMatrixQ
    norm_num [QMCLeafB.ResidRefute.G₀]
  have e10 : QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀
      (1 : Fin QMCLeafB.ResidRefute.G₀.n) (0 : Fin QMCLeafB.ResidRefute.G₀.n) = 1 / 2 := by
    unfold QMCLeafB.Finalization.wMatrixQ
    norm_num [QMCLeafB.ResidRefute.G₀]
  simp only [QMCLeafB.SepOracle.frob, Fin.sum_univ_two, e00, e01, e10, e11, Z₀,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.of_apply]
  norm_num

/-- **The witness slot at `(G₀, −1/2)`**: `Z₀` sits under the round threshold with room to spare. -/
theorem feas_G₀ :
    QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀) Z₀
      ≤ (-(1 / 2) - QMCLeafB.RundataCert.eps QMCLeafB.ResidRefute.G₀)
        + (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq / 2 := by
  rw [frob_Z₀, QMCLeafB.FlagsM5.eps_G₀]
  have h := (QMCLeafB.UnionShallow.paramsKbc2
    QMCLeafB.ResidRefute.G₀).hdq
  linarith

/-- **The construction re-proves the banked occupant.**  `FlagsM5.bundleH_G₀_inhabited` was obtained
from the pinch of `Q₀ = !![1,-3/4;-3/4,1]` through `InhabitM5.relaxMem_pinch`; the all-`ok` bundle
here comes from `Z₀` through `CentreAdm.relaxMem_diagPinch`, i.e. the two independent routes agree at
the one interior point where the residual is known to be inhabited. -/
theorem bundleH_G₀_via_verdict :
    Nonempty (BundleH (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      QMCLeafB.ResidKill.hnG₀) := by
  have hRq : 0 < QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ := by
    rw [QMCLeafB.ResidRefute.Rq_G₀]
    norm_num
  exact ⟨bundleH_of_verdict_true rfl
    (lt_of_lt_of_le Nat.zero_lt_one
      (QMCLeafB.UnionShallow.one_le_Kbc2_mul QMCLeafB.ResidRefute.G₀))
    (QMCLeafB.CentreAdm.dqShallow_le_four QMCLeafB.ResidRefute.G₀ hRq)
    Z₀ Z₀_transpose
    (fun i => by
      rw [Z₀_diag i, sub_self, abs_zero]
      have h := (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).hdq
      linarith)
    Z₀_qf feas_G₀⟩

#print axioms QMCLeafB.VerdictOkM8.frob_Z₀
#print axioms QMCLeafB.VerdictOkM8.feas_G₀
#print axioms QMCLeafB.VerdictOkM8.bundleH_G₀_via_verdict

/-- **The campaign-instantiated form**: at `paramsKbc2` no side condition on `K*m` or `dq`
survives, so this is the form d3/d5 can plug a PSD-margin slot straight into. -/
def bundleH_paramsKbc2_of_verdict_true
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {hn : 2 ≤ G.n}
    (ho : o G t = true)
    (X : Matrix (Fin G.n) (Fin G.n) ℚ)
    (hXsym : Xᵀ = X) (hXband : ∀ i, |X i i - 1| ≤ (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
    (hXpsd : ∀ x : Fin G.n → ℚ, 0 ≤ qf X x)
    (hfrob : frob (QMCLeafB.Finalization.wMatrixQ G) X
      ≤ (t - QMCLeafB.RundataCert.eps G) + (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 2) :
    BundleH o G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn :=
  bundleH_of_verdict_true ho
    (lt_of_lt_of_le Nat.zero_lt_one (QMCLeafB.UnionShallow.one_le_Kbc2_mul G))
    (dqShallow_le_four_all G) X hXsym hXband hXpsd hfrob

#print axioms QMCLeafB.VerdictOkM8.bundleH_paramsKbc2_of_verdict_true

/-! ## 5.  What `hverdict` says, exactly — and the split

At the canonical stream the verdict equation is *not* an opaque program fact: `anyOk` of the flag
stream is true iff some round's centre is a member of the relaxation at the round threshold.  So
`BundleH`'s only contact with the run is the two-sided membership existential below, and `OkCover.1`
is precisely the assertion that it is true at every interior `(G,t)`. -/

/-- A member centre raises the canonical flag. -/
theorem flagOf_true_of_relaxMem {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq) :
    flagOf G t P cX k = true := by
  by_cases hR : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
    (t - QMCLeafB.RundataCert.eps G) P.dq
  · simp [flagOf, hR]
  · exact absurd h hR

/-- The canonical flag is *exactly* the membership predicate. -/
theorem flagOf_true_iff {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ} :
    flagOf G t P cX k = true
      ↔ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
          (t - QMCLeafB.RundataCert.eps G) P.dq :=
  ⟨fun h => relaxMem_of_flagOf_true G t P cX k h, fun h => flagOf_true_of_relaxMem h⟩

#print axioms QMCLeafB.VerdictOkM8.flagOf_true_iff

/-- **`hverdict`, unfolded**: the program's bit is the membership existential over the run's
rounds. -/
theorem anyOk_flagOf_true_iff {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (T : ℕ) :
    QMCLeafB.SimLoop.anyOk (flagOf G t P cX) T = true
      ↔ ∃ k, k < T ∧ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
          (t - QMCLeafB.RundataCert.eps G) P.dq := by
  rw [QMCLeafB.SimLoop.anyOk_eq_true_iff]
  exact exists_congr (fun k => and_congr_right (fun _ => flagOf_true_iff))

#print axioms QMCLeafB.VerdictOkM8.anyOk_flagOf_true_iff

/-- **The residual splits at any threshold family.**  Above `T` the ok-cover discharges the bundle;
below `T` the cut branch is what is left.  `T G = -Rq G + eps G - dq/2` is the sharp choice, since
below it the witness slot would ask for a body point under the round threshold. -/
def residH_of_split
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (T : QuantumMaxCutEnergy.Input → ℚ)
    (habove : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) → T G ≤ t →
      BundleH o G t (Pfam G) hn)
    (hbelow : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) → t < T G →
      BundleH o G t (Pfam G) hn) :
    QMCLeafB.FlagsM5.ResidH o Pfam := by
  intro G t hn hlo hhi
  by_cases h : T G ≤ t
  · exact habove G t hn hlo hhi h
  · exact hbelow G t hn hlo hhi (lt_of_not_ge h)

#print axioms QMCLeafB.VerdictOkM8.residH_of_split

/-- **The verbatim `d9f601e5` sentence from the split** — the usable form.  `habove` is what this
file discharges (`bundleH_of_okCover_above`), `hbelow` is what is left to the cut branch, and no
side condition survives. -/
theorem solution_of_split
    (T : QuantumMaxCutEnergy.Input → ℚ)
    (habove : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) → T G ≤ t →
      BundleH (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
        QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
        QMCLeafB.ClosingAssembly.Tbc2) G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn)
    (hbelow : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) → t < T G →
      BundleH (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
        QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
        QMCLeafB.ClosingAssembly.Tbc2) G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  QMCLeafB.FlagsM5.solution_of_residH (residH_of_split T habove hbelow)

#print axioms QMCLeafB.VerdictOkM8.solution_of_split

end QMCLeafB.VerdictOkM8

/-! ## 5.  Axiom audit -/

#print axioms QMCLeafB.VerdictOkM8.bundleH_of_verdict_true
#print axioms QMCLeafB.VerdictOkM8.residH_of_okCover
#print axioms QMCLeafB.VerdictOkM8.solution_of_okCover
#print axioms QMCLeafB.VerdictOkM8.bundleH_of_okCover_above


