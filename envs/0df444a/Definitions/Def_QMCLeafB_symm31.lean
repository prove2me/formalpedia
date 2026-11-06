-- Prove2me | Definitions.Def_QMCLeafB_symm31
-- name    : QMCLeafB_symm31
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:00:37.525871+00:00
-- url     : https://prove2.me/theorems/c9c0e3fa-e8db-4dd8-baf7-58275ba812b3
-- title:
--   QMCLeafB symm31
-- statement:
--   `Check_symm31_m7` — phase 31, member m7, direction `symm-invariant`.
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_MatQ
import Definitions.Def_QMCLeafB_pivexact
import Definitions.Def_QMCLeafB_matq_update_m4
import Definitions.Def_QMCLeafB_RStInit
import Definitions.Def_QMCLeafB_htop_oklower_m7
import Definitions.Def_QMCLeafB_eaudit2
/-
  `Check_symm31_m7` — phase 31, member m7, direction `symm-invariant`.

  **The unowned slot.**  At an `ok` round of `OkLower.roundW` the programme's `hok` owes a
  `RelaxOracle.RelaxMem` at a SYMMETRIC rational centre, and every certified-test bridge
  (`RelaxApiM3.relaxMem_at_campaign_of_grid`, `LdltCertM5.pivPsdMargin_of_tolerance`) also takes

      hsym : ∀ i j, PivExact.matOf n (stX s) i j = PivExact.matOf n (stX s) j i

  as a hypothesis.  d1's accepted residual, d4's programme lane and d3's mechanical slots all *state*
  it; nobody on the board proves it.  This file does, along the whole `roundW` orbit of `init0`.

  **The predicate.**  `CodeSymm n X` — the row-major code is symmetric as a `MatQ.entry` array.  It is
  definitionally the same statement as `PivExact.matOf`'s symmetry (`entV` and `MatQ.entry` are the
  same `getD`), and it implies `MatQ.toMatrix`'s matrix symmetry (`hCsym`).

  **Why it holds.**  One round replaces `X` by `snapY s = nrmRow mu d (scaleY s)`, and
  `scaleY s = smulRaw ((n, stepY s), α⁻¹)` with
  `stepY s = Step.stepFun ((n, X), (c, λ))`.  `Step.stepProg_spec`/`updProg_spec` give

      stepFun ((n, xs), (c, λ)) = MatQ.sub n xs (MatQ.smul μ n (MatQ.ofMatrix n (vecMulVec w w)))

  with `w = vecOf n (MatQ.mulVec n xs c)` — a rank-one update, whose symmetric part does not depend on
  `c` at all (`vecMulVec w w` is symmetric by `mul_comm`).  So: `MatQ.mk`/`add`/`smul`/`neg`/`sub`/
  `ofMatrix` symmetry, entrywise-map (`nrmRow`) preservation, and induction on the iterate.

  Note the round's *normal* is never used: the symmetry obligation is normal-independent, which is
  why it survives any re-pointing of the `ok` test (the certified-test programme variant d4/d1 need).

  Discipline: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; `#print axioms` at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

noncomputable section

namespace Symm31M7

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open QMCLeafB.RoundProgram

/-! ## 1.  The symmetry predicate -/

/-- **The state's code is symmetric**: the `n × n` row-major array reads the same across the
diagonal.  `MatQ.entry` is the same `getD` that `PivExact.matOf` uses, so this *is* the engine's
`hsym`. -/
def CodeSymm (n : ℕ) (X : List ℚ) : Prop :=
  ∀ i j : ℕ, i < n → j < n → MatQ.entry n X i j = MatQ.entry n X j i

theorem codeSymm_comm {n : ℕ} {X : List ℚ} (h : CodeSymm n X) {i j : ℕ} (hi : i < n)
    (hj : j < n) : MatQ.entry n X i j = MatQ.entry n X j i := h i j hi hj

/-- **`CodeSymm` is `PivExact.matOf`'s `hsym`, verbatim.** -/
theorem matOf_symm {n : ℕ} {X : List ℚ} (h : CodeSymm n X) (i j : Fin n) :
    QMCLeafB.PivExact.matOf n X i j = QMCLeafB.PivExact.matOf n X j i :=
  h (i : ℕ) (j : ℕ) i.isLt j.isLt

/-- **`CodeSymm` gives the matrix symmetry `hCsym`.** -/
theorem toMatrix_symm {n : ℕ} {X : List ℚ} (h : CodeSymm n X) :
    (MatQ.toMatrix n X)ᵀ = MatQ.toMatrix n X := by
  ext i j
  rw [Matrix.transpose_apply]
  exact h (j : ℕ) (i : ℕ) j.isLt i.isLt

/-! ## 2.  `MatQ`'s operations preserve it -/

theorem mk_symm {n : ℕ} {f : ℕ → ℕ → ℚ}
    (hf : ∀ i j, i < n → j < n → f i j = f j i) : CodeSymm n (MatQ.mk n f) := by
  intro i j hi hj
  rw [MatQ.entry_mk n f hi hj, MatQ.entry_mk n f hj hi]
  exact hf i j hi hj

theorem add_symm {n : ℕ} {xs ys : List ℚ} (hx : CodeSymm n xs) (hy : CodeSymm n ys) :
    CodeSymm n (MatQ.add n xs ys) := by
  intro i j hi hj
  rw [MatQ.entry_add n xs ys hi hj, MatQ.entry_add n xs ys hj hi, hx i j hi hj, hy i j hi hj]

theorem smul_symm {n : ℕ} (c : ℚ) {xs : List ℚ} (hx : CodeSymm n xs) :
    CodeSymm n (MatQ.smul c n xs) := by
  intro i j hi hj
  rw [MatQ.entry_smul c n xs hi hj, MatQ.entry_smul c n xs hj hi, hx i j hi hj]

theorem neg_symm {n : ℕ} {xs : List ℚ} (hx : CodeSymm n xs) : CodeSymm n (MatQ.neg n xs) := by
  intro i j hi hj
  rw [MatQ.entry_neg n xs hi hj, MatQ.entry_neg n xs hj hi, hx i j hi hj]

theorem sub_symm {n : ℕ} {xs ys : List ℚ} (hx : CodeSymm n xs) (hy : CodeSymm n ys) :
    CodeSymm n (MatQ.sub n xs ys) :=
  add_symm hx (neg_symm hy)

theorem ofMatrix_symm {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ}
    (hM : ∀ i j : Fin n, M i j = M j i) : CodeSymm n (MatQ.ofMatrix n M) := by
  intro i j hi hj
  rw [show MatQ.entry n (MatQ.ofMatrix n M) i j
      = M ⟨i, hi⟩ ⟨j, hj⟩ from MatQ.entry_ofMatrix n M ⟨i, hi⟩ ⟨j, hj⟩,
    show MatQ.entry n (MatQ.ofMatrix n M) j i
      = M ⟨j, hj⟩ ⟨i, hi⟩ from MatQ.entry_ofMatrix n M ⟨j, hj⟩ ⟨i, hi⟩]
  exact hM ⟨i, hi⟩ ⟨j, hj⟩

theorem vecMulVec_symm {n : ℕ} (w : Fin n → ℚ) :
    ∀ i j : Fin n, Matrix.vecMulVec w w i j = Matrix.vecMulVec w w j i := by
  intro i j
  rw [Matrix.vecMulVec_apply, Matrix.vecMulVec_apply, mul_comm]

/-! ## 3.  Entrywise maps (`nrmRow`) preserve it -/

theorem getD_map_of_lt (f : ℚ → ℚ) (l : List ℚ) {k : ℕ} (hk : k < l.length) :
    (l.map f).getD k 0 = f (l.getD k 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ hk,
    List.getElem_map]

theorem entry_map {n : ℕ} (g : ℚ → ℚ) (X : List ℚ) (i j : ℕ) (h : i * n + j < X.length) :
    MatQ.entry n (X.map g) i j = g (MatQ.entry n X i j) :=
  getD_map_of_lt g X h

theorem map_symm {n : ℕ} (g : ℚ → ℚ) {X : List ℚ} (hX : CodeSymm n X)
    (hlen : X.length = n * n) : CodeSymm n (X.map g) := by
  intro i j hi hj
  have h1 : i * n + j < X.length := by
    have : i * n + j < n * n := by
      have hjn : j < n := hj
      have hin : i < n := hi
      nlinarith
    omega
  have h2 : j * n + i < X.length := by
    have : j * n + i < n * n := by nlinarith
    omega
  rw [entry_map g X i j h1, entry_map g X j i h2, hX i j hi hj]

theorem nrmRow_symm {n : ℕ} (mu : ℚ) (d : ℕ) {X : List ℚ} (hX : CodeSymm n X)
    (hlen : X.length = n * n) : CodeSymm n (nrmRow mu d X) := by
  unfold nrmRow
  exact map_symm (nrmQ mu d) hX hlen


/-! ## 4.  The round's step preserves it

`Step.stepProg_spec`/`updProg_spec` write the update as
`MatQ.sub n xs (MatQ.smul μ n (MatQ.ofMatrix n (vecMulVec w w)))`: the rank-one part is symmetric by
`mul_comm`, so the whole step is symmetric **whatever the normal is**. -/

theorem updFun_symm (n : ℕ) (xs ws : List ℚ) (mu : ℚ) (hx : xs.length = n * n)
    (hs : CodeSymm n xs) :
    CodeSymm n (QMCLeafB.MatQUpdate.Upd.updFun ((n, xs), (ws, mu))) := by
  rw [QMCLeafB.MatQUpdate.updProg_spec n xs ws mu hx]
  exact sub_symm hs (smul_symm mu (ofMatrix_symm (vecMulVec_symm _)))

theorem stepFun_symm (n : ℕ) (xs cs : List ℚ) (lam : ℚ) (hx : xs.length = n * n)
    (hs : CodeSymm n xs) :
    CodeSymm n (QMCLeafB.MatQUpdate.Step.stepFun ((n, xs), (cs, lam))) := by
  unfold QMCLeafB.MatQUpdate.Step.stepFun
  exact updFun_symm n xs _ _ hx hs

theorem stepFun_length' (n : ℕ) (xs cs : List ℚ) (lam : ℚ) (hx : xs.length = n * n) :
    (QMCLeafB.MatQUpdate.Step.stepFun ((n, xs), (cs, lam))).length = n * n :=
  QMCLeafB.MatQUpdate.Step.stepFun_length n xs cs lam hx

/-- `stepY` at the state is symmetric whenever the state's code is. -/
theorem stepY_symm (s : RSt) (hx : (stX s).length = stN s * stN s)
    (hs : CodeSymm (stN s) (stX s)) : CodeSymm (stN s) (stepY s) :=
  stepFun_symm (stN s) (stX s) ((oracleR s).2) _ hx hs

/-! ## 5.  `smulRaw`, `scaleY`, `snapY` -/

theorem smulRaw_eq_smul (n : ℕ) (v : List ℚ) (c : ℚ) (hv : v.length = n * n) :
    QMCLeafB.MatQUpdate.smulRaw ((n, v), c) = MatQ.smul c n v := by
  unfold QMCLeafB.MatQUpdate.smulRaw MatQ.smul MatQ.mk MatQ.entry
  rw [List.length_take, hv, Nat.min_eq_left (QMCLeafB.RStInit.self_le_mul_self n)]
  simp only [List.getD_eq_getElem?_getD]

theorem scaleY_symm (s : RSt) (hx : (stX s).length = stN s * stN s)
    (hs : CodeSymm (stN s) (stX s)) : CodeSymm (stN s) (scaleY s) := by
  unfold scaleY
  rw [smulRaw_eq_smul (stN s) (stepY s) (alphInv (stN s))
    (stepFun_length' (stN s) (stX s) ((oracleR s).2) _ hx)]
  exact smul_symm _ (stepY_symm s hx hs)

/-- **The round's new primal code is symmetric.** -/
theorem snapY_symm (s : RSt) (hx : (stX s).length = stN s * stN s)
    (hs : CodeSymm (stN s) (stX s)) : CodeSymm (stN s) (snapY s) := by
  have hsc : CodeSymm (stN s) (scaleY s) := scaleY_symm s hx hs
  have hlen : (scaleY s).length = stN s * stN s := by
    conv_lhs => rw [show scaleY s = MatQ.smul (alphInv (stN s)) (stN s) (stepY s) from by
      unfold scaleY
      exact smulRaw_eq_smul (stN s) (stepY s) (alphInv (stN s))
        (stepFun_length' (stN s) (stX s) ((oracleR s).2) _ hx)]
    exact MatQ.smul_length _ _ _
  unfold snapY
  exact nrmRow_symm _ _ hsc hlen

/-! ## 6.  `roundW` and the orbit -/

theorem codeSymm_roundW (s : RSt) (hx : (stX s).length = stN s * stN s)
    (hs : CodeSymm (stN s) (stX s)) :
    CodeSymm (stN (QMCLeafB.OkLower.roundW s)) (stX (QMCLeafB.OkLower.roundW s)) := by
  rw [EAudit2M7.stN_roundW]
  by_cases hreg : 0 ≤ stT s + QMCLeafB.RoundT.epsOf s
  · rw [EAudit2M7.stX_roundW_regime s hreg]; exact hs
  · by_cases hc : (QMCLeafB.OkLower.oracleV s).1 = true
    · rw [EAudit2M7.stX_roundW_cut s hreg hc]; exact snapY_symm s hx hs
    · rw [EAudit2M7.stX_roundW_ok s hreg (by simpa using hc)]; exact hs

/-- **The state's code is symmetric at every visited state of the `roundW` orbit.** -/
theorem codeSymm_orbitW (p : QMCLeafB.FuelWire.Pkg) (k : ℕ) :
    CodeSymm (stN (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p)))
      (stX (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p))) := by
  induction k with
  | zero =>
      show CodeSymm (stN (QMCLeafB.RStInit.init0 p)) (stX (QMCLeafB.RStInit.init0 p))
      have hx0 : stX (QMCLeafB.RStInit.init0 p)
          = QMCLeafB.InitVerdict.identVia
              (QMCLeafB.InitVerdict.doubleUp (QuantumMaxCutEnergy.encodeRequest p.1))
              (QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1))
              ((QMCLeafB.InitVerdict.MOf
                (QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)))⁻¹) := rfl
      rw [hx0, QMCLeafB.InitVerdict.identVia_eq_mk _ _
        (by rw [QMCLeafB.InitVerdict.doubleUp_length]
            exact Nat.le_trans (QMCLeafB.InitVerdict.inputWidth_le_length _)
              (QMCLeafB.RStInit.self_le_mul_self _))]
      refine mk_symm (fun i j hi hj => ?_)
      by_cases h : i = j
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact codeSymm_roundW _ (EAudit2M7.stX_length_orbitW _ (QMCLeafB.RStInit.stX_length p) j) ih

/-! ## 7.  The two shapes the consumers ask for -/

/-- **`LdltCertM5.pivPsdMargin_of_tolerance`'s `hsym`, at every visited state.** -/
theorem hsym_orbitW (p : QMCLeafB.FuelWire.Pkg) (k : ℕ) :
    ∀ i j : Fin (stN (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p))),
      QMCLeafB.PivExact.matOf (stN (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p)))
          (stX (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p))) i j
        = QMCLeafB.PivExact.matOf (stN (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p)))
            (stX (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p))) j i :=
  matOf_symm (codeSymm_orbitW p k)

/-- **`RundataCert.hcert_of_relaxMem`'s `hCsym` (`cXᵀ = cX`), at every visited state.**  This is the
symmetry obligation inside the composite's `hok` slot. -/
theorem hCsym_orbitW (p : QMCLeafB.FuelWire.Pkg) (k : ℕ) :
    (MatQ.toMatrix (stN (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p)))
        (stX (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p))))ᵀ
      = MatQ.toMatrix (stN (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p)))
          (stX (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p))) :=
  toMatrix_symm (codeSymm_orbitW p k)

end Symm31M7

/-! ## Axiom audit -/

#print axioms Symm31M7.matOf_symm
#print axioms Symm31M7.toMatrix_symm
#print axioms Symm31M7.add_symm
#print axioms Symm31M7.smul_symm
#print axioms Symm31M7.sub_symm
#print axioms Symm31M7.ofMatrix_symm
#print axioms Symm31M7.map_symm
#print axioms Symm31M7.nrmRow_symm
#print axioms Symm31M7.updFun_symm
#print axioms Symm31M7.stepFun_symm
#print axioms Symm31M7.smulRaw_eq_smul
#print axioms Symm31M7.scaleY_symm
#print axioms Symm31M7.snapY_symm
#print axioms Symm31M7.codeSymm_roundW
#print axioms Symm31M7.codeSymm_orbitW
#print axioms Symm31M7.hsym_orbitW
#print axioms Symm31M7.hCsym_orbitW


