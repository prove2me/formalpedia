-- Prove2me | Definitions.Def_QMCLeafB_crux_m1
-- name    : QMCLeafB_crux_m1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:50:44.987104+00:00
-- url     : https://prove2.me/theorems/7143c9e0-cff8-4619-8bf4-4f189302891c
-- title:
--   QMCLeafB crux_m1
-- statement:
--   # `Check_crux_m1` — phase 30, member m1, direction `crux` (d1, gate for d5)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_unionShallow
import Definitions.Def_QMCLeafB_zero_margin_cut_m1
import Definitions.Def_QMCLeafB_hemptyR
/-
# `Check_crux_m1` — phase 30, member m1, direction `crux` (d1, gate for d5)

**The question.**  Does the *all-false record class* (`ok k = false` for every `k < K·m`) compose
with `RunParts.hcut`'s transcript pairing against `Cat k` — the *accumulated* engine centre — or
only at empty bodies?

`RunParts.hcut` is (verbatim, `Def_QMCLeafB_final_stroke_m7` §5):

    hcut : ∀ k, k < K·m → ok k = false → ∀ z,
      z ∈ Boundary.relaxBall (wMatrix G) (t - Rq G/40000) dq (2 n² + 2 dq²) →
        -(del k) ≤ cutCR cd k ⬝ᵥ (z - Cat (n·n) 0 cd k)

Two features make this *not* a pointwise condition:

* `Cat (n·n) 0 cd k` is `stepCentre` iterated `k` times from `0` — a function of the whole prefix
  `cd 0, …, cd (k-1)` of the transcript, **not** of anything the round's state records;
* `Cat` moves by `(γ(ρ_k)/√σ_k) • p_k` where `γ(ρ) = (1-ρ)/(n+1)` — zero only at the single depth
  `ρ = 1`, which the halving slot `hhalve` (`rho0R N rmax > 1`, and `rho0R N 1 < 1` for `N ≥ 2`)
  excludes — and `√σ_k` is *irrational* in general.  (Theorems below carry `γ ≠ 0` as an explicit
  hypothesis, so nothing rests on that reading.)

The shelf's static separators (`QMCLeafB.RelaxOracle.relaxMem_or_cut`, and the zero-margin
`QMCLeafB.ZeroMarginCut.relaxMem_or_cut0` the campaigns actually use) are stated at the **round's own
centre** `cX k`:

    Cut0.separates_flat : ∀ z, relaxBodyLE A u δ (unflat z) →
      0 ≤ flatQ normal ⬝ᵥ (z - flat (castMat cX))

So the composition needs a bridge — two identifications of the transcript:

  **`hcutΔ`** = `(hnorm) : (cd k).c = flatQ (C k).normal`  ∧  `(hctr) : Cat k = flat (castMat (cX k))`.

What this file machine-checks, in order:

* §1 `hcut_of_cut0_family` — **`hcutΔ` ⟹ `RunParts.hcut` verbatim**, plus the campaign
  instantiation `hcut_of_cut0_family_campaign` at `wMatrixQ G` / `t - Rq/40000` / `dq`.  So the
  composition *does* exist; the question is what `hcutΔ` costs.
* §2 `hcut_of_emptyBody` — at an empty body `hcut` is vacuous for **any** transcript: no pairing, no
  `hctr`, no trajectory constraint.  That is the only stratum where the class is free.
* §3 `Cat_one` + `hctr_one_forces_square` — **the cost of `hctr`, exactly.**  Already at `k = 1`,
  `hctr` forces the first round's `σ₀ = c₀ ⬝ p₀` to be a **square in ℚ**.  This is not a technical
  artefact: `Cat 1 = (γ(ρ₀)/√σ₀) • p₀` with `p₀ ≠ 0`, so every component of `Cat 1` is rational only
  if `√σ₀` is.
* §4 `not_hctr_initShape_two` — a **genuine failing trajectory**: at the engine's own init shape
  `initShapeOf 4 M`, the coordinate normal `e₀` and its exact witness `p₀ = M • e₀` give
  `σ₀ = M`; at `M = 2` the witness relation `Aat 0 p₀ = c₀` holds (`hwit_initShape`) and `√2` is
  irrational, so **no** rational centre can satisfy `hctr` at `k = 1`.  Hence the static separators
  do *not* compose with a generic trajectory — `hctr` is a real constraint on the chosen normals
  (`σ₀` must be a perfect square), i.e. a **trajectory design axiom**, not a free bridge.
* §5 `exists_hcut_round_zero` — the opposite receipt: at a **nonempty** body the all-false class
  does have a legal first round (`del = 0`, the diagonal normal at the forced centre `0`,
  `z₀₀ ≥ 1 - δ/4 > 0`).  So the class is **not** restricted to empty bodies.
* §7 `le_del_of_interior` / `eq_zero_of_interior_zero_del` — **the necessity half**: if the
  accumulated centre is an interior point of the body (a ball of radius `ε` around it lies in the
  body), then the round's margin is forced up to `ε·S/(2(1+S))`, `S = ∑ cᵢ²`; at `del = 0` no nonzero
  normal survives.  So the pairing really is a condition on the accumulated-centre path.

* §1b `hcut_of_cut0_family_enclosure` — **the patch.**  The exact identification is not needed:
  the strictly weaker *signed enclosure* inequality

      henc : -del k ≤ c_k ⬝ (flat (castMat (cX k)) - Cat k)

  (the accumulated centre lies on the body's side of the round's cut hyperplane, up to the margin
  the round already declares) gives `hcut` with the same `del`, by one telescoping identity
  (`dotProduct_sub_split`).  `hctr` is the `del = 0` special case (`enclosure_of_hctr`), and
  `hcheck` prices the enclosure budget at `del k ≤ ρ_k √σ_k` — the round's own absolute margin.
  No square-σ condition, no lattice condition: **budget the margin, do not identify the centre.**

* §8 `allFalseParts` / `allFalsePartsOfCuts` — the class **assembled**: with `ok ≡ false` the
  `hcert` slot is vacuous and the verdict slot is the bit equation `o G t = false`, so the class is
  exactly the nine engine slots, and `allFalsePartsOfCuts` discharges the crux slot from a static
  `Cut0` family plus the enclosure inequality of §1b.

**Verdict.**  *Not* "only at empty bodies".  The all-false record class composes at every stratum:

* empty body — `hcut` vacuous, any transcript (§2);
* every body — round `0` is free (§5);
* nonempty body, later rounds — `hcut` holds exactly when the transcript keeps the accumulated centre
  within the round's margin of the round's cut hyperplane (`henc`), which is a statement about the
  *trajectory*, not about the body.

The exact-centre bridge `hctr` (the one the shelf's `hcutδ_of_relaxCuts` / `ZeroMarginCut` interface
uses) is sufficient but **generically false**: it forces every recorded `σ_k` to be a perfect square
in ℚ, and the natural first move already violates it (§3, §4).  So the residual of the all-false
class is *not* a body condition and *not* a square-class arithmetic condition — it is the enclosure
budget, which is the one thing a dyadic rational trajectory is built to dominate.

No `sorry`, no `axiom`, no `native_decide`; axiom audits at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.CruxM1

open QMCLeafB.EngineIterates
open QMCLeafB.ZeroMarginCut

/-! ## 1.  `hcutΔ` ⟹ `RunParts.hcut`, verbatim

The two identifications of the transcript, and nothing else.  `A` is the rational weight matrix
(`wMatrixQ G`, whose cast is `wMatrix G` by `HemptyR_M3.castMat_wMatrixQ`), `u = t - Rq/40000`,
`δ = dq`, `M = 2n² + 2dq²`, `T = K·m`. -/

/-- The flattening of a rational matrix is the cast of `flatQ`. -/
theorem flat_castMat_eq (n : ℕ) (cX : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat cX)
      = fun k => ((QMCLeafB.RelaxOracle.flatQ cX k : ℚ) : ℝ) := by
  funext k
  rw [QMCLeafB.AnswerProducer.flat, QMCLeafB.RelaxOracle.flatQ,
    QMCLeafB.SepOracle.castMat_apply]

/-- **The composition, in `RunParts.hcut`'s own shape.**  From a family of zero-margin (central)
cuts at the round's own centres, the recorded normal identification `hnorm` and the accumulated
centre identification `hctr`, the transcript-level separation holds with `del k = 0`. -/
theorem hcut_of_cut0_family {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {M : ℝ}
    (ok : ℕ → Bool) (T : ℕ) (cX : ℕ → Matrix (Fin n) (Fin n) ℚ)
    (C : ∀ k, ok k = false → QMCLeafB.ZeroMarginCut.Cut0 A (cX k) u δ)
    (cd : ℕ → CutData (n * n)) (del : ℕ → ℚ)
    (hnorm : ∀ k (hok : ok k = false),
      (cd k).c = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hctr : ∀ k, QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
      = QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
    (hdel : ∀ k, del k = 0) :
    ∀ k, k < T → ok k = false → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
        ((δ : ℚ) : ℝ) M →
      -(((del k : ℚ)) : ℝ) ≤
        QMCLeafB.EngineIterates.cutCR cd k ⬝ᵥ
          (z - QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k) := by
  intro k _ hok z hz
  have h := (C k hok).separates_flat z hz.1
  have hcut : QMCLeafB.EngineIterates.cutCR cd k
      = fun i => (((QMCLeafB.RelaxOracle.flatQ (C k hok).normal) i : ℚ) : ℝ) := by
    funext i
    simp only [QMCLeafB.EngineIterates.cutCR, hnorm k hok]
  rw [hcut, hctr k, hdel k]
  simpa using h

/-- **The same bridge instantiated at the campaign's own data**: `wMatrixQ G`, level `t - Rq/40000`,
tolerance `dq`, norm bound `2n² + 2dq²`, `T = K·m`.  This is `RunParts.hcut` with
`A := wMatrix G` face to face. -/
theorem hcut_of_cut0_family_campaign {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (ok : ℕ → Bool) (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.ZeroMarginCut.Cut0 (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq)
    (cd : ℕ → CutData (G.n * G.n)) (del : ℕ → ℚ)
    (hnorm : ∀ k (hok : ok k = false),
      (cd k).c = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hctr : ∀ k, QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k
      = QMCLeafB.AnswerProducer.flat
          (QMCLeafB.SepOracle.castMat (cX k)))
    (hdel : ∀ k, del k = 0) :
    ∀ k, k < P.K * P.m → ok k = false → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) (P.dq : ℝ)
        (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ) →
      -(((del k : ℚ)) : ℝ) ≤
        QMCLeafB.EngineIterates.cutCR cd k ⬝ᵥ
          (z - QMCLeafB.EngineIterates.Cat (G.n * G.n)
            (0 : Fin (G.n * G.n) → ℝ) cd k) := by
  intro k hk hok z hz
  have hu : (((t - QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
      = (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
    push_cast
    ring
  refine hcut_of_cut0_family (A := QMCLeafB.Finalization.wMatrixQ G)
    (u := t - QMCLeafB.EngineRuntime.Rq G / 40000) (δ := P.dq)
    (M := (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ)) ok (P.K * P.m) cX C cd del
    hnorm hctr hdel k hk hok z ?_
  rw [QMCLeafB.HemptyR_M3.castMat_wMatrixQ, hu]
  exact hz

/-! ## 1b.  The *enclosure* bridge: `hctr` is the wrong condition, `del` is the right slack

The exact identification `Cat k = flat (castMat (cX k))` is only one way to pass from a static
separator to `hcut`.  The other, strictly weaker, one costs nothing but the round's own margin:

    c_k ⬝ (flat (cX k) - Cat k) ≥ -(del k)          (`enclosure`)

i.e. the *accumulated* centre lies on the body's side of the round's cut hyperplane, up to the
margin the round already declares.  Then

    c_k ⬝ (z - Cat k) = c_k ⬝ (z - flat cX_k) + c_k ⬝ (flat cX_k - Cat k) ≥ 0 - del k

and this is `hcut`.  The margin is not free: `hcheck` bounds it by `ρ_k √σ_k`, so the enclosure
budget is exactly the round's absolute cut margin — the quantity the engine's own dyadic state is
built to dominate.  **This is the patch: budget the margin, do not identify the centre.** -/

/-- The dot product splits along the telescoping difference of three points. -/
theorem dotProduct_sub_split {N : ℕ} (v z a b : Fin N → ℝ) :
    v ⬝ᵥ (z - b) = v ⬝ᵥ (z - a) + v ⬝ᵥ (a - b) := by
  rw [← dotProduct_add]
  congr 1
  funext i
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- **The enclosure bridge, in `RunParts.hcut`'s own shape.**  Same data as
`hcut_of_cut0_family`, but the centre identification is replaced by the signed enclosure inequality
against the round's margin `del k`.  (`del` is *not* required to vanish.) -/
theorem hcut_of_cut0_family_enclosure {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {M : ℝ}
    (ok : ℕ → Bool) (T : ℕ) (cX : ℕ → Matrix (Fin n) (Fin n) ℚ)
    (C : ∀ k, ok k = false → QMCLeafB.ZeroMarginCut.Cut0 A (cX k) u δ)
    (cd : ℕ → CutData (n * n)) (del : ℕ → ℚ)
    (hnorm : ∀ k (hok : ok k = false),
      (cd k).c = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (henc : ∀ k (hok : ok k = false),
      -(((del k : ℚ)) : ℝ) ≤
        (fun i => (((QMCLeafB.RelaxOracle.flatQ (C k hok).normal) i : ℚ) : ℝ)) ⬝ᵥ
          (QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))
            - QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k)) :
    ∀ k, k < T → ok k = false → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
        ((δ : ℚ) : ℝ) M →
      -(((del k : ℚ)) : ℝ) ≤
        QMCLeafB.EngineIterates.cutCR cd k ⬝ᵥ
          (z - QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k) := by
  intro k _ hok z hz
  have h0 := (C k hok).separates_flat z hz.1
  have h1 := henc k hok
  have hcut : QMCLeafB.EngineIterates.cutCR cd k
      = fun i => (((QMCLeafB.RelaxOracle.flatQ (C k hok).normal) i : ℚ) : ℝ) := by
    funext i
    simp only [QMCLeafB.EngineIterates.cutCR, hnorm k hok]
  rw [hcut]
  rw [dotProduct_sub_split (fun i => (((QMCLeafB.RelaxOracle.flatQ (C k hok).normal) i : ℚ) : ℝ))
    z (QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
    (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k)]
  linarith

/-- **The enclosure bridge at the campaign's own data** (`wMatrixQ G`, level `t - Rq/40000`,
tolerance `dq`, norm bound `2n² + 2dq²`, `T = K·m`): `RunParts.hcut` with `A := wMatrix G`. -/
theorem hcut_of_cut0_family_campaign_enclosure {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (ok : ℕ → Bool) (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.ZeroMarginCut.Cut0 (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq)
    (cd : ℕ → CutData (G.n * G.n)) (del : ℕ → ℚ)
    (hnorm : ∀ k (hok : ok k = false),
      (cd k).c = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (henc : ∀ k (hok : ok k = false),
      -(((del k : ℚ)) : ℝ) ≤
        (fun i => (((QMCLeafB.RelaxOracle.flatQ (C k hok).normal) i : ℚ) : ℝ)) ⬝ᵥ
          (QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))
            - QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k)) :
    ∀ k, k < P.K * P.m → ok k = false → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) (P.dq : ℝ)
        (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ) →
      -(((del k : ℚ)) : ℝ) ≤
        QMCLeafB.EngineIterates.cutCR cd k ⬝ᵥ
          (z - QMCLeafB.EngineIterates.Cat (G.n * G.n)
            (0 : Fin (G.n * G.n) → ℝ) cd k) := by
  intro k hk hok z hz
  have hu : (((t - QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
      = (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
    push_cast
    ring
  refine hcut_of_cut0_family_enclosure (A := QMCLeafB.Finalization.wMatrixQ G)
    (u := t - QMCLeafB.EngineRuntime.Rq G / 40000) (δ := P.dq)
    (M := (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ)) ok (P.K * P.m) cX C cd del
    hnorm henc k hk hok z ?_
  rw [QMCLeafB.HemptyR_M3.castMat_wMatrixQ, hu]
  exact hz

/-- **The two bridges are nested**: the exact identification `hctr` is the special case
`del = 0` of the enclosure inequality.  So `hcut_of_cut0_family` is `hcut_of_cut0_family_enclosure`
with a stronger, and (see §3/§4) generically unattainable, hypothesis. -/
theorem enclosure_of_hctr {n : ℕ} (cd : ℕ → CutData (n * n))
    (cX : ℕ → Matrix (Fin n) (Fin n) ℚ) (del : ℕ → ℚ) (hdel : ∀ k, del k = 0)
    (hctr : ∀ k, QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
      = QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) :
    ∀ k (Nv : Fin (n * n) → ℝ),
      -(((del k : ℚ)) : ℝ) ≤
        Nv ⬝ᵥ (QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))
          - QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k) := by
  intro k Nv
  rw [hctr k, sub_self, hdel k]
  simp

/-- **The enclosure budget is the round's absolute margin.**  `hcheck` (`del² ≤ ρ²σ`) plus
`margin_le_of_sq_check` bound the enclosure error the trajectory is allowed at round `k` by
`ρ_k √σ_k`; that is exactly what `RunParts.hle` (`ρ ≤ rmax`) and the depth parameter control. -/
theorem enclosure_budget {δ ρ σ : ℚ} (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (h : δ ^ 2 ≤ ρ ^ 2 * σ) : (δ : ℝ) ≤ (ρ : ℝ) * Real.sqrt ((σ : ℚ) : ℝ) :=
  QMCLeafB.EngineIterates.margin_le_of_sq_check hδ hρ hσ h

/-! ## 2.  The one stratum where `hcut` is free: the empty body -/

/-- **Empty body ⟹ `hcut` is vacuous**, for *any* transcript and *any* margin stream.  No pairing
with `Cat`, no `hctr`, no trajectory constraint: this is the only stratum at which the all-false
record class is unconditional. -/
theorem hcut_of_emptyBody {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {u δ M : ℝ}
    (hW : ∀ z : Fin (n * n) → ℝ,
      z ∉ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) u δ M)
    (cd : ℕ → CutData (n * n)) (del : ℕ → ℚ) (ok : ℕ → Bool) (T : ℕ) :
    ∀ k, k < T → ok k = false → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) u δ M →
      -(((del k : ℚ)) : ℝ) ≤
        QMCLeafB.EngineIterates.cutCR cd k ⬝ᵥ
          (z - QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k) :=
  fun k _ _ z hz => absurd hz (hW z)

/-! ## 3.  The cost of `hctr`: the accumulated centre at `k = 1`

`Cat (k+1) = Cat k + (γ(ρ_k)/√σ_k) • p_k` with `γ(ρ) = (1-ρ)/(n+1)`.  At `k = 1` the whole
transcript prefix is one round, so the identification `Cat 1 = flat (castMat cX)` is a statement
about `(γ(ρ₀)/√σ₀) • p₀` alone. -/

/-- The rational companion of `gammaR`, so that the rationality conclusion can be drawn in `ℚ`. -/
def gammaQ (N : ℕ) (ρ : ℚ) : ℚ := (1 - ρ) / ((N : ℚ) + 1)

theorem cast_gammaQ (N : ℕ) (ρ : ℚ) :
    ((gammaQ N ρ : ℚ) : ℝ) = gammaR N ((ρ : ℚ) : ℝ) := by
  rw [gammaQ, gammaR]
  push_cast
  ring

/-- **The accumulated centre after one round**, in closed form. -/
theorem Cat_one (N : ℕ) (cd : ℕ → CutData N) :
    QMCLeafB.EngineIterates.Cat N (0 : Fin N → ℝ) cd 1
      = (gammaR N ((cd 0).rho : ℝ) /
          sqrtSigmaR (cutCR cd 0) (cutPR cd 0)) • cutPR cd 0 := by
  rw [QMCLeafB.EngineIterates.Cat_unfold]
  simp only [QMCLeafB.EngineIterates.Cat, stepCentre, zero_add]

/-- **`hctr` at `k = 1` forces a rational square.**  If the accumulated engine centre after one
round is the flattening of a *rational* matrix, then the round's `σ₀ = c₀ ⬝ p₀` is a square in `ℚ`.

Hence `hctr` is not a bookkeeping bridge: it is an arithmetic condition on the recorded normal
(modulo squares: scaling `c` by `λ ∈ ℚ` multiplies `σ` by `λ²`, so the condition is a condition on
the projective normal only). -/
theorem hctr_one_forces_square {n : ℕ} (cd : ℕ → CutData (n * n))
    (cX : Matrix (Fin n) (Fin n) ℚ)
    (hσ : 0 < QMCLeafB.EngineIterates.sigmaQ (cd 0).c (cd 0).p)
    (hγ : gammaR (n * n) ((cd 0).rho : ℝ) ≠ 0)
    (h : QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd 1
      = QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat cX)) :
    IsSquare (QMCLeafB.EngineIterates.sigmaQ (cd 0).c (cd 0).p) := by
  classical
  have hσR : (0 : ℝ) < sigmaR (cutCR cd 0) (cutPR cd 0) := by
    rw [← QMCLeafB.EngineIterates.cast_sigmaQ]
    exact_mod_cast hσ
  have hsqrt : sqrtSigmaR (cutCR cd 0) (cutPR cd 0) ≠ 0 := by
    simp only [sqrtSigmaR]
    exact (Real.sqrt_pos.mpr hσR).ne'
  have hp : (cd 0).p ≠ 0 := by
    intro hp0
    have hz : QMCLeafB.EngineIterates.sigmaQ (cd 0).c (cd 0).p = 0 := by
      simp [QMCLeafB.EngineIterates.sigmaQ, hp0]
    rw [hz] at hσ
    exact lt_irrefl (0 : ℚ) hσ
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hp
  have h1 : QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd 1 i
      = (gammaR (n * n) ((cd 0).rho : ℝ) /
          sqrtSigmaR (cutCR cd 0) (cutPR cd 0)) * ((cd 0).p i : ℝ) := by
    rw [Cat_one]
    simp [Pi.smul_apply, cutPR]
  have hcomp : (gammaR (n * n) ((cd 0).rho : ℝ) /
        sqrtSigmaR (cutCR cd 0) (cutPR cd 0)) * ((cd 0).p i : ℝ)
      = ((QMCLeafB.RelaxOracle.flatQ cX i : ℚ) : ℝ) := by
    rw [← h1, h, flat_castMat_eq]
  have hir : ((cd 0).p i : ℝ) ≠ 0 := by exact_mod_cast hi
  have hrne : ((QMCLeafB.RelaxOracle.flatQ cX i : ℚ) : ℝ) ≠ 0 := by
    rw [← hcomp]
    exact mul_ne_zero (div_ne_zero hγ hsqrt) hir
  have hsqrt_eq : sqrtSigmaR (cutCR cd 0) (cutPR cd 0)
      = gammaR (n * n) ((cd 0).rho : ℝ) * ((cd 0).p i : ℝ) /
        ((QMCLeafB.RelaxOracle.flatQ cX i : ℚ) : ℝ) := by
    have hmul := congrArg
      (fun x : ℝ => x * sqrtSigmaR (cutCR cd 0) (cutPR cd 0)) hcomp
    simp only [div_mul_eq_mul_div, div_mul_cancel₀ _ hsqrt] at hmul
    rw [eq_div_iff hrne]
    rw [mul_comm (sqrtSigmaR (cutCR cd 0) (cutPR cd 0))]
    exact hmul.symm
  have hσeq : ((QMCLeafB.EngineIterates.sigmaQ (cd 0).c (cd 0).p : ℚ) : ℝ)
      = sqrtSigmaR (cutCR cd 0) (cutPR cd 0) ^ 2 := by
    rw [QMCLeafB.EngineIterates.cast_sigmaQ]
    exact (Real.sq_sqrt hσR.le).symm
  have hsq : ((QMCLeafB.EngineIterates.sigmaQ (cd 0).c (cd 0).p : ℚ) : ℝ)
      = (gammaR (n * n) ((cd 0).rho : ℝ) * ((cd 0).p i : ℝ) /
          ((QMCLeafB.RelaxOracle.flatQ cX i : ℚ) : ℝ)) ^ 2 := by
    rw [hσeq, hsqrt_eq]
  refine ⟨gammaQ (n * n) (cd 0).rho * (cd 0).p i / QMCLeafB.RelaxOracle.flatQ cX i, ?_⟩
  have hfin : (((gammaQ (n * n) (cd 0).rho * (cd 0).p i /
        QMCLeafB.RelaxOracle.flatQ cX i) ^ 2 : ℚ) : ℝ)
      = ((QMCLeafB.EngineIterates.sigmaQ (cd 0).c (cd 0).p : ℚ) : ℝ) := by
    rw [hsq]
    push_cast
    rw [cast_gammaQ]
  have hfin' : (gammaQ (n * n) (cd 0).rho * (cd 0).p i /
        QMCLeafB.RelaxOracle.flatQ cX i) ^ 2
      = QMCLeafB.EngineIterates.sigmaQ (cd 0).c (cd 0).p := by
    exact_mod_cast hfin
  simpa [pow_two] using hfin'.symm

/-! ## 4.  A genuine failing trajectory: the coordinate cut at the engine's own init shape

The engine's init shape is `initShapeOf N M = M⁻¹ • 1`, so the exact witness of the coordinate
normal `e₀` is `p₀ = M • e₀` and `σ₀ = M`.  That record satisfies `RunParts.hwit` at `k = 0`
(`hwit_initShape`), and at `M = 2` it violates `hctr` at `k = 1` outright (`√2 ∉ ℚ`).  So the
static-separator bridge is **not** available for a generic trajectory: `hctr` restricts the recorded
normals to the square-`σ` class. -/

/-- The coordinate normal `e₀` in `ℚ⁴`. -/
def e0 : Fin 4 → ℚ := fun i => if i = 0 then 1 else 0

/-- The failing trajectory: one recorded cut, normal `e₀`, exact witness `M • e₀`, depth `0`. -/
def coordCd (M : ℚ) : ℕ → CutData 4 := fun _ => ⟨e0, M • e0, 0⟩

/-- The record satisfies the engine's witness relation at `k = 0` against the init shape. -/
theorem hwit_initShape (M : ℚ) (hM : M ≠ 0) :
    QMCLeafB.EngineIterates.Aat 4 (QMCLeafB.Boundary.initShapeOf 4 M) (coordCd M) 0
        *ᵥ (coordCd M 0).p
      = (coordCd M 0).c := by
  show QMCLeafB.Boundary.initShapeOf 4 M *ᵥ (M • e0) = e0
  rw [QMCLeafB.Boundary.initShapeOf, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul,
    inv_mul_cancel₀ hM, one_smul]

/-- The recorded `σ` is exactly the init radius `M`. -/
theorem sigmaQ_coord (M : ℚ) :
    QMCLeafB.EngineIterates.sigmaQ (coordCd M 0).c (coordCd M 0).p = M := by
  simp [QMCLeafB.EngineIterates.sigmaQ, coordCd, e0, dotProduct]

/-- **`hctr` fails at `k = 1` on a genuine trajectory.**  At the init shape with `M = 2`, the
coordinate record satisfies `hwit` and depth `0`, yet no rational centre can be the accumulated
engine centre after one round: `Cat 1 = (γ/√2) • (2 e₀) = (√2/5) e₀` is irrational. -/
theorem not_hctr_initShape_two :
    ¬ ∃ cX : Matrix (Fin 2) (Fin 2) ℚ,
      QMCLeafB.EngineIterates.Cat 4 (0 : Fin 4 → ℝ) (coordCd 2) 1
        = QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat cX) := by
  rintro ⟨cX, hcX⟩
  have hσ : 0 < QMCLeafB.EngineIterates.sigmaQ (coordCd 2 0).c (coordCd 2 0).p := by
    rw [sigmaQ_coord]
    norm_num
  have hγ : gammaR (2 * 2) (((coordCd 2) 0).rho : ℝ) ≠ 0 := by
    simp only [coordCd]
    rw [gammaR]
    norm_num
  have hsq := hctr_one_forces_square (n := 2) (coordCd 2) cX hσ hγ hcX
  rw [sigmaQ_coord] at hsq
  obtain ⟨q, hq⟩ := hsq
  have hqR : (q : ℝ) * (q : ℝ) = 2 := by exact_mod_cast hq.symm
  have hsqeq : (q : ℝ) ^ 2 = (Real.sqrt 2) ^ 2 := by
    rw [sq, hqR, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsqeq with h | h
  · exact (irrational_sqrt_two.ne_rat q) h.symm
  · refine (irrational_sqrt_two.ne_rat (-q)) ?_
    have hcast : ((-q : ℚ) : ℝ) = -((q : ℚ) : ℝ) := by push_cast; ring
    rw [hcast, h]
    ring

/-! ## 5.  The class is *not* empty-body-only: round `0` is free at every body

`Cat N 0 cd 0 = 0` for every transcript, so `hctr` holds at `k = 0` with the **zero** centre — and
the zero matrix is never a `RelaxMem` member (`|0 - 1| ≤ δ/4` fails for `δ < 4`), so the separator
branch is taken: the coordinate normal `e₀e₀ᵀ` separates the whole relaxation from the origin because
every body point has `z₀₀ ≥ 1 - δ/4 > 0`.  Hence at a **nonempty** body the all-false class has a
legal first round (`del 0 = 0`), and nothing about empty bodies is needed. -/

/-- The accumulated centre at `k = 0` is the origin, whatever the transcript. -/
theorem Cat_zero (n : ℕ) (cd : ℕ → CutData (n * n)) :
    QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd 0 = 0 := rfl

/-- The flattening of the zero matrix is the origin. -/
theorem flat_zero (n : ℕ) :
    QMCLeafB.AnswerProducer.flat
      (QMCLeafB.SepOracle.castMat (0 : Matrix (Fin n) (Fin n) ℚ)) = 0 := by
  funext k
  simp [QMCLeafB.AnswerProducer.flat, QMCLeafB.SepOracle.castMat_apply]

/-- `hctr` at `k = 0` is automatic, with the zero centre. -/
theorem hctr_zero (n : ℕ) (cd : ℕ → CutData (n * n)) :
    QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd 0
      = QMCLeafB.AnswerProducer.flat
          (QMCLeafB.SepOracle.castMat (0 : Matrix (Fin n) (Fin n) ℚ)) := by
  rw [Cat_zero, flat_zero]

/-- **Round `0` of the all-false class, at an arbitrary body**: there is a zero-margin cut through
the accumulated centre `Cat 0 = 0` whose normal separates the whole relaxation.  With `δ < 4` the
diagonal branch applies at the zero centre; no emptiness, no size condition on the body. -/
theorem exists_hcut_round_zero {n : ℕ} (hn : 0 < n)
    {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {M : ℝ}
    (hδ4 : δ < 4) :
    ∃ C : QMCLeafB.ZeroMarginCut.Cut0 A (0 : Matrix (Fin n) (Fin n) ℚ) u δ,
      ∀ z : Fin (n * n) → ℝ,
        z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
          ((δ : ℚ) : ℝ) M →
        0 ≤ (fun k => ((QMCLeafB.RelaxOracle.flatQ C.normal k : ℚ) : ℝ)) ⬝ᵥ
              (z - QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ)
                (fun _ => ⟨0, 0, 0⟩) 0) := by
  have hdiag : δ / 4 < |(0 : Matrix (Fin n) (Fin n) ℚ) ⟨0, hn⟩ ⟨0, hn⟩ - 1| := by
    rw [Matrix.zero_apply, zero_sub, abs_neg, abs_one]
    linarith
  refine ⟨QMCLeafB.ZeroMarginCut.diagCut0 (A := A)
    (cX := (0 : Matrix (Fin n) (Fin n) ℚ)) (u := u) (δ := δ) ⟨0, hn⟩ hdiag, ?_⟩
  intro z hz
  have h := (QMCLeafB.ZeroMarginCut.diagCut0 (A := A)
    (cX := (0 : Matrix (Fin n) (Fin n) ℚ)) (u := u) (δ := δ) ⟨0, hn⟩ hdiag).separates_flat z hz.1
  rw [Cat_zero]
  rw [flat_zero] at h
  exact h

/-! ## 7.  The necessity half: the pairing forbids interior accumulated centres

`hcut` is not merely *served* by an enclosure (1b) — it *forces* one.  If the accumulated centre is
an interior point of the body, the body contains a point in the `-c` direction at distance `t`, so
the round's margin must be at least `t·‖c‖²`: the pairing is a **quantitative condition on the
accumulated centre**, and at `del = 0` it is unsatisfiable for every nonzero normal. -/

/-- **Interior accumulated centres cost margin.**  If a Euclidean ball of radius `ε` around `a` lies
in the body `W`, then any cut with normal `c` and margin `del` that contains `W` must have
`del ≥ ε·S/(2(1+S))`, `S = ∑ cᵢ²`.  (The point used is `a - t•c` with `t = ε/(2(1+S))`.) -/
theorem le_del_of_interior {N : ℕ} {W : Set (Fin N → ℝ)} {a c : Fin N → ℝ} {del ε : ℝ}
    (hε : 0 < ε) (hS : 0 < ∑ i, c i ^ 2)
    (hball : ∀ z : Fin N → ℝ, ∑ i, (z i - a i) ^ 2 < ε ^ 2 → z ∈ W)
    (hcut : ∀ z, z ∈ W → -del ≤ c ⬝ᵥ (z - a)) :
    ε * (∑ i, c i ^ 2) / (2 * (1 + ∑ i, c i ^ 2)) ≤ del := by
  set S : ℝ := ∑ i, c i ^ 2 with hSdef
  set t : ℝ := ε / (2 * (1 + S)) with htdef
  have h1S : (0 : ℝ) < 1 + S := by linarith
  have htpos : 0 < t := by rw [htdef]; positivity
  have hz : (fun i => a i - t * c i) ∈ W := by
    apply hball
    have hsum : ∑ i, ((fun i => a i - t * c i) i - a i) ^ 2 = t ^ 2 * S := by
      rw [hSdef, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    have htS : t ^ 2 * S < ε ^ 2 := by
      have hfac : S / (1 + S) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith
      have hkey : t ^ 2 * S = ε ^ 2 / 4 * (S / (1 + S) ^ 2) := by
        rw [htdef]; field_simp; ring
      have hε2 : (0:ℝ) < ε ^ 2 := by positivity
      rw [hkey]
      nlinarith
    rw [hsum]
    exact htS
  have hdot : c ⬝ᵥ ((fun i => a i - t * c i) - a) = -(t * S) := by
    rw [dotProduct, hSdef, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.sub_apply]
    ring
  have h := hcut _ hz
  rw [hdot] at h
  have htS : t * S = ε * S / (2 * (1 + S)) := by
    rw [htdef]
    field_simp
  rw [htS] at h
  linarith

/-- **At `del = 0` an interior accumulated centre admits no cut at all.**  So a round that both
satisfies `hcut` with zero margin and records a nonzero normal (`RunParts.hcne`) must have its
accumulated centre outside the body's interior. -/
theorem eq_zero_of_interior_zero_del {N : ℕ} {W : Set (Fin N → ℝ)} {a c : Fin N → ℝ}
    {ε : ℝ} (hε : 0 < ε)
    (hball : ∀ z : Fin N → ℝ, ∑ i, (z i - a i) ^ 2 < ε ^ 2 → z ∈ W)
    (hcut : ∀ z, z ∈ W → 0 ≤ c ⬝ᵥ (z - a)) : c = 0 := by
  by_contra hc
  have hS : 0 < ∑ i, c i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
    have hterm : 0 < c i ^ 2 := by
      rw [pow_two]
      exact mul_self_pos.mpr hi
    exact Finset.sum_pos' (fun j _ => sq_nonneg (c j)) ⟨i, Finset.mem_univ i, hterm⟩
  have h := le_del_of_interior (W := W) (a := a) (c := c) (del := 0) (ε := ε) hε hS hball
    (by simpa using hcut)
  have hpos : 0 < ε * (∑ i, c i ^ 2) / (2 * (1 + ∑ i, c i ^ 2)) := by positivity
  linarith

/-! ## 8.  The all-false record class, assembled

The deliverable for the hd family: the class as a `RunParts` builder.  With `ok ≡ false` every
`ok`-conditioned slot is vacuous and the verdict slot is free (`o G t = false` is exactly the
consistency condition), so the obligation list is the nine engine slots, of which the crux slot is
`hcut` — and §1b says `hcut` follows from a static `Cut0` plus the enclosure inequality. -/

/-- The all-`false` flag stream reports `anyOk = false`. -/
theorem anyOk_false : ∀ N : ℕ, QMCLeafB.SimLoop.anyOk (fun _ => false) N = false
  | 0 => rfl
  | (k + 1) => by
      rw [QMCLeafB.SimLoop.anyOk_succ]
      simp [anyOk_false k]

/-- **The all-false record class.**  Bit `o G t = false` plus the nine engine slots.  `hcert` is
vacuous; `hverdict` is the bit equation; everything else is the recorded transcript. -/
def allFalseParts {o : QuantumMaxCutEnergy.Input → ℚ → Bool} {G : QuantumMaxCutEnergy.Input}
    {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hbit : o G t = false)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (del : ℕ → ℚ)
    (hwit : ∀ k, k < P.K * P.m →
      QMCLeafB.EngineIterates.Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) cd k
        *ᵥ (cd k).p = (cd k).c)
    (hrho : ∀ k, k < P.K * P.m → 0 ≤ (cd k).rho)
    (hcne : ∀ k, k < P.K * P.m → (cd k).c ≠ 0)
    (hdel0 : ∀ k, k < P.K * P.m → 0 ≤ del k)
    (hcheck : ∀ k, k < P.K * P.m →
      (del k) ^ 2 ≤ ((cd k).rho) ^ 2 * QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p)
    (hle : ∀ k, k < P.K * P.m → (cd k).rho ≤ P.rmax)
    (hcut : ∀ k, k < P.K * P.m → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) (P.dq : ℝ)
        (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ) →
      -(((del k : ℚ)) : ℝ) ≤
        QMCLeafB.EngineIterates.cutCR cd k ⬝ᵥ
          (z - QMCLeafB.EngineIterates.Cat (G.n * G.n)
            (0 : Fin (G.n * G.n) → ℝ) cd k)) :
    QMCLeafB.FinalStroke.RunParts o G t P where
  ok := fun _ => false
  cd := cd
  del := del
  hcert := by
    intro k _ hok
    exact absurd hok (by simp)
  hwit := fun k hk _ => hwit k hk
  hrho := fun k hk _ => hrho k hk
  hcne := fun k hk _ => hcne k hk
  hdel0 := fun k hk _ => hdel0 k hk
  hcheck := fun k hk _ => hcheck k hk
  hle := fun k hk _ => hle k hk
  hcut := fun k hk _ => hcut k hk
  hverdict := by
    rw [hbit]
    exact (anyOk_false (P.K * P.m)).symm

/-- **The class, with the crux slot discharged by the enclosure bridge.**  Combining §1b and §8:
an all-false `RunParts` exists as soon as a zero-margin `Cut0` family at rational centres, together
with the enclosure inequality, is available at every round below the horizon. -/
def allFalsePartsOfCuts {o : QuantumMaxCutEnergy.Input → ℚ → Bool} {G : QuantumMaxCutEnergy.Input}
    {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hbit : o G t = false)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (C : ∀ k,
      QMCLeafB.ZeroMarginCut.Cut0 (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.EngineRuntime.Rq G / 40000) P.dq)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (del : ℕ → ℚ)
    (hnorm : ∀ k, (cd k).c = QMCLeafB.RelaxOracle.flatQ (C k).normal)
    (henc : ∀ k,
      -(((del k : ℚ)) : ℝ) ≤
        (fun i => (((QMCLeafB.RelaxOracle.flatQ (C k).normal) i : ℚ) : ℝ)) ⬝ᵥ
          (QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))
            - QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k))
    (hwit : ∀ k, k < P.K * P.m →
      QMCLeafB.EngineIterates.Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) cd k
        *ᵥ (cd k).p = (cd k).c)
    (hrho : ∀ k, k < P.K * P.m → 0 ≤ (cd k).rho)
    (hcne : ∀ k, k < P.K * P.m → (cd k).c ≠ 0)
    (hdel0 : ∀ k, k < P.K * P.m → 0 ≤ del k)
    (hcheck : ∀ k, k < P.K * P.m →
      (del k) ^ 2 ≤ ((cd k).rho) ^ 2 * QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p)
    (hle : ∀ k, k < P.K * P.m → (cd k).rho ≤ P.rmax) :
    QMCLeafB.FinalStroke.RunParts o G t P :=
  allFalseParts hbit cd del hwit hrho hcne hdel0 hcheck hle
    (fun k hk z hz =>
      hcut_of_cut0_family_campaign_enclosure (t := t) (P := P)
        (fun _ => false) cX (fun j _ => C j) cd del
        (fun j _ => hnorm j) (fun j _ => henc j) k hk rfl z hz)

/-! ## 9.  Axiom audit -/

#print axioms QMCLeafB.CruxM1.hcut_of_cut0_family
#print axioms QMCLeafB.CruxM1.hcut_of_cut0_family_campaign
#print axioms QMCLeafB.CruxM1.hcut_of_cut0_family_enclosure
#print axioms QMCLeafB.CruxM1.hcut_of_cut0_family_campaign_enclosure
#print axioms QMCLeafB.CruxM1.enclosure_of_hctr
#print axioms QMCLeafB.CruxM1.enclosure_budget
#print axioms QMCLeafB.CruxM1.hcut_of_emptyBody
#print axioms QMCLeafB.CruxM1.Cat_one
#print axioms QMCLeafB.CruxM1.hctr_one_forces_square
#print axioms QMCLeafB.CruxM1.hwit_initShape
#print axioms QMCLeafB.CruxM1.not_hctr_initShape_two
#print axioms QMCLeafB.CruxM1.hctr_zero
#print axioms QMCLeafB.CruxM1.exists_hcut_round_zero
#print axioms QMCLeafB.CruxM1.le_del_of_interior
#print axioms QMCLeafB.CruxM1.eq_zero_of_interior_zero_del
#print axioms QMCLeafB.CruxM1.allFalseParts
#print axioms QMCLeafB.CruxM1.allFalsePartsOfCuts

end QMCLeafB.CruxM1


