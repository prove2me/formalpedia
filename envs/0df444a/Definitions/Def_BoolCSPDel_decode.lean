-- Prove2me | Definitions.Def_BoolCSPDel_decode
-- name    : BoolCSPDel_decode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:33.320953+00:00
-- url     : https://prove2.me/theorems/c84c48a5-21cf-4c66-81ad-370aa750eb59
-- title:
--   Algorithms 3–7: decoding at one regularizer, as pure functions
-- statement:
--   Algorithm 7 computes $v_i\approx H^{-1}b_i$ by $r_{\mathrm{inv}}$ rounded iterations $v\leftarrow\mathrm{round}_{g_v}(v+U^{-1}(b_i-Hv))$. Algorithm 6 tests a row on a working sketch $Z$: with $q_i=b_i^\top v_i$ (failure if $q_i\le0$), estimates $\hat y_i,\hat\nu_i$ from $Zv_i$, it rejects unless $\hat y_i>0$ and $\hat y_i^2\ge2\vartheta(\hat\nu_i+\ell\|v_i\|_2^2)$, and returns $\hat z_i=\mathrm{round}_{g_a}(\hat y_i/q_i)$, with failure unless $0<\hat z_i\le W_{\max}$. Algorithm 4 prepares $Z_u=2^tY_{t,u}$ and adds the saved rows that left the sample. Algorithm 5 runs $T$ scans halving the saved rows still sampled. Algorithm 3 runs these at each level $t<T$, saves each nonzero unsaved row passing the test at threshold $\theta$ on $Z_T$, and fails if the final sample is nonempty. The stored sketches are $Y_{t,u}=\Phi_{t,u}\mathrm{diag}(f1_{E_t})B$. The seeds of one call are independent masks and pairs.
--
--   **Formalization Note** Failure is `none`. The check against $C_{\max}$ is on all working entries: line 1 of Algorithm 4 modifies every entry, and Claim A.24 bounds the copies not yet queried as well. Rounding ties go up, a fixed tie breaking. Algorithms 1 and 2 are not needed for Lemma A.3, as $Y_{t,u}$ is their end-of-stream value.
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), Algorithms 3–7, pp.49–53; p.48

import Mathlib
import Definitions.Def_BoolCSPDel_Params

open MeasureTheory

namespace BoolCSPDel

/-- **Algorithm 7, p.53 (computing `v_i`) as a pure function.** Bandekar, Sharma, Velusamy, STOC 2027
submission (manuscript sha256 15f83519…).

The row `b_i` over `ℚ`. -/
def rowQ {m D : ℕ} (B : Matrix (Fin m) (Fin D) ℤ) (i : Fin m) : Fin D → ℚ := fun c => (B i c : ℚ)

/-- `Hv = ℓv + Σ_a w_a b_{i_a}(b_{i_a}ᵀv)`, scanning the weighted row list (Algorithm 7, line 3). -/
def applyH {m D : ℕ} (B : Matrix (Fin m) (Fin D) ℤ) (ell : ℚ) (H : List (Fin m × ℚ))
    (v : Fin D → ℚ) : Fin D → ℚ :=
  ell • v + (H.map fun e => (e.2 * (rowQ B e.1 ⬝ᵥ v)) • rowQ B e.1).sum

/-- p.51: `round_g(x)`, a nearest multiple of `g`; ties go up (`round`), a fixed tie breaking. -/
def roundTo (g x : ℚ) : ℚ := g * (round (x / g) : ℚ)

/-- Algorithm 7, p.53: `v ← 0`; `r_inv` times, `v ← round_{g_v}(v + U⁻¹(b_i − Hv))`. `H` is given by
`ell` and the list of pairs (row, weight). -/
def computeV (P : Params) (B : Matrix (Fin P.m) (Fin P.D) ℤ) (ell : ℚ) (H : List (Fin P.m × ℚ))
    (i : Fin P.m) : Fin P.D → ℚ :=
  (fun v c => roundTo P.gv (v c + (1 / (P.U : ℚ)) * (rowQ B i c - applyH B ell H v c)))^[P.rinv] 0

/-- The outcome of a row test. -/
inductive TestResult : Type
  /-- The row is rejected. -/
  | reject
  /-- The test returns an estimated multiplier. -/
  | est (z : ℚ)
  /-- The test returns failure. -/
  | fail

/-- Algorithm 6, p.52: test a nonzero row with threshold `ϑ` on a working sketch pair `Z` with seed
`s`. -/
def testRow (P : Params) {Ωs : Type} (pair : SketchPair P.m Ωs) (B : Matrix (Fin P.m) (Fin P.D) ℤ)
    (ell : ℚ) (H : List (Fin P.m × ℚ)) (s : Ωs) (Z : Matrix (Fin pair.r) (Fin P.D) ℚ) (vartheta : ℚ)
    (i : Fin P.m) : TestResult :=
  let v := computeV P B ell H i
  let q := rowQ B i ⬝ᵥ v
  if q ≤ 0 then TestResult.fail else
  let yh := pair.coord s (Z.mulVec v) i
  let nu := pair.norm s (Z.mulVec v)
  if 0 < yh ∧ 2 * vartheta * (nu + ell * (v ⬝ᵥ v)) ≤ yh ^ 2 then
    let z := roundTo P.ga (yh / q)
    if 0 < z ∧ z ≤ P.Wmax then TestResult.est z else TestResult.fail
  else TestResult.reject

/-- A saved row: index `i`, level `c_i`, multiplier `â_i` (Algorithm 3, line 9). -/
structure Saved (m : ℕ) : Type where
  /-- The row. -/
  idx : Fin m
  /-- The level at which it was saved. -/
  level : ℕ
  /-- The estimated multiplier. -/
  mult : ℚ

/-- `i ∈ E_t` (Algorithm 2, line 4): all masks `ξ_s`, `s < t`, keep `i`. -/
def inSample {T m : ℕ} (masks : Fin T → Fin m → Bool) (t : ℕ) (i : Fin m) : Prop :=
  ∀ s : Fin T, s.1 < t → masks s i = true

instance {T m : ℕ} (masks : Fin T → Fin m → Bool) (t : ℕ) (i : Fin m) :
    Decidable (inSample masks t i) := by
  unfold inSample; infer_instance

/-- All the seeds of one decoding call: the masks `ξ_t` and the sketch seeds `(t, u)`. -/
abbrev Seeds (P : Params) (Ωs : Type) : Type :=
  (Fin P.T → Fin P.m → Bool) × (Fin P.T → Fin (P.T + 1) → Ωs)

/-- p.48: `Y_{t,u} = Φ_{t,u} diag(f 1_{E_t}) B`, the stored sketch at the end of the stream. -/
def storedY (P : Params) {Ωs : Type} (pair : SketchPair P.m Ωs) (B : Matrix (Fin P.m) (Fin P.D) ℤ)
    (f : Fin P.m → ℕ) (ω : Seeds P Ωs) (t : Fin P.T) (u : Fin (P.T + 1)) :
    Matrix (Fin pair.r) (Fin P.D) ℚ :=
  pair.Φ (ω.2 t u) *
    (Matrix.diagonal fun i => if inSample ω.1 t i then (f i : ℚ) else 0) * B.map (Int.cast : ℤ → ℚ)

/-- `(Φe_i)b_iᵀ`. -/
def colRow (P : Params) {Ωs : Type} (pair : SketchPair P.m Ωs) (B : Matrix (Fin P.m) (Fin P.D) ℤ)
    (s : Ωs) (i : Fin P.m) : Matrix (Fin pair.r) (Fin P.D) ℚ :=
  Matrix.vecMulVec (fun a => pair.Φ s a i) (rowQ B i)

/-- Working sketches `Z_0, …, Z_T` of one level. -/
abbrev Working (P : Params) {Ωs : Type} (pair : SketchPair P.m Ωs) : Type :=
  Fin (P.T + 1) → Matrix (Fin pair.r) (Fin P.D) ℚ

/-- The entry limit `C_max` holds on every working sketch.

**Formalization Note.** The page checks "any modified sketch entry"; line 1 of Algorithm 4 modifies
every entry and Claim A.24 bounds "this also … copies not yet queried", so Lean checks all entries. -/
def EntriesOK (P : Params) {Ωs : Type} {pair : SketchPair P.m Ωs} (Z : Working P pair) : Prop :=
  ∀ u a c, |Z u a c| ≤ (P.Cmax : ℚ)

instance (P : Params) {Ωs : Type} {pair : SketchPair P.m Ωs} (Z : Working P pair) :
    Decidable (EntriesOK P Z) := by
  unfold EntriesOK; infer_instance

/-- Algorithm 4, p.50: prepare the sketches at level `t`. Returns `Z_0, …, Z_T` and the integers
`d_i` (zero outside `F`), or failure (`none`). -/
def prepare (P : Params) {Ωs : Type} (pair : SketchPair P.m Ωs) (B : Matrix (Fin P.m) (Fin P.D) ℤ)
    (f : Fin P.m → ℕ) (ω : Seeds P Ωs) (t : Fin P.T) (F : List (Saved P.m)) :
    Option (Working P pair × (Fin P.m → ℕ)) :=
  let init : Working P pair × (Fin P.m → ℕ) :=
    (fun u => (2 : ℚ) ^ t.1 • storedY P pair B f ω t u, fun _ => 0)
  let res := F.foldl (fun (acc : Working P pair × (Fin P.m → ℕ)) e =>
    if inSample ω.1 t.1 e.idx then
      (acc.1, Function.update acc.2 e.idx (t.1 - e.level))
    else
      (fun u => acc.1 u + e.mult • colRow P pair B (ω.2 t u) e.idx,
        Function.update acc.2 e.idx 0)) init
  if EntriesOK P res.1 then some res else none

/-- One scan of Algorithm 5 (lines 2–8) on copy `u`: test each `i ∈ F` with `d_i > 0` against `Z_u`
at threshold `η`; on an estimate, subtract `(ẑ_i/2)(Φ_{t,v}e_i)b_iᵀ` from every `Z_v`, `v > u`, and
decrease `d_i`. -/
def scan (P : Params) {Ωs : Type} (pair : SketchPair P.m Ωs) (B : Matrix (Fin P.m) (Fin P.D) ℤ)
    (ell : ℚ) (H : List (Fin P.m × ℚ)) (ω : Seeds P Ωs) (t : Fin P.T) (F : List (Saved P.m))
    (u : Fin (P.T + 1)) (st : Working P pair × (Fin P.m → ℕ)) :
    Option (Working P pair × (Fin P.m → ℕ)) :=
  F.foldl (fun (acc : Option (Working P pair × (Fin P.m → ℕ))) e =>
    acc.bind fun cur =>
      if 0 < cur.2 e.idx then
        match testRow P pair B ell H (ω.2 t u) (cur.1 u) P.eta e.idx with
        | TestResult.fail => none
        | TestResult.reject => some cur
        | TestResult.est z =>
            some (fun v => if u < v then cur.1 v - (z / 2) • colRow P pair B (ω.2 t v) e.idx
                  else cur.1 v,
              Function.update cur.2 e.idx (cur.2 e.idx - 1))
      else some cur) (some st)

/-- Algorithm 5, p.51: `T` scans on `Z_0, …, Z_{T-1}`, with the limit check after each; failure if
some `d_i > 0` at the end. -/
def correct (P : Params) {Ωs : Type} (pair : SketchPair P.m Ωs) (B : Matrix (Fin P.m) (Fin P.D) ℤ)
    (ell : ℚ) (H : List (Fin P.m × ℚ)) (ω : Seeds P Ωs) (t : Fin P.T) (F : List (Saved P.m))
    (st : Working P pair × (Fin P.m → ℕ)) : Option (Working P pair) :=
  let res := (List.finRange P.T).foldl (fun (acc : Option (Working P pair × (Fin P.m → ℕ))) u =>
    acc.bind fun cur =>
      (scan P pair B ell H ω t F u.castSucc cur).bind fun nxt =>
        if EntriesOK P nxt.1 then some nxt else none) (some st)
  res.bind fun last => if ∃ e ∈ F, 0 < last.2 e.idx then none else some last.1

/-- Algorithm 3, lines 5–11: test every nonzero row outside `F` with `Z_T` at threshold `θ`, saving
each row with an estimate; failure if `|F| = M_max` when a row is to be added. -/
def select (P : Params) {Ωs : Type} (pair : SketchPair P.m Ωs) (B : Matrix (Fin P.m) (Fin P.D) ℤ)
    (ell : ℚ) (H : List (Fin P.m × ℚ)) (ω : Seeds P Ωs) (t : Fin P.T) (Z : Working P pair)
    (F : List (Saved P.m)) : Option (List (Saved P.m)) :=
  (List.finRange P.m).foldl (fun (acc : Option (List (Saved P.m))) i =>
    acc.bind fun cur =>
      if rowQ B i ≠ 0 ∧ ∀ e ∈ cur, e.idx ≠ i then
        match testRow P pair B ell H (ω.2 t (Fin.last P.T)) (Z (Fin.last P.T)) P.theta i with
        | TestResult.fail => none
        | TestResult.reject => some cur
        | TestResult.est a =>
            if cur.length = P.Mmax then none else some (cur ++ [⟨i, t.1, a⟩])
      else some cur) (some F)

/-- **Algorithm 3, p.49: decoding at regularizer `ℓ`.** `H` is given by `ℓ` and the list of (row,
weight) pairs. The stored sketches are those of `storedY`, so the frequency vector `f` enters only
through them. Returns the saved list `F`, or failure (`none`). -/
def decode (P : Params) {Ωs : Type} (pair : SketchPair P.m Ωs) (B : Matrix (Fin P.m) (Fin P.D) ℤ)
    (f : Fin P.m → ℕ) (ell : ℚ) (H : List (Fin P.m × ℚ)) (ω : Seeds P Ωs) :
    Option (List (Saved P.m)) :=
  ((List.finRange P.T).foldl (fun (acc : Option (List (Saved P.m))) t =>
    acc.bind fun F =>
      (prepare P pair B f ω t F).bind fun st =>
        (correct P pair B ell H ω t F st).bind fun Z =>
          select P pair B ell H ω t Z F) (some [])).bind fun F =>
    if ∃ i, inSample ω.1 P.T i then none else some F

/-- p.48: the law of the seeds of one call: the masks and all the pairs are mutually independent. -/
noncomputable def seedLaw (P : Params) {Ωs : Type} [MeasurableSpace Ωs] (ξ : PMF (Fin P.m → Bool))
    (ν : PMF Ωs) : Measure (Seeds P Ωs) :=
  (Measure.pi fun _ : Fin P.T => ξ.toMeasure).prod
    (Measure.pi fun _ : Fin P.T => Measure.pi fun _ : Fin (P.T + 1) => ν.toMeasure)

/-- `H = ℓI + Σ_r a_r² b_{i_r} b_{i_r}ᵀ` as a real matrix, for a list of (row, multiplier) pairs. -/
noncomputable def hMatrix {m D : ℕ} (B : Matrix (Fin m) (Fin D) ℤ) (ell : ℝ)
    (l : List (Fin m × ℚ)) : Matrix (Fin D) (Fin D) ℝ :=
  ell • (1 : Matrix (Fin D) (Fin D) ℝ) +
    (l.map fun e => ((e.2 : ℝ) ^ 2) • Matrix.vecMulVec (fun c => (B e.1 c : ℝ))
      (fun c => (B e.1 c : ℝ))).sum

/-- The hypotheses on `H` in Lemma A.3, p.55: `p ≤ M_max` and each `a_r ∈ (0, W_max]` is a multiple of
`g_a`. -/
def ValidRep (P : Params) (l : List (Fin P.m × ℚ)) : Prop :=
  l.length ≤ P.Mmax ∧ ∀ e ∈ l, 0 < e.2 ∧ e.2 ≤ P.Wmax ∧ ∃ n : ℤ, e.2 = n * P.ga

end BoolCSPDel


