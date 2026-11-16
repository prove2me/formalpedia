-- Prove2me | Definitions.Def_DSDensity1246_Main_Supplement_predictor
-- name    : DSDensity1246_Main_Supplement_predictor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:24:14.381405+00:00
-- url     : https://prove2.me/theorems/b6beddbf-5ef2-40f7-a3ac-f1424130fc5a
-- title:
--   One-inclusion prediction and randomized prefix validation
-- statement:
--   Fix a hypothesis class H and list size ℓ. An orientation choice selects an ℓ-list orientation for each full unlabeled sequence. On training data plus a query x, the one-inclusion rule uses the indexed query edge matching every training label and outputs its selected query labels. An inconsistent fiber gives the empty list. Orientation choices carry no optimality or learning certificate.
--
--   For natural dimension d≥1, accuracy ε and confidence δ, define
--
--   $$n=4\left\lceil\frac{20(d+\log(6/\delta))}{\varepsilon}\right\rceil,\quad
--   R=\left\lceil\frac{\log(3/\delta)}{\log4}\right\rceil,\quad
--   v=\left\lceil\frac{12\log(3(R+1)/\delta)}{\varepsilon}\right\rceil.$$
--
--   Train R predictors on independently sampled prefix lengths from {n/4,…,n−1}, then select the predictor with the fewest mistakes on the next v independent validation observations. Ties retain the earliest candidate. A uniform real seed generates the R choices through the digits of a uniformly sampled integer with R base-(3n/4) digits. Surplus observations are ignored.
--
--   For d=0, the rule returns all labels realized by H at each point whenever these form a set of size at most ℓ, and otherwise returns the empty list. Deriving the size bound from dimension zero is a theorem obligation, not a defining assumption. This branch uses no observations.
--
--   **Formalization Note** The supplied sample becomes a list with repeated observations preserved. All operations are totalized on invalid parameters; guarantees apply only in the theorem's parameter ranges. No symmetry, density bound, or PAC accuracy is embedded as data in these definitions.
-- source:
--   Chirag Pabbaraju, STOC 2027 submission #1246 (October 2026), pp. 17–20, §5.1.1–§5.1.2; p. 13, Definition 2

import Definitions.Def_DSDensity1246_Main_Supplement_orientation
import Definitions.Def_DSDensity1246_Main_Supplement_learning
import Definitions.Def_MulticlassDS_Compress_Dimensions

set_option autoImplicit false

namespace DSDensity1246.Main.Supplement

/-- A choice of orientations for every full unlabeled sequence. Neither optimality
nor a learning guarantee is assumed as data. -/
def OrientationChoice (X Y : Type*) (ℓ : ℕ) (H : Set (X → Y)) :=
  (n : ℕ) → (S : Fin n → X) → ListOrientation ℓ (MulticlassDS.Compress.proj H S)

/-- §5.1.1, p.17: restrict to the training points plus query, use the indexed
edge matching all training labels, and return its selected query labels.
An inconsistent training fiber returns the empty list. -/
noncomputable def oneInclusionPredictor {X Y : Type*} {ℓ : ℕ} {H : Set (X → Y)}
    (C : OrientationChoice X Y ℓ H) (S : List (X × Y)) : ListPredictor X Y ℓ := by
  classical
  intro x
  let q : Fin (S.length + 1) := Fin.last S.length
  let xs : Fin (S.length + 1) → X := Fin.lastCases x (fun i => (S.get i).1)
  let a : {j : Fin (S.length + 1) // j ≠ q} → Y := fun j =>
    (S.get ⟨j.1.val, by
      have hj := j.1.isLt
      have hne : j.1.val ≠ S.length := by
        intro h
        apply j.2
        exact Fin.ext h
      omega⟩).2
  let W := MulticlassDS.Compress.proj H xs
  if h : (edge W q a).Nonempty then
    let e : OneInclusionEdge W := ⟨q, a, h⟩
    exact ⟨((C (S.length + 1) xs).selected e).image (fun w => w q),
      Finset.card_image_le.trans ((C (S.length + 1) xs).capacity e)⟩
  else exact ⟨∅, Nat.zero_le ℓ⟩

/-- Totalized zero-dimension rule: all labels realized at x, if they form a list
of size at most ℓ; otherwise empty. The theorem, not this definition, must
establish the size condition from dimension zero. -/
noncomputable def zeroDimensionPredictor {X Y : Type*} (ℓ : ℕ)
    (H : Set (X → Y)) : ListPredictor X Y ℓ := by
  classical
  intro x
  let L : Set Y := {y | ∃ h ∈ H, h x = y}
  if h : L.Finite then
    if hc : h.toFinset.card ≤ ℓ then exact ⟨h.toFinset, hc⟩
    else exact ⟨∅, Nat.zero_le ℓ⟩
  else exact ⟨∅, Nat.zero_le ℓ⟩

/-- Count validation mistakes, retaining repeated validation observations. -/
noncomputable def validationMistakes {X Y : Type*} {ℓ : ℕ}
    (V : List (X × Y)) (μ : ListPredictor X Y ℓ) : ℕ := by
  classical
  exact (V.filter (fun z => z.2 ∉ (μ z.1).1)).length

/-- pp.19–20: random prefixes followed by independent holdout validation.
With a uniform seed in [0,1), the base-k digits of floor(u k^R) give R independent
uniform prefix choices. Only the first n+v observations are used. The d=0
branch uses no sample. Invalid ε,δ have totalized but unused parameter values. -/
noncomputable def validatedLearner {X Y : Type*} {ℓ : ℕ} {H : Set (X → Y)}
    (d : ℕ) (C : OrientationChoice X Y ℓ H) : ListLearner X Y ℝ ℓ := by
  classical
  exact fun ε δ m S u =>
    if d = 0 then zeroDimensionPredictor ℓ H else
    let n : ℕ := 4 * ⌈20 * ((d : ℝ) + Real.log (6 / δ)) / ε⌉₊
    let R : ℕ := ⌈Real.log (3 / δ) / Real.log 4⌉₊
    let v : ℕ := ⌈12 * Real.log (3 * ((R : ℝ) + 1) / δ) / ε⌉₊
    let k : ℕ := 3 * n / 4
    let code : ℕ := ⌊u * ((k ^ R : ℕ) : ℝ)⌋₊
    let data := List.ofFn S
    let train := data.take n
    let V := (data.drop n).take v
    let B := oneInclusionPredictor C
    let candidates := (List.range R).map fun j =>
      B (train.take (n / 4 + (code / k ^ j) % k))
    candidates.foldl (fun best candidate =>
      if validationMistakes V candidate < validationMistakes V best then candidate else best)
      (candidates.headD (B []))

end DSDensity1246.Main.Supplement


