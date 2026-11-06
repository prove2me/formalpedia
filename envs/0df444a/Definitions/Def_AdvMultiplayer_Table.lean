-- Prove2me | Definitions.Def_AdvMultiplayer_Table
-- name    : AdvMultiplayer_Table
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:52.622081+00:00
-- url     : https://prove2.me/theorems/9c31ce9d-215e-4f55-8223-cdfced587d8d
-- title:
--   The public table, its law and its sampler (Algorithm 9)
-- statement:
--   The public table is either the fixed-arm fallback flag or the construction data: an ID array $I_u(t)$, $(u,t)\in[A]\times[T]$, and $M$ complete rows. Row $q$ consists of forward bits $\varphi_q(u,t)$, scalars $V_{q,t,c}$ for the labels $c\in\{\mathrm{slot},\mathrm{sel},\mathrm{rec},\mathrm{fast},\mathrm{thin},\mathrm{prop}\}\cup\{\mathrm{tuple}_r,\mathrm{pilot}_r:0\le r<m\}\cup\{\mathrm{assign}_r:1\le r\le K+1\}$, and affine pairs $(c_{q,t,\sigma,i},b_{q,t,\sigma,i})$ for $\sigma\in\{\mathrm{DOWN},\mathrm{UP}\}$, $i\in[d]$.
--
--   Under the table law all coordinates are independent: $I_u(t)\sim\mathrm{Bernoulli}(1/2)$, $\varphi_q(u,t)\sim\mathrm{Bernoulli}(1-1/L_0)$, $V_{q,t,c}\sim\mathrm{Unif}([0,1))$, and the affine pairs are uniform on $\mathbb F_2^B\times\mathbb F_2$. Off the construction branch the law is the point mass on the fallback flag. The sampler is Algorithm 9, a program that reads one uniform draw per coordinate.
--
--   **Formalization Note.** Bernoulli laws are threshold tests of a uniform draw. The table law is defined as a product measure, independently of the sampler, so the statement that the sampler has this law has content.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, App. B.1, Algorithm 9, Table 4, pp.55-57

import Mathlib
import Definitions.Def_AdvMultiplayer_Size
import Definitions.Def_AdvMultiplayer_Strategy
import Definitions.Def_LNTopology_Hermetization_tick
import Definitions.Def_LNTopology_Hermetization_rlt

open MeasureTheory LNTopology.Hermetization

namespace AdvMultiplayer

/-- The scalar-coordinate labels `C_row` of App. B.1, p.56: the six labels
`slot, sel, rec, fast, thin, prop`, then `tuple_r` and `pilot_r` for `0 ≤ r < m`, and `assign_r` for
`1 ≤ r ≤ K+1`. There are `2m + K + 7` of them. -/
abbrev Coord (p : Size) := Fin 6 ⊕ (Fin p.m ⊕ (Fin p.m ⊕ Fin (p.K + 1)))

/-- The label `slot`. -/
def cSlot (p : Size) : Coord p := .inl 0
/-- The label `sel`. -/
def cSel (p : Size) : Coord p := .inl 1
/-- The label `rec`. -/
def cRec (p : Size) : Coord p := .inl 2
/-- The label `fast`. -/
def cFast (p : Size) : Coord p := .inl 3
/-- The label `thin`. -/
def cThin (p : Size) : Coord p := .inl 4
/-- The label `prop`. -/
def cProp (p : Size) : Coord p := .inl 5
/-- The label `tuple_r`. -/
def cTuple (p : Size) (r : Fin p.m) : Coord p := .inr (.inl r)
/-- The label `pilot_r`. -/
def cPilot (p : Size) (r : Fin p.m) : Coord p := .inr (.inr (.inl r))
/-- The label `assign_{r+1}`, `r = 0, …, K`. -/
def cAssign (p : Size) (r : Fin (p.K + 1)) : Coord p := .inr (.inr (.inr r))

/-- The ID array `I_u(t)`, `(u,t) ∈ [A]×[T]` (App. B.1, p.56). -/
abbrev IdArray (p : Size) := Fin p.A → Fin p.T → Bool

/-- The forward bits `φ_q(u,t)` of all rows (p.56). -/
abbrev FwdBits (p : Size) := Fin p.M → Fin p.A → Fin p.T → Bool

/-- The scalars `V_{q,t,c}` of all rows (p.56). -/
abbrev Scalars (p : Size) := Fin p.M → Fin p.T → Coord p → ℝ

/-- The affine pairs `(c_{q,t,σ,i}, b_{q,t,σ,i})`, `σ ∈ {DOWN, UP}` (with `false` = DOWN and
`true` = UP), `i ∈ [d]` (p.56). -/
abbrev AffinePairs (p : Size) :=
  Fin p.M → Fin p.T → Bool → Fin p.d → (Fin p.Bmsg → Bool) × Bool

/-- All `M` complete rows `R_q`. -/
abbrev Rows (p : Size) := FwdBits p × Scalars p × AffinePairs p

/-- The construction data: the ID array and the complete rows. -/
abbrev TableData (p : Size) := IdArray p × Rows p

/-- **The public table** (App. B.1, Algorithm 9, Table 4, pp.55–57): the fixed-arm fallback flag
(`Sum.inl ()`), or the construction data. Gan, arXiv:2610.05688.

**Formalization Note.** The index types use the constants of `Size`; off the construction branch
those constants carry no meaning, which is why the fallback flag is a separate case. Row index
`q ∈ [M]`, ID index `u ∈ [A]`, follower `i ∈ [d]` and `t ∈ [T]` are the `Fin` elements `q-1`, `u-1`,
`i-1`, `t-1`. -/
abbrev Table (p : Size) := Unit ⊕ TableData p

/-- `Bernoulli(q)`, as the threshold test `V < q` of a `Unif([0,1))` draw. -/
noncomputable def bern (q : ℝ) : Measure Bool := unif.map fun v => decide (v < q)

lemma measurable_decide_lt (q : ℝ) : Measurable fun v : ℝ => decide (v < q) :=
  measurable_to_bool (by
    have : (fun v : ℝ => decide (v < q)) ⁻¹' {true} = Set.Iio q := by ext; simp
    simp [this])

instance (q : ℝ) : IsProbabilityMeasure (bern q) :=
  Measure.isProbabilityMeasure_map (measurable_decide_lt q).aemeasurable

/-- Law of the ID array: independent fair bits. -/
noncomputable def idLaw (p : Size) : Measure (IdArray p) :=
  Measure.pi fun _ => Measure.pi fun _ => bern (1 / 2)

/-- Law of the forward bits: independent, mean `1 - 1/L₀`. -/
noncomputable def fwdLaw (p : Size) : Measure (FwdBits p) :=
  Measure.pi fun _ => Measure.pi fun _ => Measure.pi fun _ => bern (1 - 1 / (p.L0 : ℝ))

/-- Law of the scalars: independent `Unif([0,1))`. -/
noncomputable def scalarLaw (p : Size) : Measure (Scalars p) :=
  Measure.pi fun _ => Measure.pi fun _ => Measure.pi fun _ => unif

/-- Law of the affine pairs: independent `Unif(F₂^B × F₂)`. -/
noncomputable def affineLaw (p : Size) : Measure (AffinePairs p) :=
  Measure.pi fun _ => Measure.pi fun _ => Measure.pi fun _ => Measure.pi fun _ =>
    (Measure.pi fun _ => bern (1 / 2)).prod (bern (1 / 2))

/-- Law of the complete rows: every coordinate independent. -/
noncomputable def rowsLaw (p : Size) : Measure (Rows p) :=
  (fwdLaw p).prod ((scalarLaw p).prod (affineLaw p))

/-- **The explicit table distribution** (Algorithm 9, p.57): the Dirac mass on the fallback flag off
the construction branch; on the branch the product of the ID law and the row law. -/
noncomputable def tableLaw (p : Size) : Measure (Table p) :=
  if p.branch then ((idLaw p).prod (rowsLaw p)).map Sum.inr else Measure.dirac (Sum.inl ())

/-- The uniform draws read by the table sampler, one per table coordinate. -/
abbrev TableTape (p : Size) :=
  (Fin p.A → Fin p.T → ℝ) × (Fin p.M → Fin p.A → Fin p.T → ℝ) × Scalars p ×
    (Fin p.M → Fin p.T → Bool → Fin p.d → (Fin p.Bmsg → ℝ) × ℝ)

/-- The law of the draws: independent `Unif([0,1))`. -/
noncomputable def tableTapeLaw (p : Size) : Measure (TableTape p) :=
  (Measure.pi fun _ => Measure.pi fun _ => unif).prod
    ((Measure.pi fun _ => Measure.pi fun _ => Measure.pi fun _ => unif).prod
      ((scalarLaw p).prod
        (Measure.pi fun _ => Measure.pi fun _ => Measure.pi fun _ => Measure.pi fun _ =>
          (Measure.pi fun _ => unif).prod unif)))

/-- Fill an array, charging one tick per cell on top of the cost of computing the cell. -/
noncomputable def fillProg {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type} [Inhabited α]
    (f : ι → StateM ℕ α) : StateM ℕ (ι → α) := do
  let mut arr : ι → α := fun _ => default
  for i in (Finset.univ : Finset ι).toList do
    tick 1
    let x ← f i
    arr := Function.update arr i x
  pure arr

/-- One sampled cell of `Bernoulli(q)`: read the draw, compare it with `q`. -/
noncomputable def bitProg (q v : ℝ) : StateM ℕ Bool := do
  tick 1
  rlt v q

/-- One sampled scalar cell: read the draw. -/
def readProg (v : ℝ) : StateM ℕ ℝ := do
  tick 1
  pure v

/-- **`sampleTable`: Algorithm 9 (p.57) as a ticked program.** Line 2 tests the branch; lines 5–8
draw every coordinate from one uniform draw, using the same threshold tests as `bern`. Each cell
costs a bounded number of ticks, as in the proof of Prop. 23(i). -/
noncomputable def sampleTable (p : Size) (ω : TableTape p) : StateM ℕ (Table p) := do
  tick 1
  if p.branch then
    let ids ← fillProg fun u => fillProg fun t => bitProg (1 / 2) (ω.1 u t)
    let fwd ← fillProg fun q => fillProg fun u => fillProg fun t =>
      bitProg (1 - 1 / (p.L0 : ℝ)) (ω.2.1 q u t)
    let sc ← fillProg fun q => fillProg fun t => fillProg fun c => readProg (ω.2.2.1 q t c)
    let af ← fillProg fun q => fillProg fun t => fillProg fun σ => fillProg fun i => do
      let c ← fillProg fun k => bitProg (1 / 2) ((ω.2.2.2 q t σ i).1 k)
      let b ← bitProg (1 / 2) (ω.2.2.2 q t σ i).2
      pure (c, b)
    pure (Sum.inr (ids, fwd, sc, af))
  else
    pure (Sum.inl ())

/-- The table output by `sampleTable` on the draws `ω`. -/
noncomputable def sampledTable (p : Size) (ω : TableTape p) : Table p := (sampleTable p ω).run' 0

/-- The ticks of `sampleTable` on the draws `ω`. -/
noncomputable def sampleTicks (p : Size) (ω : TableTape p) : ℕ := ((sampleTable p ω).run 0).2

end AdvMultiplayer


