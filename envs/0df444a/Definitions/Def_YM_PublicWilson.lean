-- Prove2me | Definitions.Def_YM_PublicWilson
-- name    : YM_PublicWilson
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T11:36:52.608222+00:00
-- url     : https://prove2.me/theorems/7bd75257-8797-4d02-b9d5-034c69d7156d
-- title:
--   Wilson lattice families and ordered continuum limits
-- statement:
--   Defines the four-dimensional periodic Wilson lattice. A configuration assigns a group element to each oriented link of the torus $(\mathbb Z/L\mathbb Z)^4$; the plaquette action gives the Wilson energy, and the Wilson law is the normalized Gibbs measure proportional to $e^{-\beta E}$ against product Haar measure. A **Wilson family** records strictly increasing period and denominator sequences, a running coupling $\beta(N,p)$, a Haar probability measure, and local insertions. Smearing insertions against separated Schwartz tests, taking the mesh limit at suitable fixed volumes, then the infinite-volume limit along a prescribed strictly increasing sequence, defines the convergence predicate. This is the lattice origin of the continuum correlations.
-- source:
--   https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/PublicWilson.lean

import Definitions.Def_YM_PublicTheory

/-! Four-dimensional periodic Wilson lattice and its ordered continuum limit. -/
set_option autoImplicit false
noncomputable section
namespace YangMills
open MeasureTheory TopologicalSpace Filter Set
open scoped Topology BigOperators Distributions Matrix.Norms.Frobenius

abbrev Points (n : ℕ) := PiLp 2 (fun _ : Fin n => Spacetime)
abbrev Site (l : ℕ+) := Axis → ZMod l.val
abbrev Configuration (g : GaugeGroup) (l : ℕ+) := (Site l × Axis) → g.image
abbrev Directions := {p : Axis × Axis // p.1 < p.2}

namespace GaugeGroup
instance (g : GaugeGroup) : MeasurableSpace g.image := borel _
instance (g : GaugeGroup) : BorelSpace g.image := ⟨rfl⟩
end GaugeGroup

def plaquette {g : GaugeGroup} {l : ℕ+} (U : Configuration g l) (x : Site l)
    (i j : Axis) : g.image :=
  U (x,i) * (U (x + Pi.single i 1,j) *
    ((U (x + Pi.single j 1,i))⁻¹ * (U (x,j))⁻¹))

def wilsonEnergy {g : GaugeGroup} {l : ℕ+} (U : Configuration g l) : ℝ :=
  ∑ p : Site l × Directions,
    (1 - ((plaquette U p.1 p.2.val.1 p.2.val.2).val.val.trace).re / ((g.n+1 : ℕ) : ℝ))

def wilsonLaw (g : GaugeGroup) (l : ℕ+) (β : ℝ) (haar : Measure g.image) :
    Measure (Configuration g l) :=
  let prior : Measure (Configuration g l) := Measure.pi fun _ => haar
  let density := fun U : Configuration g l => Real.exp (-β * wilsonEnergy U)
  prior.withDensity fun U => ENNReal.ofReal (density U / ∫ V, density V ∂prior)

structure WilsonFamily (g : GaugeGroup) where
  period : ℕ → ℕ+
  denominator : ℕ → ℕ+
  periodStrict : StrictMono fun p => (period p).val
  denominatorStrict : StrictMono fun N => (denominator N).val
  beta : ℕ → ℕ → ℝ
  haar : Measure g.image
  probability : IsProbabilityMeasure haar
  invariantHaar : haar.IsHaarMeasure
  Token : Type
  insertion (N p : ℕ) : Token → Site (period p * denominator N) →
    Configuration g (period p * denominator N) → ℂ

namespace WilsonFamily
variable {g : GaugeGroup} (C : WilsonFamily g)
def mesh (N : ℕ) := ((C.denominator N).val : ℝ)⁻¹
def place (N p : ℕ) (y : Site (C.period p * C.denominator N)) : Spacetime :=
  WithLp.toLp 2 fun i => C.mesh N * (ZMod.valMinAbs (y i) : ℝ)

def finiteMoment (N p : ℕ) {n : ℕ} (labels : Fin n → C.Token)
    (x : Fin n → Site (C.period p * C.denominator N)) : ℂ :=
  ∫ U, ∏ i, C.insertion N p (labels i) (x i) U
    ∂wilsonLaw g (C.period p * C.denominator N) (C.beta N p) C.haar

def separated (n : ℕ) : Opens (Points n) :=
  ⟨{x | Function.Injective x.ofLp}, by
    classical
    have eqSet : {x : Points n | Function.Injective x.ofLp} =
        ⋂ (i : Fin n) (j : Fin n) (_ : i ≠ j), {x : Points n | x i ≠ x j} := by
      ext x
      simp only [mem_setOf_eq, mem_iInter]
      exact ⟨fun h i j hij => fun he => hij (h he), fun h i j he => by_contra fun hij => h i j hij he⟩
    rw [eqSet]
    apply isOpen_iInter_of_finite; intro i
    apply isOpen_iInter_of_finite; intro j
    apply isOpen_iInter_of_finite; intro _
    exact isOpen_ne_fun (PiLp.continuous_apply _ _ i) (PiLp.continuous_apply _ _ j)⟩

abbrev SeparatedTest (n : ℕ) := _root_.TestFunction (separated n) ℂ ⊤

def suitable (p : ℕ) {n : ℕ} (t : SeparatedTest n) : Prop :=
  tsupport t ⊆ {x : Points n | ∀ i a, -((C.period p).val / (2:ℝ)) < x i a ∧
    x i a < (C.period p).val / (2:ℝ)}

def smear (N p : ℕ) {n : ℕ} (v : Fin n → C.Token) (t : SeparatedTest n) : ℂ :=
  (C.mesh N : ℂ) ^ (4*n) * ∑ x : Fin n → Site (C.period p * C.denominator N),
    t (WithLp.toLp 2 fun i => C.place N p (x i)) * C.finiteMoment N p v x

/-- Full mesh limit at each suitable fixed physical volume; then the
infinite-volume limit along the indicated strictly increasing sequence. -/
def Converges (volumeOrder : ℕ → ℕ)
    (unselected : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ) : Prop :=
  ∀ n (v : Fin n → C.Token) (t : SeparatedTest n),
    (∀ᶠ k : ℕ in atTop, C.suitable (volumeOrder k) t) ∧ ∃ row : ℕ → ℂ,
    (∀ p, C.suitable p t → Tendsto (fun N => C.smear N p v t) atTop (𝓝 (row p))) ∧
    Tendsto (fun k => row (volumeOrder k)) atTop (𝓝 (∫ x, t x * unselected v x))
end WilsonFamily
end YangMills


