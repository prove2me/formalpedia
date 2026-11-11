-- Prove2me | Definitions.Def_TwoItemMenu1393_Main_Lattice
-- name    : TwoItemMenu1393_Main_Lattice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:24:46.213195+00:00
-- url     : https://prove2.me/theorems/4f6e26cf-75a5-40a1-b328-4b91a096f833
-- title:
--   Quadratic lattice menu, full cells and forward weights
-- statement:
--   For $h>0$, let $a=\sqrt3h/2$, $b=h/2$, $\Lambda_h=\mathbb Z(2a,0)+\mathbb Z(a,3b)$ and $Z_h=\Lambda_h\cap[0,1/2]^2$. The quadratic entries offer $z\in Z_h$ at price $\|z\|^2/2+1/200$; add the bundle at price $1/4$ and null. Their utility is
--   $$U_h(v)=\max\{0,\max_{z\in Z_h}(z\cdot v-\|z\|^2/2-1/200),\ v_1+v_2-1/4\}.$$
--   Choose a highest-price maximizer, then the earliest in a fixed finite order. The six hexagon vertices, owned A/B₀ classes, sector $\mathcal D$, full cells, grid $G_h$ and the four coefficients in (17) are explicit. The provisional weights are $h^2\|v\|^{-4}$; inlets are the positive part of the finite balance operator applied to those weights. Increasing-first-coordinate forward substitution defines $W$. The module also defines the eight-edge cell slack and six-vertex defect. No balance, positivity estimate, coverage or optimality property is built into these objects. They supply the concrete geometric and algebraic data of the lower bound.
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), §4.1, pp. 8–11; D.1, pp. 21–23, equations (8)–(13); D.2, pp. 24–26, equations (16)–(19). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf

import Definitions.Def_TwoItemMenu1393_Main_Model
set_option autoImplicit false

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace TwoItemMenu1393.Main

/-! Chan–Guo–Thach, submission #1393 (October 2026), §4.1 pp. 8–11,
Appendix D.1 pp. 21–23, equations (8)–(13); D.2 pp. 24–26, (16)–(19).
All finite constructions have mathematical bodies; none contains the desired estimates. -/
def a (h : ℝ) : ℝ := Real.sqrt 3 * h / 2
def b (h : ℝ) : ℝ := h / 2
def center (h : ℝ) (k : ℤ × ℤ) : Vec :=
  vec (2 * a h * k.1 + a h * k.2) (3 * b h * k.2)
def Q (v : Vec) : ℝ := ‖v‖ ^ 2 / 2 - 1 / 200
def bundle : Entry := (vec 1 1, 1 / 4)
def quadraticEntry (z : Vec) : Entry := (z, ‖z‖ ^ 2 / 2 + 1 / 200)

/-- A finite enumeration of Λ_h ∩ [0,1/2]². For h>0 the integer box contains
every retained center; h≤0 is unused by all lattice theorem statements. -/
def centers (h : ℝ) : Finset Vec := by
  classical
  let n : ℤ := ⌈4 / h⌉ + 1
  exact (((Finset.Icc (-n) n).product (Finset.Icc (-n) n)).image (center h)).filter
    (fun z => z ∈ square (1 / 2))
def quadraticMenu (h : ℝ) : Finset Entry := by
  classical
  exact (centers h).image quadraticEntry
def latticeMenu (h : ℝ) : Finset Entry := by
  classical
  exact insert bundle (quadraticMenu h)
def U (h : ℝ) : Vec → ℝ := envelope (↑(latticeMenu h))

/-- Highest utility, then highest price, then earliest entry in a fixed finite order. -/
def chooseEntry (L : List Entry) (v : Vec) : Entry :=
  L.foldl (fun e f => if entryUtility e v < entryUtility f v ∨
    (entryUtility e v = entryUtility f v ∧ e.2 < f.2) then f else e) nullEntry
def canonical (h : ℝ) : Mechanism :=
  ⟨U h, fun v => (chooseEntry (latticeMenu h).toList v).1⟩

/-- Order: A, B₀, T, R⁺, R⁻, D₀, as in (10). -/
def offset (h : ℝ) (i : Fin 6) : Vec :=
  ![vec (-a h) (b h), vec (-a h) (-b h), vec 0 (2 * b h),
    vec (a h) (b h), vec (a h) (-b h), vec 0 (-2 * b h)] i
def vertex (h : ℝ) (z : Vec) (i : Fin 6) : Vec := z + offset h i
def direction (θ : ℝ) : Vec := vec (Real.cos θ) (Real.sin θ)
def radialBundle (θ : ℝ) : ℝ :=
  Real.cos θ + Real.sin θ - Real.sqrt ((Real.cos θ + Real.sin θ) ^ 2 - 49 / 100)
def sector : Set Vec := {v | ∃ θ r : ℝ, Real.pi / 36 < θ ∧ θ < Real.pi / 12 ∧
  1 / 10 < r ∧ r < radialBundle θ ∧ v = r • direction θ}
def InAngle (v : Vec) : Prop :=
  ∃ θ : ℝ, Real.pi / 36 ≤ θ ∧ θ ≤ Real.pi / 12 ∧ v = ‖v‖ • direction θ
def Beats (h : ℝ) (z : Vec) : Prop :=
  ∀ i : Fin 6, max 0 (entryUtility bundle (vertex h z i)) <
    entryUtility (quadraticEntry z) (vertex h z i)
def Full (h : ℝ) (z : Vec) : Prop :=
  z ∈ centers h ∧ Beats h z ∧ InAngle (vertex h z 0) ∧ InAngle (vertex h z 1)
def fullCenters (h : ℝ) : Finset Vec := by
  classical
  exact (centers h).filter (Full h)

/-- Owned vertices are indexed by their unique center and their A/B₀ class. -/
abbrev Owned := Vec × Fin 2
def ownedPoint (h : ℝ) (o : Owned) : Vec := vertex h o.1 ⟨o.2.val, by omega⟩
def grid (h : ℝ) : Finset Owned := by
  classical
  exact ((centers h).product Finset.univ).filter fun o =>
    Beats h o.1 ∧ InAngle (ownedPoint h o) ∧
      2 / 25 < ‖ownedPoint h o‖ ∧ ‖ownedPoint h o‖ < 2 / 5
def target (h : ℝ) (o : Owned) (j : Fin 4) : Vec := vertex h o.1 ⟨j.val + 2, by omega⟩
def beta (h : ℝ) (o : Owned) (j : Fin 4) : ℝ :=
  let v := ownedPoint h o
  let X := v 0 / a h
  let Y := v 1 / b h
  if o.2 = 0 then ![(8*X+2*Y)/15, X/10+Y/6, (X-2*Y)/15, (2*X-3*Y)/15] j
  else ![(2*X+3*Y)/15, (X+2*Y)/15, X/10-Y/6, (8*X-2*Y)/15] j
def betaTotal (h : ℝ) (o : Owned) : ℝ := ∑ j, beta h o j
def betaInto (h : ℝ) (o : Owned) (v : Vec) : ℝ :=
  ∑ j : Fin 4, if target h o j = v then beta h o j else 0
def provisional (h : ℝ) (o : Owned) : ℝ := h ^ 2 / ‖ownedPoint h o‖ ^ 4
def inlet (h : ℝ) (o : Owned) : ℝ :=
  max ((1 + betaTotal h o) * provisional h o -
    ∑ p ∈ grid h, provisional h p * betaInto h p (ownedPoint h o)) 0

/-- Forward substitution in increasing first coordinate, avoiding a total matrix inverse. -/
def weights (h : ℝ) : Owned → ℝ :=
  let L := (grid h).toList.mergeSort (fun o p => ownedPoint h o 0 ≤ ownedPoint h p 0)
  L.foldl (fun W o => Function.update W o
    ((inlet h o + ∑ p ∈ grid h, W p * betaInto h p (ownedPoint h o)) /
      (1 + betaTotal h o))) (fun _ => 0)
def BoundaryInlet (h : ℝ) (o : Owned) : Prop :=
  ∃ p : Owned, (∃ k : ℤ × ℤ, p.1 = center h k) ∧ p ∉ grid h ∧
    ∃ j : Fin 4, target h p j = ownedPoint h o

def cellSlack (h : ℝ) (M : Mechanism) (z : Vec) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 4, slack M (ownedPoint h (z,i)) (target h (z,i) j)
def defect (h : ℝ) (M : Mechanism) (z : Vec) : ℝ :=
  ∑ i : Fin 6, slack M (vertex h z 0) (vertex h z i)

end TwoItemMenu1393.Main


