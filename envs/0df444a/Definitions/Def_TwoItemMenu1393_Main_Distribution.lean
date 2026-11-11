-- Prove2me | Definitions.Def_TwoItemMenu1393_Main_Distribution
-- name    : TwoItemMenu1393_Main_Distribution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:26:47.521899+00:00
-- url     : https://prove2.me/theorems/a3aa914e-b516-4f0d-84e9-10997a337b1d
-- title:
--   Radial completion and the atomic lower-bound family
-- statement:
--   Continue every positive inlet backward to the first nonnull point of its ray and every grid exit forward to the first bundle point. Subdivide at active affine-piece changes and shared grid vertices. A segment from $rd$ to $r'd$ with incoming amount $I$ deposits mass $I(r'-r)/r'$ at its initial point and passes amount $Ir/r'$. An exit deposits its remaining amount at the terminal. Add three source-one chains at angles $\pi/24$, $\pi/18$, $5\pi/72$. Coincident atoms merge by measure addition. With $k_v=K_v\|v\|/\|s_v\|$ and $S_h=\sum_v k_v$, set
--   $$F_h=(S_h+3)^{-1}F_h^{\mathrm{raw}},\qquad L_h(u,g)=\mathrm{OPT}(F_h)-\mathrm{Rev}_{F_h}(u,g).$$
--   First crossings, nodes, source amounts, anchor endpoints and finite sums all have explicit mathematical definitions. Proposition 4.1 must establish that this is a finitely supported probability law for small positive $h$, and that the canonical menu is optimal. The construction does not assume those conclusions.
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), D.2, pp. 26–28, radial completion and equations (20)–(21). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf

import Definitions.Def_TwoItemMenu1393_Main_Lattice
set_option autoImplicit false

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace TwoItemMenu1393.Main

/-! Chan–Guo–Thach, submission #1393 (October 2026), Appendix D.2,
pp. 26–28, radial completion and equations (20)–(21).
The raw measure is defined for every h, but probability, support, positivity and
optimality are theorem conclusions only for sufficiently small positive h. -/
def sourceRadius (h : ℝ) (d : Vec) : ℝ :=
  sInf ((fun e : Entry => e.2 / dot e.1 d) ''
    {e ∈ (↑(latticeMenu h) : Set Entry) | 0 < dot e.1 d})
def bundleRadius (h : ℝ) (d : Vec) : ℝ :=
  sSup (insert 0 ((fun e : Entry => (bundle.2 - e.2) / dot (bundle.1 - e.1) d) ''
    insert nullEntry (↑(quadraticMenu h) : Set Entry)))
def anchorAngle (i : Fin 3) : ℝ := ![Real.pi/24, Real.pi/18, 5*Real.pi/72] i
def anchorSource (h : ℝ) (i : Fin 3) : Vec :=
  sourceRadius h (direction (anchorAngle i)) • direction (anchorAngle i)
def anchorTerminal (h : ℝ) (i : Fin 3) : Vec :=
  bundleRadius h (direction (anchorAngle i)) • direction (anchorAngle i)

/-- Only active crossings with distinct radial slopes are changes of affine piece.
Include grid vertices on the ray, as specified on p. 27. -/
def radialNodes (h : ℝ) (d : Vec) (r s : ℝ) : Finset ℝ := by
  classical
  let E := insert nullEntry (latticeMenu h)
  let crosses := ((E.product E).filter fun ef => dot (ef.1.1 - ef.2.1) d ≠ 0).image
    (fun ef => (ef.1.2 - ef.2.2) / dot (ef.1.1 - ef.2.1) d)
  let active := crosses.filter fun t => r < t ∧ t < s ∧
    ∃ e ∈ E, ∃ f ∈ E, dot (e.1-f.1) d ≠ 0 ∧
      entryUtility e (t • d) = U h (t • d) ∧ entryUtility f (t • d) = U h (t • d)
  let throughGrid := ((grid h).image (fun o => ‖ownedPoint h o‖)).filter fun t =>
    r < t ∧ t < s ∧ ∃ o ∈ grid h, ownedPoint h o = t • d
  exact insert r (insert s (active ∪ throughGrid))

/-- The segment starting at radius t receives I*r/t. Its mass is
(I*r/t)*(t'-t)/t'; terminal mass is included exactly for exit/anchor chains. -/
def radialMeasure (h : ℝ) (d : Vec) (r s I : ℝ) (terminal : Bool) : Measure Vec :=
  let L := (radialNodes h d r s).sort (· ≤ ·)
  let pieces := L.zip L.tail
  (pieces.map (fun tt => ENNReal.ofReal ((I*r/tt.1)*(tt.2-tt.1)/tt.2) •
    Measure.dirac (tt.1 • d))).sum +
      (if terminal then ENNReal.ofReal (I*r/s) • Measure.dirac (s • d) else 0)

def sourceAmount (h : ℝ) (o : Owned) : ℝ :=
  let v := ownedPoint h o
  let d := ‖v‖⁻¹ • v
  inlet h o * ‖v‖ / sourceRadius h d
def totalSource (h : ℝ) : ℝ := ∑ o ∈ grid h, sourceAmount h o

/-- Grid weights plus inlet completions, exits and the three unit-source anchors.
Coincident atoms merge by addition of measures. -/
def rawLaw (h : ℝ) : Measure Vec :=
  (∑ o ∈ grid h, ENNReal.ofReal (weights h o) • Measure.dirac (ownedPoint h o)) +
  (∑ o ∈ grid h,
    let v := ownedPoint h o
    let d := ‖v‖⁻¹ • v
    radialMeasure h d (sourceRadius h d) ‖v‖ (sourceAmount h o) false) +
  (∑ o ∈ grid h, ∑ j : Fin 4,
    let t := target h o j
    let d := ‖t‖⁻¹ • t
    if ∃ p ∈ grid h, ownedPoint h p = t then 0 else
      radialMeasure h d ‖t‖ (bundleRadius h d) (weights h o * beta h o j) true) +
  ∑ i : Fin 3,
    let d := direction (anchorAngle i)
    radialMeasure h d (sourceRadius h d) (bundleRadius h d) 1 true
def lowerLaw (h : ℝ) : Measure Vec :=
  ENNReal.ofReal ((totalSource h + 3)⁻¹) • rawLaw h
def loss (h : ℝ) (M : Mechanism) : ℝ := optimum (lowerLaw h) - revenue (lowerLaw h) M

end TwoItemMenu1393.Main


