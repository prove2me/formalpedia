-- Prove2me | Definitions.Def_SteinerShortcuts_Main_TestFunctions
-- name    : SteinerShortcuts_Main_TestFunctions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T12:35:11.131429+00:00
-- url     : https://prove2.me/theorems/faa87882-1442-4352-9583-c1594e453f0d
-- title:
--   The optimized test functions and transfer conditions
-- statement:
--   Fix critical paths $P_1,P_2$ with labels $a_i,b_i$ and sources $s_i$, and cross-paths in both directions. Test functions take a pre-step position $p$ and label $t$ to a real number. Let $y=\mu_ot+\nu_o$ be the secant through $(a_1,y_{a_1}),(a_2,y_{a_2})$, or the line of slope $2a_1$ through $(a_1,y_{a_1})$ when labels coincide; define the even line from $b_1,b_2$. Then
--   $$
--   Y(p,c_t)=(y_t-\mu_\sigma t-\nu_\sigma)^2
--   $$
--   on steps of parity $\sigma$. Write $x_o=x_o^1(p)$, $x_{o,i}=x_o^1(s_i)$ and define, when $a_1\ne a_2$,
--   $$
--   \psi_{o,i}(p)=\frac{x_o-x_{o,i}-a_i r_o(p)}{a_2-a_1},\qquad
--   R^o(p,c)=\begin{cases}\psi_{o,1}(p)\psi_{o,2}(p)&\ell\text{ odd},\\0&\ell\text{ even}.\end{cases}
--   $$
--   The even functions use $x_e,r_e,b_i$ and vanish on odd layers. If both label pairs are unequal, set $\tau_o=(x_{o,1}-x_{o,2})/(a_2-a_1)$ and $\tau_e=(x_{e,1}-x_{e,2})/(b_2-b_1)$. Equation (9) is
--   $$
--   S(p,c_t)=\begin{cases}(\tau_e-\tau_o)\dfrac{t-a_1}{a_2-a_1}\psi_{e,2}(p)&\ell\text{ odd},\\0&\ell\text{ even}.\end{cases}
--   $$
--   The definitions extend $R$ and $S$ by zero outside their unequal-label domains; claims using their formulas keep the corresponding domain conditions.
--
--   (T1′) is nonnegativity on the two fixed cross-paths. The schema (T2) requires vanishing on both critical paths and says that vanishing on a path implies its desired property. The relaxed linear representation is
--   $$
--   F(p,c)=\operatorname{Upd}(p,c)^\top\lambda+g(\ell).
--   $$
--   This condition (T3′) is imposed for construction vertices and direction labels, where the counters are determined by the layer. The explicit pair setup records sources, compatibility and both cross-paths. These definitions express the conditions of the transfer claim without assuming any test-function representation or any cross-path restriction.
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), pp. 9, 15–20, (T1′), (T2), (T3′), eqs. (7)–(9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_Construction

namespace SteinerShortcuts.Main

noncomputable section
open scoped Classical

abbrev TestFunction (q : ℕ) := Position → Fin q → ℝ

def lineSlope (q : ℕ) (a b : Fin q) : ℝ :=
  if a = b then 2*(a.val : ℝ)
  else ((labelY q b.val : ℝ) - (labelY q a.val : ℝ)) / ((b.val : ℝ) - (a.val : ℝ))

def lineIntercept (q : ℕ) (a b : Fin q) : ℝ :=
  (labelY q a.val : ℝ) - lineSlope q a b * (a.val : ℝ)

/-- Equation (7), including the tangent line when the labels coincide. -/
def testY {q : ℕ} (P Q : CriticalData q) : TestFunction q := fun p t =>
  let a := if p 0 % 2 = 1 then P.a else P.b
  let b := if p 0 % 2 = 1 then Q.a else Q.b
  ((labelY q t.val : ℝ) - lineSlope q a b * (t.val : ℝ) - lineIntercept q a b)^2

def psi (x r : ℤ) (x₁ : ℤ) (a a₁ a₂ : ℕ) : ℝ :=
  ((x : ℝ) - (x₁ : ℝ) - (a : ℝ)*(r : ℝ)) / ((a₂ : ℝ)-(a₁ : ℝ))

/-- Equation (8); its source domain is unequal labels. Outside it the chosen extension is zero. -/
def testROdd {q : ℕ} (P Q : CriticalData q) : TestFunction q := fun p _ =>
  if P.a ≠ Q.a ∧ p 0 % 2 = 1 then
    psi (p 3) (p 1) (P.source 3) P.a.val P.a.val Q.a.val *
    psi (p 3) (p 1) (Q.source 3) Q.a.val P.a.val Q.a.val
  else 0

def testREven {q : ℕ} (P Q : CriticalData q) : TestFunction q := fun p _ =>
  if P.b ≠ Q.b ∧ p 0 % 2 = 0 then
    psi (p 7) (p 2) (P.source 7) P.b.val P.b.val Q.b.val *
    psi (p 7) (p 2) (Q.source 7) Q.b.val P.b.val Q.b.val
  else 0

def tauOdd {q : ℕ} (P Q : CriticalData q) : ℝ :=
  ((P.source 3 : ℝ) - (Q.source 3 : ℝ)) / ((Q.a.val : ℝ) - (P.a.val : ℝ))

def tauEven {q : ℕ} (P Q : CriticalData q) : ℝ :=
  ((P.source 7 : ℝ) - (Q.source 7 : ℝ)) / ((Q.b.val : ℝ) - (P.b.val : ℝ))

/-- Equation (9), used only with both pairs of labels unequal. -/
def testS {q : ℕ} (P Q : CriticalData q) : TestFunction q := fun p t =>
  if P.a ≠ Q.a ∧ P.b ≠ Q.b ∧ p 0 % 2 = 1 then
    (tauEven P Q - tauOdd P Q) *
    (((t.val : ℝ) - (P.a.val : ℝ)) / ((Q.a.val : ℝ) - (P.a.val : ℝ))) *
    psi (p 7) (p 2) (Q.source 7) Q.b.val P.b.val Q.b.val
  else 0

/-- Vanishing on every step; labels are quantified only when they realize that actual edge. -/
def Vanishes {q : ℕ} (F : TestFunction q) (R : Route Point) : Prop :=
  ∀ e ∈ R.arcs, ∀ t : Fin q, e.2 = step q e.1 t → F (position e.1) t = 0

def NonnegativeOn {q : ℕ} (F : TestFunction q) (R : Route Point) : Prop :=
  ∀ e ∈ R.arcs, ∀ t : Fin q, e.2 = step q e.1 t → 0 ≤ F (position e.1) t

def T1prime {q : ℕ} (F : TestFunction q) (R T : Route Point) : Prop :=
  NonnegativeOn F R ∧ NonnegativeOn F T

/-- The schema T2 for a desired path property; it includes vanishing on both critical paths. -/
def T2 {q : ℕ} (F : TestFunction q) (P Q : Route Point)
    (desired : Route Point → Prop) (G : Digraph Point) : Prop :=
  Vanishes F P ∧ Vanishes F Q ∧
    ∀ R, IsPath G R → Vanishes F R → desired R

/-- T3-prime is required on construction vertices and every direction, not arbitrary counters. -/
def T3prime (L q : ℕ) (F : TestFunction q) : Prop :=
  ∃ coeff : Fin 21 → ℝ, ∃ g : ℤ → ℝ,
    ∀ v ∈ vertices L q, ∀ t : Fin q,
      F (position v) t = (∑ i, (update q (position v) t i : ℝ) * coeff i) + g (v 0)

/-- Both critical sources, compatibility, and the two fixed cross-paths of printed p.15. -/
def PairSetup (L q : ℕ) (P Q : CriticalData q) (R T : Route Point) : Prop :=
  P.Valid L ∧ Q.Valid L ∧
  CompatiblePair (construction L q) (P.route L) (Q.route L) ∧
  IsCrossPath (construction L q) (P.route L) (Q.route L) R ∧
  IsCrossPath (construction L q) (Q.route L) (P.route L) T

end
end SteinerShortcuts.Main


