-- Prove2me | Definitions.Def_HooftDimReduction_Defs
-- name    : HooftDimReduction_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-26T01:17:55.448971+00:00
-- url     : https://prove2.me/theorems/d8bdf70f-4a16-41d7-9553-eeef931703b2
-- title:
--   't Hooft 1993: cubic lattice, staircase (14), plaquette relations (12), linear rules (17)
-- statement:
--   Definitions for the cellular-automaton model of 't Hooft's essay *Dimensional Reduction in Quantum Gravity* (Section on Fig. 1, eqs. (12)–(19)).
--
--   1. **Sites**: the lattice $\mathbb Z^3$ with unit vectors $e^1=(1,0,0)$, $e^2=(0,1,0)$, $e^3=(0,0,1)$.
--   2. **Staircase** $x(n)$, $n\in\mathbb Z$, starting at $x(0)=x_0$ (eq. (14)):
--   $$x(3q)=x_0+q\,(e^1-e^2+e^3),\quad x(3q+1)=x(3q)+e^1,\quad x(3q+2)=x(3q)+e^1-e^2 .$$
--   3. **Plaquettes**: for a lowest corner $x$ and an orientation spanned by $(u,v)\in\{(e^1,e^2),(e^1,e^3),(e^2,e^3)\}$, the corners in cyclic order $x,\,x+u,\,x+u+v,\,x+v$.
--   4. **Plaquette rule**: a map $g:(\mathbb Z/p)^4\to\mathbb Z/p$ such that for every slot $i$ and every values of the other three entries there is exactly one value of the $i$-th entry with $g=0$.
--   5. **Satisfying the rules**: $f:\mathbb Z^3\to\mathbb Z/p$ satisfies a family $g_{x,P}$ if $g_{x,P}$ vanishes on the corner values of every plaquette $(x,P)$.
--   6. **Cube faces** in the order (12a–f): $ABCD$, $EFGH$, $ABFE$, $DCGH$, $ADHE$, $BCGF$ with $A=x$, $B=x+e^1$, $D=x+e^2$, $E=x+e^3$.
--   7. **Linear rule** (eq. (17)): $g(f)=\sum_{j=1}^4 a_j f_j+b$.
--   8. **Cube consistency** (eq. (16)): for all $f(A),f(B),f(D),f(E)$ there are data on $\mathbb Z^3$ with these values at $0,e^1,e^2,e^3$ that satisfy the six face relations of the unit cube at the origin.
--   9. **Alternating rule**: $g(f)=f_1-f_2+f_3-f_4$.
--
--   These are shared by all statements of the mission.
--
--   **Formalization Note** Integer division and remainder in the staircase are Euclidean (remainder in $\{0,1,2\}$), so the formula is valid for negative $n$ as well.
-- source:
--   G. 't Hooft, "Dimensional Reduction in Quantum Gravity", essay dedicated to Abdus Salam, Utrecht preprint THU-93/26, arXiv:gr-qc/9310026v2, https://arxiv.org/abs/gr-qc/9310026

import Mathlib

namespace HooftDimReduction

/-- Sites of the rectangular lattice `ℤ³`, with coordinates `(x₁, x₂, x₃)`. -/
abbrev Site := ℤ × ℤ × ℤ

/-- The unit vector `e¹` of the lattice. -/
def e1 : Site := (1, 0, 0)
/-- The unit vector `e²` of the lattice. -/
def e2 : Site := (0, 1, 0)
/-- The unit vector `e³` of the lattice. -/
def e3 : Site := (0, 0, 1)

/-- The staircase series of points `x(n)`, `n ∈ ℤ`, of eq. (14), starting at `x(0) = x₀`:
`x(3n+1) = x(3n) + e¹`, `x(3n+2) = x(3n+1) - e²`, `x(3n+3) = x(3n+2) + e³`. -/
def staircase (x₀ : Site) (n : ℤ) : Site :=
  x₀ + (n / 3) • (e1 - e2 + e3) +
    (if n % 3 = 0 then 0 else if n % 3 = 1 then e1 else e1 - e2)

/-- The three orientations of an elementary plaquette: parallel to the `x₁x₂`, `x₁x₃`
or `x₂x₃` coordinate plane. -/
inductive Plane
  | p12
  | p13
  | p23
  deriving DecidableEq

/-- The two lattice directions `(u, v)` spanning a plaquette of the given orientation. -/
def Plane.dirs : Plane → Site × Site
  | .p12 => (e1, e2)
  | .p13 => (e1, e3)
  | .p23 => (e2, e3)

/-- The four corners of the plaquette with lowest corner `x` and orientation `P`, listed in
cyclic order `x, x + u, x + u + v, x + v` (this is the order of the arguments in eqs. (12a–f)). -/
def plaquette (x : Site) (P : Plane) : Fin 4 → Site :=
  ![x, x + P.dirs.1, x + P.dirs.1 + P.dirs.2, x + P.dirs.2]

/-- A plaquette relation `g(f₁, f₂, f₃, f₄) = 0` on data modulo `p` such that, whenever three of
the four entries are given, the fourth is uniquely determined. -/
def IsPlaquetteRule {p : ℕ} (g : (Fin 4 → ZMod p) → ZMod p) : Prop :=
  ∀ (i : Fin 4) (w : Fin 4 → ZMod p), ∃! a : ZMod p, g (Function.update w i a) = 0

/-- The lattice data `f : ℤ³ → ℤ/p` satisfy the plaquette relation `g x P` on every plaquette
`(x, P)` of the lattice. -/
def SatisfiesRules {p : ℕ} (g : Site → Plane → (Fin 4 → ZMod p) → ZMod p)
    (f : Site → ZMod p) : Prop :=
  ∀ (x : Site) (P : Plane), g x P (fun i => f (plaquette x P i)) = 0

/-- The six faces of the unit cube with lowest corner `x`, in the order of eqs. (12a–f):
`(a) ABCD, (b) EFGH, (c) ABFE, (d) DCGH, (e) ADHE, (f) BCGF`, where `A = x`, `B = x + e¹`,
`D = x + e²`, `E = x + e³`. Each face is given by its lowest corner and its orientation. -/
def cubeFace (x : Site) : Fin 6 → Site × Plane :=
  ![(x, .p12), (x + e3, .p12), (x, .p13), (x + e2, .p13), (x, .p23), (x + e1, .p23)]

/-- A linear plaquette relation modulo `p`, as in eq. (17): `g(f) = ∑ⱼ aⱼ fⱼ + b`. -/
def linearRule {p : ℕ} (a : Fin 4 → ZMod p) (b : ZMod p) : (Fin 4 → ZMod p) → ZMod p :=
  fun w => ∑ j, a j * w j + b

/-- Consistency ("commutation") of six plaquette relations on the unit cube, eq. (16): for every
choice of the free data `f(A), f(B), f(D), f(E)` there are data on the eight corners of the cube
`[0,1]³` taking these values and satisfying all six face relations `(12a–f)`. -/
def CubeConsistent {p : ℕ} (g : Fin 6 → (Fin 4 → ZMod p) → ZMod p) : Prop :=
  ∀ fA fB fD fE : ZMod p, ∃ f : Site → ZMod p,
    f 0 = fA ∧ f e1 = fB ∧ f e2 = fD ∧ f e3 = fE ∧
    ∀ k : Fin 6, g k (fun i => f (plaquette (cubeFace 0 k).1 (cubeFace 0 k).2 i)) = 0

/-- The alternating linear plaquette relation `f₁ - f₂ + f₃ - f₄ = 0 (mod p)`. -/
def altRule {p : ℕ} : (Fin 4 → ZMod p) → ZMod p :=
  fun w => w 0 - w 1 + w 2 - w 3

end HooftDimReduction


