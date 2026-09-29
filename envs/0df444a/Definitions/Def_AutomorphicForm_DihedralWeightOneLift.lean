-- Prove2me | Definitions.Def_AutomorphicForm_DihedralWeightOneLift
-- name    : AutomorphicForm_DihedralWeightOneLift
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/8ebb2b37-fd60-5841-98b7-33e0b624fa7a
-- title:
--   Adelic weight-one lift at level N over Q
-- statement:
--   Working over the rational field, this module sets up the shape of the adelization of a weight-one form on the upper half plane. First, [`DihedralWeightOne.weightOneArchLift`](../def/AutomorphicForm_DihedralWeightOneLift.html#L12) takes a function $f : \mathbb{H} \to \mathbb{C}$ and an element $h \in \mathrm{GL}_2(\mathbb{R})$ and returns $(f \mid_1 h)(i) \cdot (\det h)^{1}$, where $\mid_1$ is the weight-one slash action, the value is read at the point $i$ of the upper half plane, and the determinant (a unit of $\mathbb{R}$) is coerced into $\mathbb{C}$ and raised to the integer power $1$. Second, [`DihedralWeightOne.HasWeightOneDecomp`](../def/AutomorphicForm_DihedralWeightOneLift.html#L15) is a predicate on an ideal $N$ of the ring of integers of $\mathbb{Q}$ and an element $g$ of $\mathrm{GL}_2$ of the adele ring: it asserts the existence of $\gamma \in \mathrm{GL}_2(\mathbb{Q})$ and adelic elements $h, u$ with $u$ in the level-$N$ subgroup $(\mathtt{productionPinsCompact}\ \mathbb{Q}).U\,N$, which by definition is the intersection of the level-one subgroup attached to $N$ with the kernel of the archimedean projection, with $h$ trivial at all finite places (`AdelicLevel.glFin` of $h$ equal to $1$), with the associated real matrix [`LanglandsTunnell.ratArchGL2`](../def/LanglandsTunnell_DeltaLift.html#L16) $h$ — the component of $h$ at the unique infinite place of $\mathbb{Q}$, transported along the identification of that completion with $\mathbb{R}$ — of positive determinant, and with $g = \gamma h u$, the global point $\gamma$ being taken in the adelic group by [`AutomorphicForm.globalPoints`](../def/AutomorphicForm_AdelicLsXi.html#L15). Third, [`DihedralWeightOne.weightOneLift`](../def/AutomorphicForm_DihedralWeightOneLift.html#L23) $N$ $f$ $g$ is defined by a case split on this predicate: where a decomposition exists, it is the archimedean lift of $f$ evaluated at the real matrix attached to the middle factor of a classically chosen witness; where none exists, the value is $0$. Thus the definition as such carries no invariance, eigenfunction or well-definedness assertion: independence of the choice of decomposition and the automorphy properties are the content of separate theorems.
--
--   **Relation to Mathlib.** The weight-one slash action $\mid_1$, the positive-determinant subgroup $\mathrm{GL}^+_2(\mathbb{R})$ and the adele ring are Mathlib's; the adelic lift of a function on the upper half plane and the attendant strong-approximation decomposition predicate are the project's own notions, parallel to the weight-twelve lift of $\Delta$ in the imported module.
--
--   **Where it is used.** These definitions provide the adelic realisation used on the Langlands–Tunnell side of the argument, where weight-one dihedral forms must be viewed as automorphic functions on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$ with prescribed level, in parallel with the lift of the discriminant form supplied by the imported module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_DihedralWeightOneLift.lean

import Definitions.Def_LanglandsTunnell_DeltaLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix AutomorphicForm
open scoped ModularForm MatrixGroups

namespace DihedralWeightOne

def weightOneArchLift (f : UpperHalfPlane → ℂ) (h : GL (Fin 2) ℝ) : ℂ :=
  (f ∣[(1 : ℤ)] h) UpperHalfPlane.I * ((h.det.val : ℝ) : ℂ) ^ (1 : ℤ)

def HasWeightOneDecomp (N : Ideal (𝓞 ℚ)) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Prop :=
  ∃ (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)),
    u ∈ (productionPinsCompact ℚ).U N ∧ AdelicLevel.glFin (𝓞 ℚ) ℚ h = 1 ∧
    LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ ∧
    g = AutomorphicForm.globalPoints (𝓞 ℚ) ℚ γ * h * u

open scoped Classical in

def weightOneLift (N : Ideal (𝓞 ℚ)) (f : UpperHalfPlane → ℂ)
    (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : ℂ :=
  if H : HasWeightOneDecomp N g then
    weightOneArchLift f (LanglandsTunnell.ratArchGL2 H.choose_spec.choose) else 0

end DihedralWeightOne

end


