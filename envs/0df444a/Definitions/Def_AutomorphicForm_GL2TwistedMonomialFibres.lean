-- Prove2me | Definitions.Def_AutomorphicForm_GL2TwistedMonomialFibres
-- name    : AutomorphicForm_GL2TwistedMonomialFibres
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/98780e29-a24f-50b7-aaf6-f5b8251df3a3
-- title:
--   Twisted invariants and fibre terms for GL(2,ℂ) monomials
-- statement:
--   Fix $g \in \mathrm{GL}_2(\mathbb{C})$ and write $\bar g$ for its entrywise conjugate (the `conjEntries` of the ambient module) and $g^{*}$ for its conjugate transpose. Four scalar invariants are introduced: `invFrobSq` $T = \operatorname{Re}\operatorname{tr}(g g^{*})$, the sum of the squared moduli of the entries; `invTraceNorm` $y = \operatorname{tr}(g\bar g) \in \mathbb{C}$; `invSecondRe` $= \operatorname{Re}\operatorname{tr}\bigl((g\bar g)(g g^{*})\bigr)$; and `invAbsDet` $d = |\det g|$. From these, `invDifference` is $E = \bigl(\operatorname{Re}\operatorname{tr}((g\bar g)(gg^{*})) - T\,\operatorname{Re} y + 2d^{2}\bigr)/d$, and `monomialInput` of bidegree $(i,l)$ is the real number
--   $$\Bigl(\tfrac{T - \operatorname{Re} y + E}{2(T+2d)}\Bigr)^{i}\Bigl(\tfrac{T - \operatorname{Re} y - E}{2(T-2d)}\Bigr)^{l}.$$
--   Divisions follow the Lean convention that division by zero is zero, so on the locus $T = 2d$ the second base is read as $0$.
--
--   The remaining definitions are the shapes in which these monomials are expected to transform. `fibreMonomialFactor` is $(T-x)^{i+l}/\bigl((T+2d)^{i}(T-2d)^{l}\bigr)$ for real parameters $T$, $d$, $x$; `fibreArcIntegral` is $\int_{-\Psi/2}^{\Psi/2}\cos^{2i}\psi\,\sin^{2l}\psi\,d\psi$; and `ellipticArcLength` is $\arccos\bigl((2r - T\cos\theta)/(T - 2r\cos\theta)\bigr)$. Then `ellipticFibreTerm` is the complex number obtained from the real quantity $(4\pi\sin\theta/r)\cdot$ (the monomial factor at $d = r$, $x = 2r\cos\theta$) $\cdot$ (the arc integral over an arc of length `ellipticArcLength`), while `splitFibreTerm` at $(a_1,a_2)$ is one half of the monomial factor at $d = \sqrt{a_1 a_2}$, $x = a_1 + a_2$, times the arc integral over $\Psi = 2\pi$, i.e. the full circle. Finally, for a complex-valued profile $c$ on the levels $T$, `ellipticFibreSide` is $\int_{T > 2r} c(T)\,\cdot$ `ellipticFibreTerm` and `splitFibreSide` is $\int_{T > a_1+a_2} c(T)\,\cdot$ `splitFibreTerm`, both Lebesgue integrals over the indicated half-lines.
--
--   **Relation to Mathlib.** All thirteen notions are the project's own; Mathlib contributes only the ingredients (`Matrix.trace`, `Matrix.conjTranspose`, `Matrix.det`, `Real.arccos`, and interval and set integrals).
--
--   **Where it is used.** This vocabulary accompanies the twisted orbital transforms `twistedSplitTransform` and `twistedEllipticTransform` of the imported module: the fibre terms are the level-wise integrands through which the split and elliptic twisted transforms of `monomialInput` are compared, and the bidegree $(0,0)$ case supplies the pairing identity used in the automorphic input to the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_GL2TwistedMonomialFibres.lean

import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

noncomputable section

namespace AutomorphicForm.GL2Twisted

def invFrobSq (g : GL (Fin 2) ℂ) : ℝ :=
  (Matrix.trace ((g : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.conjTranspose (g : Matrix (Fin 2) (Fin 2) ℂ))).re

def invTraceNorm (g : GL (Fin 2) ℂ) : ℂ :=
  Matrix.trace ((g * conjEntries g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)

def invSecondRe (g : GL (Fin 2) ℂ) : ℝ :=
  (Matrix.trace (((g * conjEntries g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
    ((g : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.conjTranspose (g : Matrix (Fin 2) (Fin 2) ℂ)))).re

def invAbsDet (g : GL (Fin 2) ℂ) : ℝ :=
  ‖Matrix.det (g : Matrix (Fin 2) (Fin 2) ℂ)‖

def invDifference (g : GL (Fin 2) ℂ) : ℝ :=
  (invSecondRe g - invFrobSq g * (invTraceNorm g).re + 2 * invAbsDet g ^ 2) / invAbsDet g

def monomialInput (i l : ℕ) (g : GL (Fin 2) ℂ) : ℝ :=
  ((invFrobSq g - (invTraceNorm g).re + invDifference g) / (2 * (invFrobSq g + 2 * invAbsDet g))) ^ i *
    ((invFrobSq g - (invTraceNorm g).re - invDifference g) / (2 * (invFrobSq g - 2 * invAbsDet g))) ^ l

def fibreMonomialFactor (i l : ℕ) (T d x : ℝ) : ℝ :=
  (T - x) ^ (i + l) / ((T + 2 * d) ^ i * (T - 2 * d) ^ l)

def fibreArcIntegral (i l : ℕ) (Ψ : ℝ) : ℝ :=
  ∫ ψ in (-(Ψ / 2))..(Ψ / 2), Real.cos ψ ^ (2 * i) * Real.sin ψ ^ (2 * l)

def ellipticArcLength (T r θ : ℝ) : ℝ :=
  Real.arccos ((2 * r - T * Real.cos θ) / (T - 2 * r * Real.cos θ))

def ellipticFibreTerm (i l : ℕ) (T r θ : ℝ) : ℂ :=
  ((4 * Real.pi * Real.sin θ / r : ℝ) : ℂ) *
    ((fibreMonomialFactor i l T r (2 * r * Real.cos θ) * fibreArcIntegral i l (ellipticArcLength T r θ) : ℝ) : ℂ)

def splitFibreTerm (i l : ℕ) (T a₁ a₂ : ℝ) : ℂ :=
  ((1 / 2 * fibreMonomialFactor i l T (Real.sqrt (a₁ * a₂)) (a₁ + a₂) * fibreArcIntegral i l (2 * Real.pi) : ℝ) : ℂ)

def ellipticFibreSide (i l : ℕ) (c : ℝ → ℂ) (r θ : ℝ) : ℂ :=
  ∫ T in Set.Ioi (2 * r), c T * ellipticFibreTerm i l T r θ

def splitFibreSide (i l : ℕ) (c : ℝ → ℂ) (a₁ a₂ : ℝ) : ℂ :=
  ∫ T in Set.Ioi (a₁ + a₂), c T * splitFibreTerm i l T a₁ a₂

end AutomorphicForm.GL2Twisted

end


