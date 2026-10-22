-- Prove2me | Definitions.Def_GeomDL_GroupConv_Model
-- name    : GeomDL_GroupConv_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:42.075179+00:00
-- url     : https://prove2.me/theorems/1134e225-e596-4660-add3-b0f2d21d92a7
-- title:
--   §4.3, pp. 41–42 — signal actions, pairing, group convolution, and the cyclic example
-- statement:
--   Let a group $G$ act on a domain $\Omega$. A scalar signal is a real-valued function on $\Omega$. For $g\in G$, the induced action on signals is
--
--   $$
--   (\rho(g)x)(u)=x(g^{-1}\cdot u).
--   $$
--
--   Given a measure $\mu$ on $\Omega$, the pairing and group convolution are
--
--   $$
--   \langle x,\theta\rangle_\mu=\int_\Omega x(u)\theta(u)\,d\mu(u),\qquad
--   (x\star\theta)(g)=\langle x,\rho(g)\theta\rangle_\mu.
--   $$
--
--   A signal $y:G\to\mathbb R$ on the group has the regular action $(\rho_G(h)y)(g)=y(h^{-1}g)$. For the cyclic example, the shift group $G=\mathbb Z_n$ (a copy of $\mathbb Z/n$ written multiplicatively) acts on the index set $\Omega=\mathbb Z_n$ by $g\cdot v=v-u$, where $u$ is the index identified with the shift $g$.
--
--   These definitions fix the two signal domains and the action conventions used in the equivariance theorem.
--
--   **Formalization Note** The pairing is the real Lebesgue integral. Lean assigns zero to an integral of a nonintegrable function; the theorem below remains an equality for these inputs under measure-preserving changes of variables. The cyclic shift group is a separate type `CyclicShiftGroup n`, so that its action is the page's $v\mapsto v-u$ rather than Mathlib's additive regular action $v\mapsto v+u$ on `Multiplicative (ZMod n)`.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.3, equation (14), pp. 41–43; cyclic example pp. 41–42

import Mathlib

namespace GeomDL.GroupConv

universe u v

variable {G : Type u} {Ω : Type v}

/-- The induced action of a group element on a real signal, §4.3, p. 41. -/
def signalAction [Group G] [MulAction G Ω] (g : G) (x : Ω → ℝ) : Ω → ℝ :=
  fun u => x (g⁻¹ • u)

/-- The real signal pairing with respect to the measure in §4.3, p. 41. -/
noncomputable def signalPairing [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (x θ : Ω → ℝ) : ℝ :=
  ∫ u, x u * θ u ∂μ

/-- Equation (14), the group convolution of a signal and a filter. -/
noncomputable def groupConvolution [Group G] [MulAction G Ω] [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (x θ : Ω → ℝ) : G → ℝ :=
  fun g => signalPairing μ x (signalAction g θ)

/-- The regular action on signals indexed by the group, §4.3, p. 43. -/
def regularAction [Group G] (h : G) (y : G → ℝ) : G → ℝ :=
  fun g => y (h⁻¹ * g)

/-- The cyclic shift group `G = ℤ_n` of pp. 41–42, a copy of `Multiplicative (ZMod n)`.
It is a separate type so that its action on the grid is the page's `g.v = v - u`, not
Mathlib's additive regular action `v + u`. -/
def CyclicShiftGroup (n : ℕ) : Type := Multiplicative (ZMod n)

instance (n : ℕ) : Group (CyclicShiftGroup n) :=
  inferInstanceAs (Group (Multiplicative (ZMod n)))

/-- The shift `g ∈ ℤ_n` identified with the index `u = 0, …, n − 1`. -/
def CyclicShiftGroup.ofShift {n : ℕ} (u : ZMod n) : CyclicShiftGroup n :=
  Multiplicative.ofAdd u

/-- The index `u` of a shift `g`. -/
def CyclicShiftGroup.toShift {n : ℕ} (g : CyclicShiftGroup n) : ZMod n :=
  Multiplicative.toAdd g

/-- The action of pp. 41–42 on `Ω = ℤ_n`: the shift identified with `u` sends `v` to `v - u`. -/
instance (n : ℕ) : MulAction (CyclicShiftGroup n) (ZMod n) where
  smul g v := v - g.toShift
  one_smul v := by
    show v - (1 : CyclicShiftGroup n).toShift = v
    rw [show (1 : CyclicShiftGroup n).toShift = 0 from rfl, sub_zero]
  mul_smul g h v := by
    show v - (g * h).toShift = (v - h.toShift) - g.toShift
    rw [show (g * h).toShift = g.toShift + h.toShift from rfl]; abel

end GeomDL.GroupConv


