-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_SeparableStates
-- name    : QuantumSepPoly_Frobenius_SeparableStates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:01.044861+00:00
-- url     : https://prove2.me/theorems/c70e3dc5-c56c-4e82-90fb-50a0081e5101
-- title:
--   Pure-product separable states, support, and distance
-- statement:
--   For positive local dimension $d$, let
--   $$\operatorname{Sep}(d,d)=\operatorname{conv}_{\mathbb R}\{(x\otimes y)(x\otimes y)^*: \|x\|_2=\|y\|_2=1\}.$$
--   A density matrix is Hermitian, positive semidefinite, and trace one. Define $h_{\rm Sep}(M)$ as the supremum of $\operatorname{Re}\operatorname{Tr}(M\psi)$ over this set and $\operatorname{distSep}_d(\rho)$ as the infimum of $\|\rho-\psi\|_F$. Separate geometry statements require attainment and compactness, so these represent the source maxima and minima. No decomposition, optimizer, or distance value is an input.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), §§2–5, p. 8 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_MatrixGeometry

noncomputable section
open scoped ComplexOrder

namespace QuantumSepPoly.Frobenius

/-- §2.4, p.8: the real convex hull of all pure unit product projectors. -/
def Sep (d : ℕ) : Set (Bip d) := convexHull ℝ
  {R | ∃ x y : Vec d, vecSq x = 1 ∧ vecSq y = 1 ∧ R = productDensity x y}

def IsDensity {d : ℕ} (R : Bip d) : Prop := R.IsHermitian ∧ R.PosSemidef ∧ R.trace = 1

/-- Computed from Sep, never a free scalar or an optimization oracle. -/
def support {d : ℕ} (M : Bip d) : ℝ := sSup ((fun R => (M * R).trace.re) '' Sep d)

def distanceSep {d : ℕ} (R : Bip d) : ℝ := sInf ((fun S => frob (R - S)) '' Sep d)

end QuantumSepPoly.Frobenius


