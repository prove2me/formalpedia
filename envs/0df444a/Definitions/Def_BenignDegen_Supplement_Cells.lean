-- Prove2me | Definitions.Def_BenignDegen_Supplement_Cells
-- name    : BenignDegen_Supplement_Cells
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:30:40.107612+00:00
-- url     : https://prove2.me/theorems/077e9ea6-85f9-453d-9af9-2be08614730c
-- title:
--   The cells $\mathcal Q(a,d)$, $\mathcal E(a,d)$, $\mathcal E_{\mathrm{sc}}(a,d)$ and the first exact order $d_\star(f)$
-- statement:
--   Fix $a\in\{\pm1\}^n$, an order $d$, and $u=b_d(a)=(a^T)_{T\in\mathcal I_d}$.
--
--   1. The **normalized coefficient space** $\mathcal Q(a,d)=\{g\in\mathcal P_{\le2d}: g(a)=0\}$.
--   2. The **exact cell** $\mathcal E(a,d)=\{g\in\mathcal Q(a,d): \operatorname{argmin}_{X\in\mathcal X_d}\langle C_g,X\rangle=\{uu^\top\}\}$.
--   3. The **strictly complementary cell** $\mathcal E_{\mathrm{sc}}(a,d)=\{g\in\mathcal Q(a,d):\exists S\succeq0,\ G_d(S)=g,\ \ker S=\operatorname{span}\{u\}\}$.
--   4. For $f$ and a candidate minimizer $x_\star$, the set of orders of (2.5),
--   $$
--   \{1\le d\le n:\ \deg f\le 2d,\ \operatorname{argmin}(P_d)=\{b_d(x_\star)b_d(x_\star)^\top\}\},
--   $$
--   and $d_\star(f)$, its least element.
--
--   Here $\mathcal X_d$ is the Boolean moment body, $C_g$ the canonical cost matrix and $G_d$ the Gram-to-polynomial map of the base mission. These are the objects of Theorems 6.2 and 6.3.
--
--   **Formalization Note** Polynomials are coefficient functions $\mathrm{Finset}(\mathrm{Fin}\,n)\to\mathbb R$; $\ker S$ is the kernel of $v\mapsto Sv$ on $\mathbb R^{\mathcal I_d}$. $d_\star(f)$ is `sInf` of the set in item 4; it is the minimum only when that set is nonempty, and every statement using it asserts nonemptiness.
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, §6, p.11 and Appendix G.2, (G.2), p.31 (cells); §2, (2.5), p.5 (d⋆)

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Boolean

namespace BenignDegen

namespace Supplement

open SunNLSDP.Equiv Matrix

noncomputable section

/-! # The fixed-order cells `Q(a,d)`, `E(a,d)`, `E_sc(a,d)` and the first exact order `d⋆(f)`

Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*,
arXiv:2610.20270v1, §6, p.11 and Appendix G.2, (G.2), p.31 (the cells); §2, (2.5), p.5
(`d⋆(f)`).

**Formalization Note** Square-free polynomials are coefficient functions
`Finset (Fin n) → ℝ`; `P_{≤2d}` is `DegLe g (2d)`; `g(a)` is `evalPoly g a`; `argmin(P_d)` is
the published `argminPd`; `G_d` is the published `Gd` (coefficientwise). `ker S` is the kernel of
the linear map `v ↦ S v` on `ℝ^{I_d}`, and `span{u}` the line through `u = b_d(a)`. -/

/-- The normalized coefficient space `Q(a,d) := {g ∈ P_{≤2d} : g(a) = 0}` (p.11, (G.2)). -/
def Qcell (n d : ℕ) (a : Fin n → ℤˣ) : Set (Finset (Fin n) → ℝ) :=
  {g | DegLe g (2 * d) ∧ evalPoly g a = 0}

/-- The exact cell `E(a,d) := {g ∈ Q(a,d) : argmin_{X ∈ X_d} ⟨C_g, X⟩ = {uu^⊤}}`, `u = b_d(a)`
(p.11, (G.2)). -/
def Ecell (n d : ℕ) (a : Fin n → ℤˣ) : Set (Finset (Fin n) → ℝ) :=
  {g | g ∈ Qcell n d a ∧ UniqueRankOneOpt n d g a}

/-- The strictly complementary cell
`E_sc(a,d) := {g ∈ Q(a,d) : ∃ S ⪰ 0, G_d(S) = g, ker(S) = span{u}}`, `u = b_d(a)`
(p.11, (G.2)). -/
def EscCell (n d : ℕ) (a : Fin n → ℤˣ) : Set (Finset (Fin n) → ℝ) :=
  {g | g ∈ Qcell n d a ∧ ∃ S ∈ psdCone (Idx n d), Gd n d S = g ∧
    LinearMap.ker (Matrix.toLin' S.toMat) =
      Submodule.span ℝ {(WithLp.ofLp (bvec n d a) : Idx n d → ℝ)}}

/-- The orders entering (2.5): `{1 ≤ d ≤ n : deg f ≤ 2d, argmin(P_d) = {b_d(x⋆)b_d(x⋆)^⊤}}`. -/
def dStarSet (n : ℕ) (f : Finset (Fin n) → ℝ) (xs : Fin n → ℤˣ) : Set ℕ :=
  {d | 1 ≤ d ∧ d ≤ n ∧ DegLe f (2 * d) ∧ UniqueRankOneOpt n d f xs}

/-- The first order of unique rank-one exactness `d⋆(f)` (2.5), the least element of
`dStarSet n f x⋆`. It is meaningful only when that set is nonempty ("`d⋆(f) ≤ n` is well
defined"), which every statement using it asserts separately. -/
def dStar (n : ℕ) (f : Finset (Fin n) → ℝ) (xs : Fin n → ℤˣ) : ℕ :=
  sInf (dStarSet n f xs)

end

end Supplement

end BenignDegen


