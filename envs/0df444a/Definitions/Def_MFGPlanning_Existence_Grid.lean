-- Prove2me | Definitions.Def_MFGPlanning_Existence_Grid
-- name    : MFGPlanning_Existence_Grid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:11:02.242106+00:00
-- url     : https://prove2.me/theorems/cb2b358b-5e5d-413e-a9fe-1ab1bcba94cf
-- title:
--   The periodic grid $\mathbb T^2_h$, the operators $D_h$, $\Delta_h$, $\mathcal B$, $\mathrm{div}_h$ and the set $\mathcal K$ ((10)–(12), (15), (17))
-- statement:
--   Fix integers $N_h \ge 1$ and $N_T \ge 1$, a horizon $T > 0$ and a viscosity $\nu \ge 0$. Let $h = 1/N_h$ and $\Delta t = T/N_T$. The grid $\mathbb T^2_h$ is the uniform periodic grid on the two-dimensional torus, with points $x_{i,j}$ indexed by $(i,j) \in (\mathbb Z/N_h\mathbb Z)^2$; a grid function is a family $U = (U_{i,j})$ of real numbers. The data of the planning problem are a **numerical Hamiltonian** $g(x_{i,j}, q)$, $q = (q_1,q_2,q_3,q_4) \in \mathbb R^4$, given at the grid points; a function $W:\mathbb R\to\mathbb R$ with $V = W'$; and two grid functions $(m_0)_{i,j}$, $(m_T)_{i,j}$.
--
--   The finite-difference operators are
--   $$(D_1^+U)_{i,j} = \frac{U_{i+1,j}-U_{i,j}}{h},\qquad (D_2^+U)_{i,j} = \frac{U_{i,j+1}-U_{i,j}}{h},$$
--   $$[D_hU]_{i,j} = \big((D_1^+U)_{i,j}, (D_1^+U)_{i-1,j}, (D_2^+U)_{i,j}, (D_2^+U)_{i,j-1}\big),$$
--   $$(\Delta_h U)_{i,j} = -\frac1{h^2}\big(4U_{i,j}-U_{i+1,j}-U_{i-1,j}-U_{i,j+1}-U_{i,j-1}\big).$$
--   The transport operator $\mathcal B_{i,j}(U,M)$ is $\frac1h$ times
--   $$\Big(M_{i,j}\tfrac{\partial g}{\partial q_1}(x_{i,j},[D_hU]_{i,j}) - M_{i-1,j}\tfrac{\partial g}{\partial q_1}(x_{i-1,j},[D_hU]_{i-1,j}) + M_{i+1,j}\tfrac{\partial g}{\partial q_2}(x_{i+1,j},[D_hU]_{i+1,j}) - M_{i,j}\tfrac{\partial g}{\partial q_2}(x_{i,j},[D_hU]_{i,j})\Big)$$
--   $$+\Big(M_{i,j}\tfrac{\partial g}{\partial q_3}(x_{i,j},[D_hU]_{i,j}) - M_{i,j-1}\tfrac{\partial g}{\partial q_3}(x_{i,j-1},[D_hU]_{i,j-1}) + M_{i,j+1}\tfrac{\partial g}{\partial q_4}(x_{i,j+1},[D_hU]_{i,j+1}) - M_{i,j}\tfrac{\partial g}{\partial q_4}(x_{i,j},[D_hU]_{i,j})\Big).$$
--   For a field $Z = (Z^1,Z^2,Z^3,Z^4)$ of grid functions, the discrete divergence is
--   $$\mathrm{div}_h(Z)_{i,j} = (D_1^+Z^1)_{i-1,j} + (D_1^+Z^2)_{i,j} + (D_2^+Z^3)_{i,j-1} + (D_2^+Z^4)_{i,j}.$$
--   Finally, $\mathcal K$ is the set of discrete probability densities,
--   $$\mathcal K = \Big\{ M : h^2 \sum_{i,j} M_{i,j} = 1,\ M_{i,j}\ge 0 \Big\}.$$
--
--   These objects are shared by every statement of the mission: the discrete Hamilton–Jacobi and Fokker–Planck equations and the duality functionals are written with them.
--
--   **Formalization Note** Grid indices are elements of `ZMod Nh`, so $i\pm1$ is taken modulo $N_h$ (the torus). The components $q_1,\dots,q_4$ and $Z^1,\dots,Z^4$ are the indices `0, 1, 2, 3` of `Fin 4`. $\partial g/\partial q_k$ is the Fréchet derivative of $g(x_{i,j},\cdot)$ applied to the $k$-th unit vector; it is meaningful under (G3). The side conditions $N_h, N_T \ge 1$, $T > 0$, $\nu \ge 0$ are fields of the data structure. $g$ is only given at grid points, which is all the discrete statements use. The page indexes $\mathcal K$ by $0\le i,j<N_T$, a slip for $N_h$.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), §2, pp. 4–6, (10)–(12), (15), (17); §3.1, p. 7 (div_h)

import Mathlib

namespace MFGPlanning.Existence

/-- The data of the discrete planning problem of Achdou, Camilli, Capuzzo-Dolcetta, *Mean field games:
numerical methods for the planning problem*, hal-00465404v1 (2010), §2, pp. 4–6 (PDF 5–7) and §3.1,
pp. 6–7 (PDF 7–8): the number `Nh = 1/h` of grid points per direction of the torus `𝕋²_h`, the number
`NT` of time steps, the horizon `T`, the viscosity `ν ≥ 0`, the numerical Hamiltonian `g` evaluated at
the grid points `x_{i,j}`, the function `W` with `V = W'` of (24), and the discrete densities
`(m_0)_{i,j}`, `(m_T)_{i,j}`.

Formalization Note: the grid indices live in `ZMod Nh`, so `i ± 1` is periodic, as on the torus.
The arguments `q_1, …, q_4` of `g` are the indices `0, 1, 2, 3` of `Fin 4`. The side conditions
`1/h = Nh` an integer, `NT ≥ 1`, `T > 0` (p. 4) and `ν ≥ 0` (p. 6) are fields. -/
structure Data where
  Nh : ℕ
  NT : ℕ
  hNh : 0 < Nh
  hNT : 0 < NT
  T : ℝ
  hT : 0 < T
  ν : ℝ
  hν : 0 ≤ ν
  g : ZMod Nh × ZMod Nh → (Fin 4 → ℝ) → ℝ
  W : ℝ → ℝ
  m0 : ZMod Nh × ZMod Nh → ℝ
  mT : ZMod Nh × ZMod Nh → ℝ

instance (d : Data) : NeZero d.Nh := ⟨Nat.pos_iff_ne_zero.mp d.hNh⟩

instance (d : Data) : NeZero d.NT := ⟨Nat.pos_iff_ne_zero.mp d.hNT⟩

/-- The grid points `x_{i,j}` of the periodic grid `𝕋²_h` (p. 4), indexed by `(i, j) ∈ (ℤ/N_h)²`. -/
abbrev Data.Pt (d : Data) : Type := ZMod d.Nh × ZMod d.Nh

/-- The mesh step `h = 1/N_h` (p. 4). -/
noncomputable def Data.h (d : Data) : ℝ := (d.Nh : ℝ)⁻¹

/-- The time step `Δt = T/N_T` (p. 4). -/
noncomputable def Data.dt (d : Data) : ℝ := d.T / d.NT

/-- `V = W'` ((24), p. 6). -/
noncomputable def Data.V (d : Data) : ℝ → ℝ := deriv d.W

variable (d : Data)

/-- `(D₁⁺U)_{i,j} = (U_{i+1,j} − U_{i,j})/h` ((10), p. 4). -/
noncomputable def D1 (U : d.Pt → ℝ) (p : d.Pt) : ℝ := (U (p.1 + 1, p.2) - U p) / d.h

/-- `(D₂⁺U)_{i,j} = (U_{i,j+1} − U_{i,j})/h` ((10), p. 4). -/
noncomputable def D2 (U : d.Pt → ℝ) (p : d.Pt) : ℝ := (U (p.1, p.2 + 1) - U p) / d.h

/-- `[D_h U]_{i,j} = ((D₁⁺U)_{i,j}, (D₁⁺U)_{i−1,j}, (D₂⁺U)_{i,j}, (D₂⁺U)_{i,j−1})` ((11), p. 4);
component `k : Fin 4` is the paper's component `k + 1`. -/
noncomputable def Dh (U : d.Pt → ℝ) (p : d.Pt) : Fin 4 → ℝ :=
  ![D1 d U p, D1 d U (p.1 - 1, p.2), D2 d U p, D2 d U (p.1, p.2 - 1)]

/-- The discrete Laplacian
`(Δ_h U)_{i,j} = −(1/h²)(4U_{i,j} − U_{i+1,j} − U_{i−1,j} − U_{i,j+1} − U_{i,j−1})` ((12), p. 4). -/
noncomputable def lap (U : d.Pt → ℝ) (p : d.Pt) : ℝ :=
  -(1 / d.h ^ 2) * (4 * U p - U (p.1 + 1, p.2) - U (p.1 - 1, p.2) - U (p.1, p.2 + 1)
    - U (p.1, p.2 - 1))

/-- `∂g/∂q_{k+1}(x_{i,j}, q)`, the partial derivative of the numerical Hamiltonian at the grid point
`p` in the direction of component `k : Fin 4` (meaningful under (G3)). -/
noncomputable def dg (p : d.Pt) (q : Fin 4 → ℝ) (k : Fin 4) : ℝ :=
  fderiv ℝ (d.g p) q (Pi.single k 1)

/-- The operator `𝓑_{i,j}(U, M)` of (15), p. 5. -/
noncomputable def B (U M : d.Pt → ℝ) (p : d.Pt) : ℝ :=
  (1 / d.h) *
    ((M p * dg d p (Dh d U p) 0 - M (p.1 - 1, p.2) * dg d (p.1 - 1, p.2) (Dh d U (p.1 - 1, p.2)) 0
      + M (p.1 + 1, p.2) * dg d (p.1 + 1, p.2) (Dh d U (p.1 + 1, p.2)) 1
      - M p * dg d p (Dh d U p) 1)
    + (M p * dg d p (Dh d U p) 2 - M (p.1, p.2 - 1) * dg d (p.1, p.2 - 1) (Dh d U (p.1, p.2 - 1)) 2
      + M (p.1, p.2 + 1) * dg d (p.1, p.2 + 1) (Dh d U (p.1, p.2 + 1)) 3
      - M p * dg d p (Dh d U p) 3))

/-- The discrete divergence of (26), p. 7:
`div_h(Z)_{i,j} = (D₁⁺Z¹)_{i−1,j} + (D₁⁺Z²)_{i,j} + (D₂⁺Z³)_{i,j−1} + (D₂⁺Z⁴)_{i,j}`,
with `Z^{k+1}` the component `k : Fin 4`. -/
noncomputable def divh (Z : d.Pt → Fin 4 → ℝ) (p : d.Pt) : ℝ :=
  (Z p 0 - Z (p.1 - 1, p.2) 0) / d.h + (Z (p.1 + 1, p.2) 1 - Z p 1) / d.h
    + (Z p 2 - Z (p.1, p.2 - 1) 2) / d.h + (Z (p.1, p.2 + 1) 3 - Z p 3) / d.h

/-- The set `𝒦` of discrete probability densities ((17), p. 6):
`h² ∑_{i,j} M_{i,j} = 1` and `M_{i,j} ≥ 0`. -/
def InK (M : d.Pt → ℝ) : Prop := d.h ^ 2 * ∑ p, M p = 1 ∧ ∀ p, 0 ≤ M p

end MFGPlanning.Existence


