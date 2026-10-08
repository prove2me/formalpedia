-- Prove2me | Definitions.Def_MFGPlanning_Penalized_Grid
-- name    : MFGPlanning_Penalized_Grid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:11:00.286998+00:00
-- url     : https://prove2.me/theorems/9ec0ac06-3ce4-4b8f-98f6-79153e6b266a
-- title:
--   The periodic grid $\mathbb T^2_h$, the operators $D_h$, $\Delta_h$, $\mathcal B$, $\mathrm{div}_h$ and the set $\mathcal K$ ((10)–(12), (15), (17))
-- statement:
--   Fix integers $N_h \ge 1$ and $N_T \ge 1$, a horizon $T > 0$ and a viscosity $\nu \ge 0$. Let $h = 1/N_h$ and $\Delta t = T/N_T$. The uniform grid $\mathbb T^2_h$ on the two-dimensional torus has points $x_{i,j}$, $(i,j) \in (\mathbb Z/N_h\mathbb Z)^2$, so that all indices are periodic. A grid function is a map $U : \mathbb T^2_h \to \mathbb R$. The data also comprise a numerical Hamiltonian $g(x_{i,j}, q)$, $q = (q_1, q_2, q_3, q_4) \in \mathbb R^4$, given at the grid points, a function $W : \mathbb R \to \mathbb R$ with $V = W'$, and grid functions $(m_0)_{i,j}$, $(m_T)_{i,j}$.
--
--   The finite difference operators are
--   $$
--   (D_1^+U)_{i,j} = \frac{U_{i+1,j} - U_{i,j}}{h}, \qquad (D_2^+U)_{i,j} = \frac{U_{i,j+1} - U_{i,j}}{h},
--   $$
--   $$
--   [D_hU]_{i,j} = \big((D_1^+U)_{i,j}, (D_1^+U)_{i-1,j}, (D_2^+U)_{i,j}, (D_2^+U)_{i,j-1}\big),
--   $$
--   $$
--   (\Delta_hU)_{i,j} = -\frac{1}{h^2}\big(4U_{i,j} - U_{i+1,j} - U_{i-1,j} - U_{i,j+1} - U_{i,j-1}\big).
--   $$
--   The transport operator $\mathcal B_{i,j}(U, M)$ is
--   $$
--   \frac1h\Big(M_{i,j}\tfrac{\partial g}{\partial q_1}(x_{i,j},[D_hU]_{i,j}) - M_{i-1,j}\tfrac{\partial g}{\partial q_1}(x_{i-1,j},[D_hU]_{i-1,j}) + M_{i+1,j}\tfrac{\partial g}{\partial q_2}(x_{i+1,j},[D_hU]_{i+1,j}) - M_{i,j}\tfrac{\partial g}{\partial q_2}(x_{i,j},[D_hU]_{i,j})
--   $$
--   $$
--   + M_{i,j}\tfrac{\partial g}{\partial q_3}(x_{i,j},[D_hU]_{i,j}) - M_{i,j-1}\tfrac{\partial g}{\partial q_3}(x_{i,j-1},[D_hU]_{i,j-1}) + M_{i,j+1}\tfrac{\partial g}{\partial q_4}(x_{i,j+1},[D_hU]_{i,j+1}) - M_{i,j}\tfrac{\partial g}{\partial q_4}(x_{i,j},[D_hU]_{i,j})\Big),
--   $$
--   the discrete divergence of a field $Z = (Z^1, Z^2, Z^3, Z^4)$ is $\mathrm{div}_h(Z)_{i,j} = (D_1^+Z^1)_{i-1,j} + (D_1^+Z^2)_{i,j} + (D_2^+Z^3)_{i,j-1} + (D_2^+Z^4)_{i,j}$, and the set of discrete probability densities is
--   $$
--   \mathcal K = \Big\{ M : h^2 \sum_{i,j} M_{i,j} = 1,\ M_{i,j} \ge 0 \Big\}.
--   $$
--   Finally $\|[D_hU]\|_\infty$ is the maximum of $|[D_hU]^k_{i,j}|$ over all grid points and $k = 1, \dots, 4$.
--
--   These are the objects every statement of the mission is written in.
--
--   **Formalization Note** Grid points are `ZMod Nh × ZMod Nh`; the components $q_1, \dots, q_4$ and $Z^1, \dots, Z^4$ are the indices `0, 1, 2, 3` of `Fin 4`. The partial derivative $\partial g/\partial q_k$ is the Fréchet derivative of $q \mapsto g(x_{i,j}, q)$ applied to the $k$-th basis vector; it is meaningful under (G3). The page indexes $\mathcal K$ by $0 \le i, j < N_T$, a slip for $N_h$.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), §2, eqs. (10)–(12), (15), (17), pp. 4–6; div_h, p. 7

import Mathlib

namespace MFGPlanning.Penalized

/-- The data of the discrete planning problem of Achdou, Camilli, Capuzzo-Dolcetta,
*Mean field games: numerical methods for the planning problem*, hal-00465404v1 (2010),
§2, pp. 4–6 (PDF 5–7) and (24), p. 6 (PDF 7), in dimension d = 2.

* `Nh` = N_h = 1/h, the number of grid points per direction of the torus T²_h (p. 4);
* `NT` = N_T, the number of time steps, Δt = T/N_T (p. 4);
* `ν ≥ 0` the viscosity ("we assume that ν is nonnegative", p. 6);
* `g p q` the numerical Hamiltonian g(x_{i,j}, q) at the grid point p = (i, j);
* `W` the potential with V = W' ((24), p. 6);
* `m0`, `mT` the grid functions (m_0)_{i,j}, (m_T)_{i,j}.

Formalization Note: grid points are `ZMod Nh × ZMod Nh`, so the indices are periodic
(the torus T²_h); the side conditions `0 < Nh`, `0 < NT`, `0 < T` are implicit in the paper. -/
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

instance (d : Data) : NeZero d.Nh := ⟨d.hNh.ne'⟩

/-- The grid points x_{i,j} of the torus T²_h, indexed periodically by `ZMod Nh × ZMod Nh`. -/
abbrev Pt (d : Data) : Type := ZMod d.Nh × ZMod d.Nh

/-- The mesh step h = 1/N_h (p. 4). -/
noncomputable def Data.h (d : Data) : ℝ := (d.Nh : ℝ)⁻¹

/-- The time step Δt = T/N_T (p. 4). -/
noncomputable def Data.Δt (d : Data) : ℝ := d.T / d.NT

/-- The coupling V = W' ((24), p. 6). -/
noncomputable def Data.V (d : Data) : ℝ → ℝ := deriv d.W

/-- (D₁⁺U)_{i,j} = (U_{i+1,j} − U_{i,j})/h ((10), p. 4). -/
noncomputable def D1 (d : Data) (U : Pt d → ℝ) (p : Pt d) : ℝ :=
  (U (p.1 + 1, p.2) - U p) / d.h

/-- (D₂⁺U)_{i,j} = (U_{i,j+1} − U_{i,j})/h ((10), p. 4). -/
noncomputable def D2 (d : Data) (U : Pt d → ℝ) (p : Pt d) : ℝ :=
  (U (p.1, p.2 + 1) - U p) / d.h

/-- [D_hU]_{i,j} = ((D₁⁺U)_{i,j}, (D₁⁺U)_{i−1,j}, (D₂⁺U)_{i,j}, (D₂⁺U)_{i,j−1}) ((11), p. 4).
Formalization Note: the components q₁, …, q₄ are the indices `0, 1, 2, 3` of `Fin 4`. -/
noncomputable def Dh (d : Data) (U : Pt d → ℝ) (p : Pt d) : Fin 4 → ℝ :=
  ![D1 d U p, D1 d U (p.1 - 1, p.2), D2 d U p, D2 d U (p.1, p.2 - 1)]

/-- (Δ_hU)_{i,j} = −(1/h²)(4U_{i,j} − U_{i+1,j} − U_{i−1,j} − U_{i,j+1} − U_{i,j−1}) ((12), p. 4). -/
noncomputable def lap (d : Data) (U : Pt d → ℝ) (p : Pt d) : ℝ :=
  -(1 / d.h ^ 2) * (4 * U p - U (p.1 + 1, p.2) - U (p.1 - 1, p.2) - U (p.1, p.2 + 1)
    - U (p.1, p.2 - 1))

/-- ∂g/∂q_{k+1}(x_{i,j}, q): the partial derivative of the numerical Hamiltonian in its
(k+1)-th momentum variable (`k : Fin 4`, indices 0–3 for q₁–q₄). Meaningful under (G3). -/
noncomputable def dg (d : Data) (p : Pt d) (q : Fin 4 → ℝ) (k : Fin 4) : ℝ :=
  fderiv ℝ (d.g p) q (Pi.single k 1)

/-- The discrete transport operator B_{i,j}(U, M) of (15), p. 5. -/
noncomputable def B (d : Data) (U M : Pt d → ℝ) (p : Pt d) : ℝ :=
  let pm1 : Pt d := (p.1 - 1, p.2)
  let pp1 : Pt d := (p.1 + 1, p.2)
  let pm2 : Pt d := (p.1, p.2 - 1)
  let pp2 : Pt d := (p.1, p.2 + 1)
  (1 / d.h) *
    ((M p * dg d p (Dh d U p) 0 - M pm1 * dg d pm1 (Dh d U pm1) 0
      + M pp1 * dg d pp1 (Dh d U pp1) 1 - M p * dg d p (Dh d U p) 1)
    + (M p * dg d p (Dh d U p) 2 - M pm2 * dg d pm2 (Dh d U pm2) 2
      + M pp2 * dg d pp2 (Dh d U pp2) 3 - M p * dg d p (Dh d U p) 3))

/-- The discrete divergence of p. 7:
div_h(Z)_{i,j} = (D₁⁺Z¹)_{i−1,j} + (D₁⁺Z²)_{i,j} + (D₂⁺Z³)_{i,j−1} + (D₂⁺Z⁴)_{i,j}
(Z¹, …, Z⁴ are the indices `0, 1, 2, 3` of `Fin 4`). -/
noncomputable def divh (d : Data) (Z : Pt d → Fin 4 → ℝ) (p : Pt d) : ℝ :=
  (Z p 0 - Z (p.1 - 1, p.2) 0) / d.h + (Z (p.1 + 1, p.2) 1 - Z p 1) / d.h
    + (Z p 2 - Z (p.1, p.2 - 1) 2) / d.h + (Z (p.1, p.2 + 1) 3 - Z p 3) / d.h

/-- The set K of discrete probability densities ((17), p. 6):
h² Σ_{i,j} M_{i,j} = 1 and M_{i,j} ≥ 0. -/
def InK (d : Data) (M : Pt d → ℝ) : Prop :=
  d.h ^ 2 * ∑ p, M p = 1 ∧ ∀ p, 0 ≤ M p

/-- ‖[D_hU]‖_∞ = max_{i,j} max_{k} |[D_hU]^k_{i,j}|, the maximum over all 4N_h² entries
of the discrete gradient (used in (13), p. 5). -/
noncomputable def supNormDh (d : Data) (U : Pt d → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x : Pt d × Fin 4 => |Dh d U x.1 x.2|)

end MFGPlanning.Penalized


