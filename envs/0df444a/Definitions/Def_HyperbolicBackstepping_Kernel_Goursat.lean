-- Prove2me | Definitions.Def_HyperbolicBackstepping_Kernel_Goursat
-- name    : HyperbolicBackstepping_Kernel_Goursat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T12:35:48.227328+00:00
-- url     : https://prove2.me/theorems/28b2fad8-5752-4ee7-9251-df9f8ce1afd9
-- title:
--   Appendix A, pp. 18–21 — four-component Goursat data, characteristics, and integral iteration
-- statement:
--   This file fixes the data, the characteristic curves, the integral operators and the constants of the generalized Goursat problem of Appendix A of Coron–Vazquez–Krstic–Bastin.
--
--   **Data.** Let $\mathcal T=\{(x,\xi):0\le\xi\le x\le1\}$. The data of the system are
--
--   1. two speeds $\epsilon_1,\epsilon_2$, continuous and strictly positive on $[0,1]$;
--   2. forcing terms $g_1,\dots,g_4$ and coupling coefficients $C_{ji}$ ($i,j=1,\dots,4$), continuous on $\mathcal T$;
--   3. boundary functions $h_1,\dots,h_4$ and $q_1,\dots,q_4$, continuous on $[0,1]$.
--
--   They describe the $4\times4$ hyperbolic system (A.1)–(A.4),
--   $$\epsilon_1(x)F^1_x+\epsilon_1(\xi)F^1_\xi,\quad \epsilon_1(x)F^2_x-\epsilon_2(\xi)F^2_\xi,\quad \epsilon_2(x)F^3_x-\epsilon_1(\xi)F^3_\xi,\quad \epsilon_2(x)F^4_x+\epsilon_2(\xi)F^4_\xi \;=\; g_j+\sum_{i=1}^4 C_{ji}F^i,$$
--   with boundary conditions $F^1(x,0)=h_1(x)+q_1(x)F^2(x,0)+q_2(x)F^3(x,0)$, $F^2(x,x)=h_2(x)$, $F^3(x,x)=h_3(x)$, $F^4(x,0)=h_4(x)+q_3(x)F^2(x,0)+q_4(x)F^3(x,0)$ (A.5)–(A.7).
--
--   **Characteristics.** With $\phi_1(x)=\int_0^x\frac{dz}{\epsilon_1(z)}$, $\phi_2(x)=\int_0^x\frac{dz}{\epsilon_2(z)}$ and $\phi_3=\phi_1+\phi_2$ (A.8), the characteristic curves $(x_j(x,\xi,s),\xi_j(x,\xi,s))$, $s\in[0,s_j^F(x,\xi)]$, are those of (A.9)–(A.20); for example
--   $$x_1=\phi_1^{-1}(\phi_1(x)-\phi_1(\xi)+s),\quad \xi_1=\phi_1^{-1}(s),\quad s_1^F=\phi_1(\xi),$$
--   $$x_2=\phi_1^{-1}\big(\phi_1(\phi_3^{-1}(\phi_1(x)+\phi_2(\xi)))+s\big),\quad \xi_2=\phi_2^{-1}\big(\phi_2(\phi_3^{-1}(\phi_1(x)+\phi_2(\xi)))-s\big),\quad s_2^F=\phi_1(x)-\phi_1(\phi_3^{-1}(\phi_1(x)+\phi_2(\xi))),$$
--   and symmetrically for $j=3,4$ with the roles of $\epsilon_1,\epsilon_2$ exchanged.
--
--   **Integral form.** $G_j(x,\xi)=\int_0^{s_j^F}g_j(x_j,\xi_j)\,ds$ and $I_j[F](x,\xi)=\sum_{i=1}^4\int_0^{s_j^F}C_{ji}(x_j,\xi_j)F^i(x_j,\xi_j)\,ds$ (A.24)–(A.25). A **characteristic solution** is a quadruple $F=(F^1,\dots,F^4)$ such that, for every $j$ and every $(x,\xi)\in\mathcal T$,
--   $$F^j(x,\xi)=F^j\big(x_j(x,\xi,0),\xi_j(x,\xi,0)\big)+G_j(x,\xi)+I_j[F](x,\xi)\qquad\text{(A.23)},$$
--   and the boundary conditions (A.5)–(A.7) hold for every $x\in[0,1]$.
--
--   **Iteration.** $H_j(x,\xi)=h_j(x_j(x,\xi,0))$; the boundary source terms $\varphi_1,\varphi_4$ (A.27)–(A.28) and boundary operators $Q_1,Q_4$ (A.29)–(A.30) (with $\varphi_2=\varphi_3=0$, $Q_2=Q_3=0$); $\Phi_j[F]=Q_j[F]+I_j[F]$ (A.31); the source vector $\varphi=(H_j+G_j+\varphi_j)_j$ (A.32); and the increments $\Delta F^0=\varphi$, $\Delta F^{n+1}=\Phi[\Delta F^n]$ (p. 21).
--
--   **Constants** (A.35): $K_\epsilon=\max_{x\in[0,1]}\max\{1/\epsilon_1(x),1/\epsilon_2(x)\}$, $\bar C_{ji}=\max_{\mathcal T}|C_{ji}|$, $\bar q_i=\max_{[0,1]}|q_i|$, $\bar C=(1+\sum_i\bar q_i)(\sum_j\sum_i\bar C_{ji})$, and $\bar\phi=\max_{\mathcal T,\,i}|\varphi_i|$.
--
--   These objects are shared by the goal (Theorem A.1) and its milestones.
--
--   **Formalization Note** Lean indices $0,1,2,3$ stand for the paper's $1,2,3,4$; in particular `q 0, q 1` are $q_1,q_2$ of (A.5) and `q 2, q 3` are $q_3,q_4$ of (A.7), and `Cc j i` is $C_{j+1,i+1}$. The data are functions on $\mathbb R$ or $\mathbb R^2$ whose hypotheses (continuity, positivity) are imposed only on $[0,1]$ or $\mathcal T$; a continuous function on these compact sets extends continuously, so nothing is lost. $\phi_i^{-1}$ is `Function.invFunOn` on $[0,1]$, which is the true inverse on $[0,\phi_i(1)]$; every argument at which a statement evaluates it lies in that range (Lemma A.3). The maxima of (A.35) are `sSup` of the image of a compact set under a continuous map, hence attained. The paper's source terms $\varphi_j$ are named `boundarySrc` and the full source vector `src`, to avoid a clash with $\phi_i$. The `IsCharSolution` predicate records (A.23) and (A.5)–(A.7); Theorem A.1 imposes continuity separately on each component.
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, pp. 18–21, (A.1)–(A.35)

import Mathlib

namespace HyperbolicBackstepping.Kernel

/-- The closed characteristic triangle of Appendix A. -/
def Tri : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1}

/-- Data of (A.1)–(A.7). Indices `0,1,2,3` represent the paper's `1,2,3,4`.
The four entries of `q` represent `q₁,q₂,q₃,q₄`, respectively. -/
structure GoursatData where
  eps1 : ℝ → ℝ
  eps2 : ℝ → ℝ
  g : Fin 4 → ℝ → ℝ → ℝ
  Cc : Fin 4 → Fin 4 → ℝ → ℝ → ℝ
  h : Fin 4 → ℝ → ℝ
  q : Fin 4 → ℝ → ℝ
  eps1_cont : ContinuousOn eps1 (Set.Icc 0 1)
  eps2_cont : ContinuousOn eps2 (Set.Icc 0 1)
  eps1_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < eps1 x
  eps2_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < eps2 x
  g_cont : ∀ j, ContinuousOn (fun p : ℝ × ℝ => g j p.1 p.2) Tri
  Cc_cont : ∀ j i, ContinuousOn (fun p : ℝ × ℝ => Cc j i p.1 p.2) Tri
  h_cont : ∀ j, ContinuousOn (h j) (Set.Icc 0 1)
  q_cont : ∀ j, ContinuousOn (q j) (Set.Icc 0 1)

/-- The characteristic travel-time coordinates (A.8). -/
noncomputable def phi1 (D : GoursatData) (x : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..x, 1 / D.eps1 z

noncomputable def phi2 (D : GoursatData) (x : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..x, 1 / D.eps2 z

noncomputable def phi3 (D : GoursatData) (x : ℝ) : ℝ := phi1 D x + phi2 D x

/-- A choice of inverse on `[0,1]`; when applied to the strictly increasing travel-time
coordinates below, only in-range values occur in the statements. -/
noncomputable def phiInv (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  Function.invFunOn f (Set.Icc 0 1) y

/-- The diagonal starting point of characteristics 2 and 3. -/
noncomputable def start2 (D : GoursatData) (x ξ : ℝ) : ℝ :=
  phiInv (phi3 D) (phi1 D x + phi2 D ξ)

noncomputable def start3 (D : GoursatData) (x ξ : ℝ) : ℝ :=
  phiInv (phi3 D) (phi2 D x + phi1 D ξ)

/-- The terminal characteristic parameters (A.17)–(A.20). -/
noncomputable def sF (D : GoursatData) (j : Fin 4) (x ξ : ℝ) : ℝ :=
  if j = 0 then phi1 D ξ
  else if j = 1 then phi1 D x - phi1 D (start2 D x ξ)
  else if j = 2 then phi2 D x - phi2 D (start3 D x ξ)
  else phi2 D ξ

/-- The first coordinates of (A.9), (A.11), (A.13), and (A.15). -/
noncomputable def charX (D : GoursatData) (j : Fin 4) (x ξ s : ℝ) : ℝ :=
  if j = 0 then phiInv (phi1 D) (phi1 D x - phi1 D ξ + s)
  else if j = 1 then phiInv (phi1 D) (phi1 D (start2 D x ξ) + s)
  else if j = 2 then phiInv (phi2 D) (phi2 D (start3 D x ξ) + s)
  else phiInv (phi2 D) (phi2 D x - phi2 D ξ + s)

/-- The second coordinates of (A.10), (A.12), (A.14), and (A.16). -/
noncomputable def charXi (D : GoursatData) (j : Fin 4) (x ξ s : ℝ) : ℝ :=
  if j = 0 then phiInv (phi1 D) s
  else if j = 1 then phiInv (phi2 D) (phi2 D (start2 D x ξ) - s)
  else if j = 2 then phiInv (phi1 D) (phi1 D (start3 D x ξ) - s)
  else phiInv (phi2 D) s

/-- The domain of the `j`th characteristic in Lemma A.3. -/
noncomputable def CharDomain (D : GoursatData) (j : Fin 4) : Set ((ℝ × ℝ) × ℝ) :=
  {p | p.1 ∈ Tri ∧ p.2 ∈ Set.Icc 0 (sF D j p.1.1 p.1.2)}

/-- The forcing integral (A.24). -/
noncomputable def Gint (D : GoursatData) (j : Fin 4) (x ξ : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..sF D j x ξ, D.g j (charX D j x ξ s) (charXi D j x ξ s)

/-- The matrix-coupling integral (A.25), with row `j` and column `i`. -/
noncomputable def Iop (D : GoursatData) (F : Fin 4 → ℝ → ℝ → ℝ)
    (j : Fin 4) (x ξ : ℝ) : ℝ :=
  ∑ i : Fin 4, ∫ s in (0 : ℝ)..sF D j x ξ,
    D.Cc j i (charX D j x ξ s) (charXi D j x ξ s) *
      F i (charX D j x ξ s) (charXi D j x ξ s)

/-- The characteristic integral equations (A.23) and boundary conditions (A.5)–(A.7).
Continuity is imposed separately in Theorem A.1. -/
structure IsCharSolution (D : GoursatData) (F : Fin 4 → ℝ → ℝ → ℝ) : Prop where
  integral : ∀ j x ξ, (x, ξ) ∈ Tri →
    F j x ξ = F j (charX D j x ξ 0) (charXi D j x ξ 0) +
      Gint D j x ξ + Iop D F j x ξ
  edge1 : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    F 0 x 0 = D.h 0 x + D.q 0 x * F 1 x 0 + D.q 1 x * F 2 x 0
  diagonal2 : ∀ x ∈ Set.Icc (0 : ℝ) 1, F 1 x x = D.h 1 x
  diagonal3 : ∀ x ∈ Set.Icc (0 : ℝ) 1, F 2 x x = D.h 2 x
  edge4 : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    F 3 x 0 = D.h 3 x + D.q 2 x * F 1 x 0 + D.q 3 x * F 2 x 0

/-- The boundary values `H_j` in (A.26). -/
noncomputable def H (D : GoursatData) (j : Fin 4) (x ξ : ℝ) : ℝ :=
  D.h j (charX D j x ξ 0)

/-- The additional source terms `ϕ₁,ϕ₄` in (A.27)–(A.28); the other two vanish. -/
noncomputable def boundarySrc (D : GoursatData) (j : Fin 4) (x ξ : ℝ) : ℝ :=
  if j = 0 then
    D.q 0 (charX D 0 x ξ 0) *
        (H D 1 (charX D 0 x ξ 0) 0 + Gint D 1 (charX D 0 x ξ 0) 0) +
      D.q 1 (charX D 0 x ξ 0) *
        (H D 2 (charX D 0 x ξ 0) 0 + Gint D 2 (charX D 0 x ξ 0) 0)
  else if j = 3 then
    D.q 2 (charX D 3 x ξ 0) *
        (H D 1 (charX D 3 x ξ 0) 0 + Gint D 1 (charX D 3 x ξ 0) 0) +
      D.q 3 (charX D 3 x ξ 0) *
        (H D 2 (charX D 3 x ξ 0) 0 + Gint D 2 (charX D 3 x ξ 0) 0)
  else 0

/-- The boundary coupling terms `Q₁,Q₄` in (A.29)–(A.30). -/
noncomputable def Qop (D : GoursatData) (F : Fin 4 → ℝ → ℝ → ℝ)
    (j : Fin 4) (x ξ : ℝ) : ℝ :=
  if j = 0 then
    D.q 0 (charX D 0 x ξ 0) * Iop D F 1 (charX D 0 x ξ 0) 0 +
      D.q 1 (charX D 0 x ξ 0) * Iop D F 2 (charX D 0 x ξ 0) 0
  else if j = 3 then
    D.q 2 (charX D 3 x ξ 0) * Iop D F 1 (charX D 3 x ξ 0) 0 +
      D.q 3 (charX D 3 x ξ 0) * Iop D F 2 (charX D 3 x ξ 0) 0
  else 0

/-- The linear iteration operator `Φ` from (A.31). -/
noncomputable def PhiOp (D : GoursatData) (F : Fin 4 → ℝ → ℝ → ℝ)
    (j : Fin 4) (x ξ : ℝ) : ℝ := Qop D F j x ξ + Iop D F j x ξ

/-- The full source vector `ϕ` of (A.32). -/
noncomputable def src (D : GoursatData) (j : Fin 4) (x ξ : ℝ) : ℝ :=
  H D j x ξ + Gint D j x ξ + boundarySrc D j x ξ

/-- The increments `ΔFⁿ` defined after (A.33). -/
noncomputable def dF (D : GoursatData) : ℕ → Fin 4 → ℝ → ℝ → ℝ
  | 0 => src D
  | n + 1 => PhiOp D (dF D n)

/-- The characteristic-speed maximum `K_ε` in (A.35). -/
noncomputable def Keps (D : GoursatData) : ℝ :=
  sSup ((fun x : ℝ => max (1 / D.eps1 x) (1 / D.eps2 x)) '' Set.Icc 0 1)

/-- The entrywise maximum `C̄_{ji}` in (A.35). -/
noncomputable def Cbar (D : GoursatData) (j i : Fin 4) : ℝ :=
  sSup ((fun p : ℝ × ℝ => |D.Cc j i p.1 p.2|) '' Tri)

/-- The boundary-coefficient maximum `q̄ᵢ` in (A.35). -/
noncomputable def qbar (D : GoursatData) (i : Fin 4) : ℝ :=
  sSup ((fun x : ℝ => |D.q i x|) '' Set.Icc 0 1)

/-- The combined coupling constant `C̄` in (A.35). -/
noncomputable def CbarTot (D : GoursatData) : ℝ :=
  (1 + ∑ i : Fin 4, qbar D i) * (∑ j : Fin 4, ∑ i : Fin 4, Cbar D j i)

/-- The maximum of the full source vector `ϕ` in (A.35). -/
noncomputable def phiBar (D : GoursatData) : ℝ :=
  sSup {r : ℝ | ∃ j : Fin 4, ∃ p ∈ Tri, r = |src D j p.1 p.2|}

end HyperbolicBackstepping.Kernel


