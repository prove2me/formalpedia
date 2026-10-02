-- Prove2me | Definitions.Def_HunterPDE_Hyperbolic_Galerkin
-- name    : HunterPDE_Hyperbolic_Galerkin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:33:25.103977+00:00
-- url     : https://prove2.me/theorems/673b5224-595b-48bc-92f3-4cbd412e3e2d
-- title:
--   Galerkin spaces E_N, projections P_N ((6.15)–(6.17)) and approximate solutions (Definition 7.4)
-- statement:
--   Let $\{w_k\}_{k\ge1}$ be an orthonormal basis of $L^2(\Omega)$ of eigenfunctions of the Dirichlet Laplacian, $-\Delta w_k = \lambda_k w_k$, $w_k \in H^1_0(\Omega)$ (6.16), the equation holding weakly: $\int_\Omega Dw_k\cdot Dv\,dx = \lambda_k (w_k, v)_{L^2}$ for all $v \in H^1_0(\Omega)$. Let $E_N = \langle w_1, \dots, w_N\rangle$ (6.15) and $P_N$ the orthogonal projection (6.17), $P_N\big(\sum_k c_k w_k\big) = \sum_{k=1}^N c_k w_k$ with $c_k = (u, w_k)_{L^2}$.
--
--   **Definition 7.4.** A function $u_N : [0,T] \to E_N$ is an **approximate solution** of (7.5) if (1) $u_N, u_{Nt}, u_{Ntt} \in L^2(0,T;E_N)$; (2) for every $v \in E_N$,
--   $$(u_{Ntt}(t), v)_{L^2} + a(u_N(t), v; t) = (f(t), v)_{L^2} \quad \text{for a.e. } t \in (0,T) \qquad (7.9);$$
--   (3) $u_N(0) = P_N g$ and $u_{Nt}(0) = P_N h$.
--
--   **Formalization Note.** The basis is indexed from $0$: Lean's `w k` is the book's $w_{k+1}$, and $E_N$ is the span of `w 0, …, w (N-1)`. $P_N$ takes values in $E_N \subset H^1_0(\Omega)$ and is applied to $g$ through $H^1_0 \hookrightarrow L^2$. The initial values in (3) are those of the continuous representatives, which exist by $u_N \in H^2(0,T;E_N) \subset C^1([0,T];E_N)$ (p. 214); `IsApproxSolution` therefore requires $u_N, u_{Nt}$ to be continuous on $[0,T]$, which selects the representative and adds no condition on the class.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), pp. 181–182, Eqs. (6.15)–(6.17); p. 214, Definition 7.4

import Mathlib
import Definitions.Def_HunterPDE_Hyperbolic_H10
import Definitions.Def_HunterPDE_Hyperbolic_WeakTimeDeriv
import Definitions.Def_HunterPDE_Hyperbolic_WaveOperator

namespace HunterPDE.Hyperbolic

open MeasureTheory Set

/-- The Galerkin basis of (6.15)–(6.16) (Hunter, p. 181): `{w_k}` is an orthonormal basis of
`L²(Ω)` consisting of eigenfunctions of the Dirichlet Laplacian, `−Δ w_k = λ_k w_k`,
`w_k ∈ H¹₀(Ω)`, the eigenvalue equation taken in the weak sense
`∫_Ω Dw_k · Dv dx = λ_k (w_k, v)_{L²}` for all `v ∈ H¹₀(Ω)`.
The index is 0-based: Lean's `w k` is the book's `w_{k+1}`. -/
def IsDirichletEigenbasis {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (w : ℕ → H10 n Ω) (lam : ℕ → ℝ) : Prop :=
  Orthonormal ℝ (fun k => toL2 n Ω (w k)) ∧
    (Submodule.span ℝ (range fun k => toL2 n Ω (w k))).topologicalClosure = ⊤ ∧
    ∀ k (v : H10 n Ω), ∫ x in Ω, inner ℝ (grad (w k) x) (grad v x) =
      lam k * inner ℝ (toL2 n Ω (w k)) (toL2 n Ω v)

/-- The Galerkin space `E_N = ⟨w₁, …, w_N⟩ ⊂ H¹₀(Ω)` of (6.15): the span of the first `N` basis
vectors (Lean's `w 0, …, w (N−1)`). -/
noncomputable def galerkinSpace {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (w : ℕ → H10 n Ω) (N : ℕ) : Submodule ℝ (H10 n Ω) :=
  Submodule.span ℝ (range fun k : Fin N => w k)

/-- The orthogonal projection (6.17) `P_N : L²(Ω) → E_N`,
`P_N(∑_k c_k w_k) = ∑_{k=1}^N c_k w_k` with `c_k = (u, w_k)_{L²}`, valued in `E_N ⊂ H¹₀(Ω)`.
On `g ∈ H¹₀(Ω)` it is applied to `g` regarded in `L²(Ω)`. -/
noncomputable def galerkinProj {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (w : ℕ → H10 n Ω) (N : ℕ) (u : L2 n Ω) : H10 n Ω :=
  ∑ k : Fin N, inner ℝ u (toL2 n Ω (w k)) • w k

/-- Definition 7.4 (Hunter, p. 214): `u_N : [0, T] → E_N` is an approximate solution of (7.5),
with first and second weak time derivatives `u_Nt`, `u_Ntt`, if
(1) `u_N, u_Nt, u_Ntt` take values in `E_N` on `[0, T]` and lie in `L²(0, T; E_N)`, `u_Nt` being
the weak derivative of `u_N` and `u_Ntt` that of `u_Nt`;
(2) (7.9) for every `v ∈ E_N`: `(u_Ntt(t), v)_{L²} + a(u_N(t), v; t) = (f(t), v)_{L²}` for a.e.
`t ∈ (0, T)`;
(3) `u_N(0) = P_N g` and `u_Nt(0) = P_N h`.
The initial values in (3) are those of the continuous representatives, which exist because
`u_N ∈ H²(0, T; E_N) ⊂ C¹([0, T]; E_N)` (p. 214); accordingly `u_N` and `u_Nt` are required to be
continuous on `[0, T]` (this selects the representative, it adds no condition on the class). -/
def IsApproxSolution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (T : ℝ) (P : Coeffs n)
    (w : ℕ → H10 n Ω) (N : ℕ) (f : ℝ → L2 n Ω) (g : H10 n Ω) (h : L2 n Ω)
    (uN uN_t uN_tt : ℝ → H10 n Ω) : Prop :=
  (∀ t ∈ Icc 0 T, uN t ∈ galerkinSpace w N ∧ uN_t t ∈ galerkinSpace w N ∧
      uN_tt t ∈ galerkinSpace w N) ∧
    MemLp uN 2 (volume.restrict (Ioo 0 T)) ∧ MemLp uN_t 2 (volume.restrict (Ioo 0 T)) ∧
    MemLp uN_tt 2 (volume.restrict (Ioo 0 T)) ∧
    HasWeakTimeDeriv T uN uN_t ∧ HasWeakTimeDeriv T uN_t uN_tt ∧
    (∀ v ∈ galerkinSpace w N, ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      inner ℝ (toL2 n Ω (uN_tt t)) (toL2 n Ω v) + form P (uN t) v t =
        inner ℝ (f t) (toL2 n Ω v)) ∧
    ContinuousOn uN (Icc 0 T) ∧ ContinuousOn uN_t (Icc 0 T) ∧
    uN 0 = galerkinProj w N (toL2 n Ω g) ∧ uN_t 0 = galerkinProj w N h

end HunterPDE.Hyperbolic


