-- Prove2me | Definitions.Def_EJASpectral_RootDet_RootDetCone
-- name    : EJASpectral_RootDet_RootDetCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:09.022468+00:00
-- url     : https://prove2.me/theorems/d884f3ef-1d93-485b-8206-11ec4d65c7f7
-- title:
--   (96)–(98a), (102), pp. 23–24 — root-determinant φ, ζ, E = ℝ × Q, the cone K_rtdet, its barrier Γ, Ψ = −logdet, r̂ = P(w^{−1/2})r
-- statement:
--   Let $V$ be a Euclidean Jordan algebra of rank $d$ with cone of squares $\mathcal Q$, determinant $\det$ and quadratic representation $P$.
--
--   1. The **root-determinant** (geometric mean of the eigenvalues) is $$\varphi(w) := \det(w)^{1/d} = \prod_{i\in[\![d]\!]} w_i^{1/d}. \tag{96}$$
--   2. On $\mathcal E = \mathbb R\times\mathcal Q$, with points $\tilde u = (u,w)$, $$\zeta(\tilde u) := \varphi(w) - u. \tag{97}$$
--   3. The **root-determinant cone** is $$\mathcal K_{\mathrm{rtdet}} := \{(u,w)\in\mathbb R\times\mathcal Q : u\le\det(w)^{1/d}\}. \tag{98a}$$
--   4. Its barrier is $$\Gamma(\tilde u) := -\log(\zeta(\tilde u)) - \log\det(w), \tag{102}$$ and $\Psi(\tilde u) := -\log\det(w)$ is the standard barrier of the domain $\mathcal E$.
--   5. For $w\succ 0$ and $r\in V$, $\hat r := P(w^{-1/2})\,r$, where $w^{-1/2} = \sum_i w_i^{-1/2}c_i$.
--
--   $\mathcal K_{\mathrm{rtdet}}$ is the hypograph of the geometric mean of the eigenvalues; for $V=\mathbb S^d$ it is the hypograph of $\det(W)^{1/d}$ over the positive semidefinite cone, a cone used to model D-optimal design and related problems.
--
--   **Formalization Note** All objects are total functions: $\varphi$ is the real power `(det w) ^ (1/d)`, meaningful on $\mathcal Q$ where $\det w\ge0$; $\Gamma$, $\Psi$ and $\hat r$ use `Real.log` and real powers and are only evaluated on the interiors $\operatorname{int}(\mathcal K_{\mathrm{rtdet}})$, $\operatorname{int}(\mathcal E)$, $\operatorname{int}(\mathcal Q)$, where the logarithms and powers have positive arguments. Every theorem of the mission restricts to those interiors.
-- source:
--   Coey, Kapelevich & Vielma, Conic optimization with spectral functions on Euclidean Jordan algebras, arXiv:2103.04104v2, p. 23, (96), (97), (98a), r̂ := P(w^{−1/2})r; p. 24, (102), proof of Proposition 7.1 (Ψ)

import Mathlib
import Definitions.Def_EJASpectral_RootDet_EJA

namespace EJASpectral.RootDet

/-! # The root-determinant cone and its barrier (§7.1, §7.3, pp. 23–24)

Coey, Kapelevich & Vielma, arXiv:2103.04104v2, p. 23, (96)–(98a); p. 24, (102). -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {d : ℕ}

/-- `r̂ := P(w^{-1/2}) r` (p. 23), with `w^{-1/2} = Σᵢ wᵢ^{-1/2} cᵢ` the spectral function of
`t ↦ t^{-1/2}`. Meaningful for `w ∈ int Q`, where the eigenvalues are positive. -/
noncomputable def rhat (J : EJA V d) (w r : V) : V :=
  J.P (J.spec (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) w) r

/-- The root-determinant `φ(w) = det(w)^{1/d}` (96). Meaningful on `Q`, where `det w ≥ 0`. -/
noncomputable def rtdet (J : EJA V d) (w : V) : ℝ := (J.det w) ^ (1 / (d : ℝ))

/-- `ζ(u, w) = φ(w) − u` (97). -/
noncomputable def zeta (J : EJA V d) (x : ℝ × V) : ℝ := rtdet J x.2 - x.1

/-- `E = ℝ × Q` (p. 23). -/
def E (J : EJA V d) : Set (ℝ × V) := Set.univ ×ˢ J.Q

/-- The root-determinant cone `K_rtdet = {(u, w) ∈ ℝ × Q : u ≤ det(w)^{1/d}}` (98a). -/
def Krtdet (J : EJA V d) : Set (ℝ × V) := {x | x.2 ∈ J.Q ∧ x.1 ≤ rtdet J x.2}

/-- The barrier `Γ(u, w) = −log(ζ(u, w)) − logdet(w)` (102); only used on `int K_rtdet`. -/
noncomputable def Gamma (J : EJA V d) (x : ℝ × V) : ℝ :=
  -Real.log (zeta J x) - Real.log (J.det x.2)

/-- `Ψ(u, w) = −logdet(w)` (proof of Proposition 7.1, p. 24); only used on `int E`. -/
noncomputable def Psi (J : EJA V d) (x : ℝ × V) : ℝ := -Real.log (J.det x.2)

end EJASpectral.RootDet


