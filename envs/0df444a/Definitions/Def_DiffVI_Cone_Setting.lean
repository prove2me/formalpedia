-- Prove2me | Definitions.Def_DiffVI_Cone_Setting
-- name    : DiffVI_Cone_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:32.95013+00:00
-- url     : https://prove2.me/theorems/9744b5b9-2b0b-4019-9d22-6c50a69cb231
-- title:
--   §6.1, §7, §8, pp. 29, 42, 53–57 — (A), (B), the scheme (7.2), the step (8.4), (C), (D), (C′), (E), the Z/W coordinates and (8.7)
-- statement:
--   This file fixes the objects of §8 of Pang and Stewart's *Differential variational inequalities*. Throughout, $\mathbb R^k$ is the Euclidean space of dimension $k$, $u^\top v$ is the inner product and matrices are linear maps; $A^\top$ is the adjoint. $T>0$ is a horizon and $\Omega=[0,T]\times\mathbb R^n$ carries the metric $|t-t'|+\|x-x'\|$.
--
--   The data are $f:\Omega\to\mathbb R^n$, $B:\Omega\to\mathbb R^{n\times m}$, $G:\Omega\to\mathbb R^m$ and $F:\mathbb R^m\to\mathbb R^m$, and $K\subseteq\mathbb R^m$. For $\Phi:\mathbb R^m\to\mathbb R^m$, $\mathrm{SOL}(K,\Phi)$ is the set of $u\in K$ with $(u'-u)^\top\Phi(u)\ge 0$ for all $u'\in K$.
--
--   1. **(A)** $f$, $B$ and $G$ are Lipschitz continuous on $\Omega$ (with positive constants $L_f$, $L_B$, $L_G$; $B$ in operator norm). **(B)** $\sigma_B=\sup_\Omega\|B(t,x)\|<\infty$.
--   2. **Monotonicity.** $H$ is monotone on $S$ if $(u-u')^\top(H(u)-H(u'))\ge 0$ for $u,u'\in S$, and strongly monotone on $S$ with modulus $\eta>0$ if $(u-u')^\top(H(u)-H(u'))\ge\eta\|u-u'\|^2$.
--   3. The **dual cone** is $C^*=\{v: u^\top v\ge 0\ \forall u\in C\}$; $K$ is a **closed convex cone** if it is nonempty, closed, convex and $\tau u\in K$ for $u\in K$, $\tau\ge 0$.
--   4. **The scheme (7.2).** For an integer $N\ge 1$ let $h=T/N$ and $t_{h,i}=ih$. A run from $x^0$ is a pair of sequences with $x^{h,0}=x^0$ and, for $i=0,\dots,N-1$,
--   $$x^{h,i+1}=x^{h,i}+h\big[f(t_{h,i+1},\theta x^{h,i}+(1-\theta)x^{h,i+1})+B(t_{h,i},x^{h,i})u^{h,i+1}\big],\qquad u^{h,i+1}\in\mathrm{SOL}(K,G(t_{h,i+1},x^{h,i+1})+F).$$
--   The term $u^{h,0}$ is not constrained by the scheme.
--   5. **One step (8.4)** from $(t_{\rm ref},x^{\rm ref})$ to time $t$ with step $h$: $x^h=x^{\rm ref}+h[f(t,\theta x^{\rm ref}+(1-\theta)x^h)+B(t_{\rm ref},x^{\rm ref})u^h]$ and $u^h\in\mathrm{SOL}(K,G(t,x^h)+F)$.
--   6. **(C)** $F$ is continuous and for some $u^{\rm ref}\in K$, $\liminf_{u\in K,\|u\|\to\infty}(u-u^{\rm ref})^\top F(u)/\|u\|^2\ge 0$.
--   7. **(D)** there is $\eta_G>0$ with $(u-u')^\top\big(G(t,r+B(t_{\rm ref},x^{\rm ref})u)-G(t,r+B(t_{\rm ref},x^{\rm ref})u')\big)\ge\eta_G\|u-u'\|^2$ for all $r\in\mathbb R^n$, $u,u'\in\mathbb R^m$, $t,t_{\rm ref}\in[0,T]$, $x^{\rm ref}\in\mathbb R^n$.
--   8. **(C′)** $F=E^\top\circ\Psi\circ E$ with $E\in\mathbb R^{\ell\times m}$ and $\Psi:\mathbb R^\ell\to\mathbb R^\ell$ Lipschitz continuous and strongly monotone on $E\mathbb R^m$.
--   9. **(E)** with $\mathcal E=\ker E$ and $K_1$, $K_2$ the orthogonal projections of $K$ onto $\mathcal E$ and $\mathcal E^\perp$: $K_1\oplus K_2\subseteq K$.
--   10. **Coordinates.** $Z\in\mathbb R^{m\times k}$ and $W\in\mathbb R^{m\times p}$ have orthonormal columns spanning $\mathcal E$ and $\mathcal E^\perp$, so $P=[Z\ W]$ is orthogonal. With $\widetilde W=EW$, $\Upsilon=\widetilde W^\top\circ\Psi\circ\widetilde W$, and **(8.7)** says that for some $\eta_\Upsilon>0$,
--   $$(\Upsilon(\lambda)-\Upsilon(\lambda'))^\top(\lambda-\lambda')\ge\eta_\Upsilon\|\lambda-\lambda'\|^2\qquad\forall\lambda,\lambda'.$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\mathbb R^k$ is `EuclideanSpace ℝ (Fin k)`, matrices are continuous linear maps and $E^\top$ is `ContinuousLinearMap.adjoint`. The data are functions on all of $\mathbb R\times\mathbb R^n$; only their values on $[0,T]$ enter (A), (B), (D). The step $h$ with $(N_h+1)h=T$ is $T/N$. (C)'s liminf is written in $\varepsilon$–$R$ form. (E) uses Mathlib's orthogonal projections onto $\ker E$ and $(\ker E)^\perp$; the coordinate form (8.6) is Lemma 8.1, not a definition. The dual cone is written out as a set. These bodies duplicate the shared conventions declared in the companion missions of this paper.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, pp. 4, 29, 42, 53, 56–57, (A), (B), (7.2), (8.4), (C), (D), (C′), (E), (8.7)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Conv_Setting
import Definitions.Def_DiffVI_Exist_Setting

namespace DiffVI.Cone

open scoped InnerProductSpace InnerProduct

/-- `K` is a closed convex cone (nonempty, closed, convex, closed under nonnegative scaling). -/
def IsClosedConvexCone {k : ℕ} (K : Set (EuclideanSpace ℝ (Fin k))) : Prop :=
  K.Nonempty ∧ IsClosed K ∧ Convex ℝ K ∧ ∀ u ∈ K, ∀ τ : ℝ, 0 ≤ τ → τ • u ∈ K

/-- One step (8.4) of the scheme from `(t_ref, x^ref)` to time `t` with step `h`. -/
def IsStep {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (B : ℝ → EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (G : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (θ h t tref : ℝ) (xref xh : EuclideanSpace ℝ (Fin n)) (uh : EuclideanSpace ℝ (Fin m)) : Prop :=
  xh = xref + h • (f t (θ • xref + (1 - θ) • xh) + B tref xref uh) ∧
  uh ∈ SolodovSvaiterVI.Alg21.viSol (fun v => G t xh + F v) K

/-- Condition (C), p. 53: `F` is continuous and for some `u^ref ∈ K`,
`liminf_{u ∈ K, ‖u‖ → ∞} (u - u^ref)ᵀ F(u) / ‖u‖² ≥ 0`. -/
def CondC {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) : Prop :=
  Continuous F ∧ ∃ uref ∈ K, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ u ∈ K, R ≤ ‖u‖ →
    -ε * ‖u‖ ^ 2 ≤ ⟪u - uref, F u⟫_ℝ

/-- Condition (D), p. 53, with constant `η_G > 0`. -/
def CondD {n m : ℕ} (T : ℝ)
    (B : ℝ → EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (G : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (ηG : ℝ) : Prop :=
  0 < ηG ∧ ∀ r : EuclideanSpace ℝ (Fin n), ∀ u u' : EuclideanSpace ℝ (Fin m),
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ tref ∈ Set.Icc (0 : ℝ) T, ∀ xref : EuclideanSpace ℝ (Fin n),
      ηG * ‖u - u'‖ ^ 2 ≤ ⟪u - u', G t (r + B tref xref u) - G t (r + B tref xref u')⟫_ℝ

/-- Condition (C′), p. 56: `F = Eᵀ ∘ Ψ ∘ E` with `Ψ` Lipschitz continuous and strongly monotone
on the range `E ℝ^m`. -/
def CondC' {m ℓ : ℕ} (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (E : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin ℓ))
    (Ψ : EuclideanSpace ℝ (Fin ℓ) → EuclideanSpace ℝ (Fin ℓ)) : Prop :=
  (∀ u, F u = (E†) (Ψ (E u))) ∧ (∃ L : NNReal, LipschitzWith L Ψ) ∧
    ∃ η : ℝ, DiffVI.Exist.IsStronglyMonotoneOn Ψ (Set.range E) η

/-- Condition (E), p. 56: `K₁ ⊕ K₂ ⊆ K`, where `K₁`, `K₂` are the orthogonal projections of `K`
onto the null space `ker E` and its orthogonal complement. -/
def CondE {m ℓ : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (E : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin ℓ)) : Prop :=
  ∀ u1 ∈ K, ∀ u2 ∈ K,
    (LinearMap.ker (E : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin ℓ))).starProjection u1 +
      (LinearMap.ker (E : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin ℓ)))ᗮ.starProjection u2
      ∈ K

/-- `Z` and `W` have orthonormal columns spanning `ker E` and `(ker E)ᗮ` respectively (p. 56),
so that `P = [Z W]` is an orthogonal matrix. -/
def IsZWBasis {m ℓ k p : ℕ} (E : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin ℓ))
    (Z : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (W : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin m)) : Prop :=
  (∀ μ, ‖Z μ‖ = ‖μ‖) ∧ (∀ lam, ‖W lam‖ = ‖lam‖) ∧
    LinearMap.range (Z : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) =
      LinearMap.ker (E : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin ℓ)) ∧
    LinearMap.range (W : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) =
      (LinearMap.ker (E : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin ℓ)))ᗮ

/-- The map `Υ = W̃ᵀ ∘ Ψ ∘ W̃` with `W̃ = E W` (p. 57). -/
noncomputable def Ups {m ℓ p : ℕ} (E : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin ℓ))
    (W : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (Ψ : EuclideanSpace ℝ (Fin ℓ) → EuclideanSpace ℝ (Fin ℓ)) (lam : EuclideanSpace ℝ (Fin p)) :
    EuclideanSpace ℝ (Fin p) :=
  ((E ∘L W)†) (Ψ ((E ∘L W) lam))

/-- (8.7), p. 57: `Υ` is strongly monotone on `ℝ^{m-k}` with constant `η_Υ > 0`. -/
def CondUps {m ℓ p : ℕ} (E : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin ℓ))
    (W : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (Ψ : EuclideanSpace ℝ (Fin ℓ) → EuclideanSpace ℝ (Fin ℓ)) (ηΥ : ℝ) : Prop :=
  0 < ηΥ ∧ ∀ lam1 lam2 : EuclideanSpace ℝ (Fin p),
    ηΥ * ‖lam1 - lam2‖ ^ 2 ≤ ⟪Ups E W Ψ lam1 - Ups E W Ψ lam2, lam1 - lam2⟫_ℝ

end DiffVI.Cone


