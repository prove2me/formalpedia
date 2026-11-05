-- Prove2me | Definitions.Def_JencovaRenyi_Predual
-- name    : JencovaRenyi_Predual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:39:43.039922+00:00
-- url     : https://prove2.me/theorems/997b32d8-8483-4ddd-ac30-a22e69869402
-- title:
--   The predual $\mathcal M_* \simeq L_1(\mathcal M)$, its positive cone, order and support condition
-- statement:
--   Let $\mathcal M$ be a von Neumann algebra acting on a Hilbert space $H$. For $\xi,\eta\in H$ write $\omega_{\xi,\eta}(a) = \langle \xi, a\eta\rangle$, $a\in\mathcal M$. The **predual** $\mathcal M_*$ is the norm closure, in the Banach dual of $\mathcal M$, of the linear span of the functionals $\omega_{\xi,\eta}$; these are exactly the normal functionals, and the paper identifies $\mathcal M_*$ isometrically with Haagerup's $L_1(\mathcal M)$, $\psi \leftrightarrow h_\psi$, $\operatorname{Tr} h_\psi = \psi(1)$.
--
--   1. $\psi\in\mathcal M_*$ is **positive** ($\psi\in\mathcal M_*^+$) if $\psi(a^*a)$ is real and nonnegative for every $a\in\mathcal M$.
--   2. $k \le k'$ means that $k' - k$ is positive.
--   3. For $\varphi \in \mathcal M_*^+$ with support projection $e = s(\varphi)$, an element $k$ is **supported by $\varphi$**, $k = eke$, if $k(a) = 0 = k(a^*)$ whenever $\varphi(a^*a) = 0$. Since $\varphi(a^*a) = 0$ exactly when $ae = 0$, this says $k(x) = k(exe)$ for all $x$. The set of such $k$ is $L_1(\mathcal M,\varphi)$ of §3.
--
--   These are the ambient objects of the whole mission: every $L_p(\mathcal M,\varphi)$ is a subspace of $L_1(\mathcal M)$.
--
--   **Formalization Note** `A` is a `StarSubalgebra ℂ (H →L[ℂ] H)`; `Predual A` is a `Submodule` of `A →L[ℂ] ℂ` with the inherited (dual) norm. The support condition is stated without the projection $e$, which Mathlib does not provide.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, §2, p.3 (identification $\mathcal M_*\simeq L_1(\mathcal M)$, $\mathcal M_*^+$); §3, p.10 ($L_1(\mathcal M,\varphi) = \{h = ehe\}$)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06

open scoped InnerProductSpace

namespace JencovaRenyi

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The vector functional `a ↦ ⟪ξ, a η⟫` restricted to a star subalgebra `A ⊆ B(H)`, as a
bounded linear functional on `A` (Jenčová, arXiv:1609.08462v4, §2, p.3, the functional
`ω_k(a) = (ak, k)` and its polarizations).

**Formalization Note.** Mathlib's inner product `⟪ξ, ζ⟫` is conjugate linear in `ξ` and
linear in `ζ`; the paper's `(ζ, ξ)` of (4) is the same number. -/
noncomputable def vecFunctional (A : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ η : H) : A →L[ℂ] ℂ :=
  (innerSL ℂ ξ).comp ((ContinuousLinearMap.apply ℂ H η).comp
    (A.toSubalgebra.toSubmodule.subtypeL))

/-- The predual `M_*` of the von Neumann algebra `M = A ⊆ B(H)`, identified with `L_1(M)` as on
p.3 of Jenčová, arXiv:1609.08462v4 ("the identification `M_* ∋ ψ ↔ h_ψ ∈ L_1(M)`",
`Tr h_ψ = ψ(1)`): the normal functionals on `A`, i.e. the norm-closed linear span of the vector
functionals `a ↦ ⟪ξ, a η⟫` inside the Banach dual `A →L[ℂ] ℂ`.

**Formalization Note.** The normal (σ-weakly continuous) functionals on a von Neumann algebra
`M ⊆ B(H)` are exactly the norm limits of finite sums of vector functionals; the norm is the
dual norm on `A`, which is the `L_1(M)` norm `‖h_ψ‖_1 = ‖ψ‖`. -/
noncomputable def Predual (A : StarSubalgebra ℂ (H →L[ℂ] H)) : Submodule ℂ (A →L[ℂ] ℂ) :=
  (Submodule.span ℂ (Set.range fun p : H × H => vecFunctional A p.1 p.2)).topologicalClosure

/-- Positivity in the predual, `M_*^+` of p.3 (Jenčová, arXiv:1609.08462v4): `ψ(a^* a) ≥ 0` for
every `a ∈ M`, i.e. `ψ(a^* a)` is real and nonnegative. In a von Neumann algebra every
positive element is of the form `a^* a`. -/
def IsPositive {A : StarSubalgebra ℂ (H →L[ℂ] H)} (ψ : Predual A) : Prop :=
  ∀ a : A, ((ψ : A →L[ℂ] ℂ) (star a * a)).im = 0 ∧ 0 ≤ ((ψ : A →L[ℂ] ℂ) (star a * a)).re

/-- The order of `L_1(M)` (p.4, `k ≤ λ h_φ`): `k ≤ k'` iff `k' − k` is positive. -/
def PredualLE {A : StarSubalgebra ℂ (H →L[ℂ] H)} (k k' : Predual A) : Prop :=
  IsPositive (k' - k)

/-- Support condition `k = e k e`, `e = s(φ)` the support projection of `φ` (Jenčová,
arXiv:1609.08462v4, §3, p.10: `L_1(M, φ) = {h ∈ L_1(M), h = ehe}`). Stated without `e`:
`k(a) = 0 = k(a^*)` whenever `φ(a^* a) = 0`, i.e. whenever `a e = 0`.

**Formalization Note.** `φ(a^*a) = ‖a h_φ^{1/2}‖² = 0` iff `a e = 0`, so the first clause says
`k(a(1-e)) = 0` for all `a` and the second `k((1-e)a) = 0` for all `a`; together `k(x) = k(exe)`. -/
def IsSupported {A : StarSubalgebra ℂ (H →L[ℂ] H)} (φ k : Predual A) : Prop :=
  ∀ a : A, (φ : A →L[ℂ] ℂ) (star a * a) = 0 →
    (k : A →L[ℂ] ℂ) a = 0 ∧ (k : A →L[ℂ] ℂ) (star a) = 0

end JencovaRenyi


