-- Prove2me | Definitions.Def_LanglandsFunctoriality_automorphic_data
-- name    : LanglandsFunctoriality_automorphic_data
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T15:39:12.190519+00:00
-- url     : https://prove2.me/theorems/694ac395-c84b-4f44-ab5d-e671fb040447
-- title:
--   Unramified automorphic data for $GL(n)$ and the converse-theorem criterion
-- statement:
--   This file fixes the objects in which the Langlands functoriality conjecture is stated in this
--   mission: the unramified data attached to an automorphic representation of $GL(n,\mathbb A)$, and
--   the analytic criterion for such a datum to be automorphic.
--
--   A **datum of rank $n$** consists of a family of Satake parameters $\alpha_{p,1},\dots,\alpha_{p,n}
--   \in \mathbb C^{\times}$, one $n$-tuple for every prime $p$ — the diagonal of the semisimple
--   conjugacy class $c(\pi_p)\subset GL(n,\mathbb C)$ attached to the unramified local component
--   $\pi_p$ — together with archimedean shifts $\mu_1,\dots,\mu_n\in\mathbb C$.
--
--   From a datum one forms the local coefficients $h_k(\alpha_{p,1},\dots,\alpha_{p,n})$, the complete
--   homogeneous symmetric functions, which are the coefficients of the local Euler factor
--   $\prod_i (1-\alpha_{p,i}X)^{-1}$; the Dirichlet coefficients $a_\pi(m)=\prod_{p\mid m}
--   h_{v_p(m)}(\alpha_{p,\bullet})$; and the completed $L$-function
--
--   $$\Lambda(s,\pi)\;=\;Q^{s/2}\prod_{i=1}^{n}\pi^{-(s+\mu_i)/2}\,\Gamma\!\left(\frac{s+\mu_i}{2}
--   \right)\sum_{m\ge1}\frac{a_\pi(m)}{m^{s}},$$
--
--   with a conductor $Q>0$. The **contragredient** $\tilde\pi$ inverts the Satake parameters and
--   conjugates the shifts. The **Rankin–Selberg datum** $\pi\times\tau$ of rank $nm$ has parameters
--   $\alpha_{p,i}\beta_{p,j}$ and shifts $\mu_i+\nu_j$.
--
--   A datum is **nice** if, for some $Q>0$ and some $\varepsilon\in\mathbb C$, the Dirichlet series of
--   $\pi$ and of $\tilde\pi$ converge in a right half plane, both completed $L$-functions extend to
--   entire functions bounded on every vertical strip of finite width, and $\Lambda(s,\pi)=\varepsilon
--   \Lambda(1-s,\tilde\pi)$.
--
--   A datum of rank $n$ is **cuspidal automorphic** if it is nice and every Rankin–Selberg twist
--   $\pi\times\tau$ by a cuspidal automorphic datum $\tau$ of rank $m$ with $1\le m\le n-2$ is nice —
--   the recursion terminates because $m<n$. For $n\le 2$ no twist is required, which is the classical
--   setting of Hecke's converse theorem; for larger $n$ these are the twists appearing in the converse
--   theorems of Cogdell and Piatetski-Shapiro. Finally, a datum is **automorphic** in the weaker,
--   possibly non-cuspidal sense if its completed $L$-functions become entire after multiplication by
--   nonzero polynomials — clearing finitely many poles — and satisfy the functional equation in that
--   cleared form.
--
--   **Formalization Note.** Automorphy is modelled by analytic conditions, not representation
--   theoretically: no adelic group, space of automorphic forms or spectral decomposition occurs. The
--   criterion is the one the converse theorems use, which is why the mission's milestones include
--   those theorems.
-- source:
--   J.-H. Yang, Langlands Functoriality Conjecture, arXiv:0808.0917 (2008), https://arxiv.org/abs/0808.0917

import Mathlib

/-!
# Analytic data attached to an everywhere-unramified automorphic representation of `GL(n)`

This file sets up the objects in which the Langlands functoriality conjecture is stated in the
mission "Langlands Functoriality Conjecture".

An everywhere-unramified automorphic representation `π = ⊗ᵥ πᵥ` of `GL(n, 𝔸)` is recorded
through the data that functoriality actually compares: the Satake parameters
`c(πₚ) = diag(α_{p,1}, …, α_{p,n}) ⊂ GL(n, ℂ)` at the finite places, together with the shifts
entering the archimedean factor of the completed `L`-function.

Automorphy is recorded through the analytic criterion supplied by the converse theorems:
`π` is *cuspidal automorphic* when the completed `L`-function of `π` — and of every
Rankin–Selberg twist of `π` by a cuspidal automorphic datum of rank `m` with `1 ≤ m ≤ n - 2` —
is entire, bounded on vertical strips, and satisfies the standard functional equation.
-/

namespace LanglandsFunctoriality

open Complex

/-- `LData n` is the unramified datum of a representation of `GL(n, 𝔸)`: the Satake parameters
at each finite place and the shifts of the archimedean factor. -/
structure LData (n : ℕ) where
  /-- Satake parameters: `satake p` is the diagonal of `c(π_p) ⊂ GL(n, ℂ)`. -/
  satake : ℕ → Fin n → ℂ
  /-- Satake parameters at a prime are invertible. -/
  satake_ne_zero : ∀ p : ℕ, p.Prime → ∀ i : Fin n, satake p i ≠ 0
  /-- The shifts appearing in the archimedean factor `∏ᵢ π^{-(s+μᵢ)/2} Γ((s+μᵢ)/2)`. -/
  shift : Fin n → ℂ

/-- The coefficient of `X ^ k` in the local Euler factor `∏ᵢ (1 - αᵢ X)⁻¹`, i.e. the complete
homogeneous symmetric function `h_k(α₁, …, α_n)`. -/
noncomputable def localCoeff {n : ℕ} (α : Fin n → ℂ) (k : ℕ) : ℂ :=
  PowerSeries.coeff k (∏ i : Fin n, PowerSeries.mk fun j => α i ^ j)

/-- The Dirichlet coefficients of `L(s, π) = ∏ₚ ∏ᵢ (1 - α_{p,i} p^{-s})⁻¹`. -/
noncomputable def dirichletCoeff {n : ℕ} (π : LData n) (m : ℕ) : ℂ :=
  ∏ p ∈ m.primeFactors, localCoeff (π.satake p) (m.factorization p)

/-- The archimedean factor `∏ᵢ π^{-(s+μᵢ)/2} Γ((s+μᵢ)/2)`. -/
noncomputable def gammaFactor {n : ℕ} (π : LData n) (s : ℂ) : ℂ :=
  ∏ i : Fin n, ((Real.pi : ℂ) ^ (-(s + π.shift i) / 2) * Complex.Gamma ((s + π.shift i) / 2))

/-- The completed `L`-function `Λ(s, π) = Q^{s/2} · γ(s, π) · L(s, π)` with conductor `Q`,
defined where the Dirichlet series converges. -/
noncomputable def completedL {n : ℕ} (π : LData n) (Q : ℝ) (s : ℂ) : ℂ :=
  (Q : ℂ) ^ (s / 2) * gammaFactor π s * LSeries (dirichletCoeff π) s

/-- The contragredient datum `π̃`: the Satake parameters are inverted and the archimedean
shifts are conjugated. -/
noncomputable def dual {n : ℕ} (π : LData n) : LData n where
  satake p i := (π.satake p i)⁻¹
  satake_ne_zero p hp i := inv_ne_zero (π.satake_ne_zero p hp i)
  shift i := starRingEnd ℂ (π.shift i)

/-- The Rankin–Selberg datum `π × τ` of rank `n · m`: Satake parameters `α_i β_j` and
archimedean shifts `μ_i + ν_j`. -/
noncomputable def pairData {n m : ℕ} (π : LData n) (τ : LData m) : LData (n * m) where
  satake p k :=
    π.satake p (finProdFinEquiv.symm k).1 * τ.satake p (finProdFinEquiv.symm k).2
  satake_ne_zero p hp _k :=
    mul_ne_zero (π.satake_ne_zero p hp _) (τ.satake_ne_zero p hp _)
  shift k := π.shift (finProdFinEquiv.symm k).1 + τ.shift (finProdFinEquiv.symm k).2

/-- `F` is bounded on every vertical strip of finite width. -/
def BoundedOnVerticalStrips (F : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖F s‖ ≤ C

/-- The "nice" analytic conditions of the converse theorems: for some conductor `Q > 0` and
root number `ε`, the Dirichlet series of `π` and of `π̃` converge in a right half plane, their
completed `L`-functions continue to entire functions bounded on vertical strips, and they
satisfy `Λ(s, π) = ε · Λ(1 - s, π̃)`. -/
def IsNice {n : ℕ} (π : LData n) : Prop :=
  ∃ (σ₀ Q : ℝ) (ε : ℂ) (Λ Λd : ℂ → ℂ),
    0 < Q ∧
    (∀ s : ℂ, σ₀ < s.re → LSeriesSummable (dirichletCoeff π) s) ∧
    (∀ s : ℂ, σ₀ < s.re → LSeriesSummable (dirichletCoeff (dual π)) s) ∧
    Differentiable ℂ Λ ∧ Differentiable ℂ Λd ∧
    BoundedOnVerticalStrips Λ ∧ BoundedOnVerticalStrips Λd ∧
    (∀ s : ℂ, σ₀ < s.re → Λ s = completedL π Q s) ∧
    (∀ s : ℂ, σ₀ < s.re → Λd s = completedL (dual π) Q s) ∧
    (∀ s : ℂ, Λ s = ε * Λd (1 - s))

/-- The converse-theorem criterion for `π` to be a *cuspidal automorphic* datum of `GL(n)`:
`π` is nice, and so is every Rankin–Selberg twist `π × τ` by a cuspidal automorphic datum `τ`
of rank `m` with `1 ≤ m ≤ n - 2`.  For `n ≤ 2` no twists are required, which is the classical
converse theorem of Hecke; for larger `n` this is the family of twists used in the converse
theorems of Cogdell and Piatetski-Shapiro. -/
def IsCuspidalAutomorphic : ∀ (n : ℕ), LData n → Prop
  | n, π =>
      IsNice π ∧
        ∀ m : ℕ, 1 ≤ m → m + 2 ≤ n → ∀ τ : LData m,
          IsCuspidalAutomorphic m τ → IsNice (pairData π τ)
  termination_by n => n
  decreasing_by omega

/-- The analytic behaviour of the `L`-function of a general (not necessarily cuspidal)
automorphic representation: for some conductor `Q > 0` and root number `ε`, and after
multiplication by nonzero polynomials clearing the finitely many poles, the completed
`L`-functions of `π` and `π̃` continue to entire functions satisfying the functional equation
`Λ(s, π) = ε · Λ(1 - s, π̃)` in cleared form. -/
def IsAutomorphicL {n : ℕ} (π : LData n) : Prop :=
  ∃ (σ₀ Q : ℝ) (ε : ℂ) (q qd : Polynomial ℂ) (Λ Λd : ℂ → ℂ),
    0 < Q ∧ q ≠ 0 ∧ qd ≠ 0 ∧
    (∀ s : ℂ, σ₀ < s.re → LSeriesSummable (dirichletCoeff π) s) ∧
    (∀ s : ℂ, σ₀ < s.re → LSeriesSummable (dirichletCoeff (dual π)) s) ∧
    Differentiable ℂ Λ ∧ Differentiable ℂ Λd ∧
    (∀ s : ℂ, σ₀ < s.re → Λ s = q.eval s * completedL π Q s) ∧
    (∀ s : ℂ, σ₀ < s.re → Λd s = qd.eval s * completedL (dual π) Q s) ∧
    (∀ s : ℂ, Λ s * qd.eval (1 - s) = ε * Λd (1 - s) * q.eval s)

end LanglandsFunctoriality


