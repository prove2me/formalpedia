-- Prove2me | Definitions.Def_BorderD4_SigmaPiPsi
-- name    : BorderD4_SigmaPiPsi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:00:18.790332+00:00
-- url     : https://prove2.me/theorems/f2dc1ec1-28af-4b23-9083-80875c4d88d7
-- title:
--   The classes $\mathcal U$, $\Sigma\Pi\Psi(m,\ell)$ and $\Pi\Psi(P)$
-- statement:
--   $\mathcal U=\{p\in F[[\varepsilon]][x]\mid\deg p\le\Delta,\ p(u,\varphi)\text{ an }\varepsilon\text{-unit}\}$. $\Pi\Psi(P)$ is the set of products of series $\Psi(p)$ with $p\in P$, repetitions allowed, the empty product being $1$. $\Sigma\Pi\Psi(m,\ell)$ is the set of sums of at most $m$ terms
--   $$c\cdot\Psi(q_1)^{\pm1}\cdots\Psi(q_{\ell'})^{\pm1},\qquad \ell'\le\ell,$$
--   where $c\in F((\varepsilon))[z,z^{-1}]$ and each $q_t\in F[[\varepsilon]][x]$ has degree at most $\Delta$ and lies in $\mathcal U$ if its exponent is $-1$.
--
--   **Formalization Note** An element of $F((\varepsilon))[z,z^{-1}]$ is a finitely supported coefficient function $\mathbb Z\to F((\varepsilon))$.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §6.3.1, p.64; Definition 6.15, p.66

import Mathlib
import Definitions.Def_BorderD4_evalAt
import Definitions.Def_BorderD4_Psi
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

section

variable {F σ : Type*} [Field F] [DecidableEq σ]

/-- The set `U = { p ∈ F[[ε]][x] | deg p ≤ Δ and p(u, φ) is an ε-unit }`. Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), §6.3.1, p.64. -/
def U (T : Finset σ) (φ : {a // a ∉ T} → EpsSeries F T) (Δ : ℕ) : Set (MvPolynomial σ F⟦X⟧) :=
  {p | p.totalDegree ≤ Δ ∧ IsEpsUnit (evalAt T (freeDep T φ) p)}

/-- The embedding `F((ε)) → Frac F[[ε]][u][[z]]`. -/
noncomputable def kEmb (F τ : Type*) [Field F] : LaurentSeries F →+* ZFrac F τ :=
  IsFractionRing.lift (A := F⟦X⟧) (K := LaurentSeries F)
    (g := (algebraMap (ZRing F τ) (ZFrac F τ)).comp ((PowerSeries.C).comp MvPolynomial.C))
    ((IsFractionRing.injective (ZRing F τ) (ZFrac F τ)).comp
      (PowerSeries.C_injective.comp (MvPolynomial.C_injective _ _)))

/-- The variable `z` in the fraction field. -/
noncomputable def zF (F τ : Type*) [Field F] : ZFrac F τ :=
  algebraMap (ZRing F τ) (ZFrac F τ) PowerSeries.X

/-- The element `∑_d c_d z^d` of `F((ε))[z, z⁻¹]`, for a finitely supported coefficient function `c`. -/
noncomputable def laurentCoef {τ : Type*} (c : ℤ →₀ LaurentSeries F) : ZFrac F τ :=
  c.sum fun d a => kEmb F τ a * zF F τ ^ d

/-- A term `c · Ψ(q_1)^{±1} ⋯ Ψ(q_ℓ′)^{±1}`, where the Boolean `true` records the exponent `+1`. -/
noncomputable def psiTerm (T : Finset σ) (φ : {a // a ∉ T} → EpsSeries F T)
    (c : ℤ →₀ LaurentSeries F) (fs : List (MvPolynomial σ F⟦X⟧ × Bool)) : ZFrac F T :=
  laurentCoef c * (fs.map fun q => if q.2 then PsiF T φ q.1 else (PsiF T φ q.1)⁻¹).prod

/-- `ΣΠΨ(m, ℓ)`: sums of at most `m` terms `c · Ψ(q_1)^{±1} ⋯ Ψ(q_ℓ′)^{±1}` with `ℓ′ ≤ ℓ`, where
`c ∈ F((ε))[z, z⁻¹]` and each `q_t ∈ F[[ε]][x]` has degree at most `Δ` and lies in `U` if its exponent is `−1`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 6.15, p.66. -/
def SigmaPiPsi (T : Finset σ) (φ : {a // a ∉ T} → EpsSeries F T) (Δ m ℓ : ℕ) : Set (ZFrac F T) :=
  {A | ∃ (n : ℕ) (_ : n ≤ m) (c : Fin n → ℤ →₀ LaurentSeries F)
      (fs : Fin n → List (MvPolynomial σ F⟦X⟧ × Bool)),
    (∀ i, (fs i).length ≤ ℓ) ∧
    (∀ i, ∀ q ∈ fs i, q.1.totalDegree ≤ Δ ∧ (q.2 = false → q.1 ∈ U T φ Δ)) ∧
    A = ∑ i, psiTerm T φ (c i) (fs i)}

/-- `ΠΨ(P)`: products of series `Ψ(p)` with `p ∈ P`, repetitions allowed, the empty product being `1`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 6.15, p.66. -/
def PiPsi (T : Finset σ) (φ : {a // a ∉ T} → EpsSeries F T) (P : Set (MvPolynomial σ F⟦X⟧)) :
    Set (ZFrac F T) :=
  {A | ∃ l : List (MvPolynomial σ F⟦X⟧), (∀ p ∈ l, p ∈ P) ∧ A = (l.map (PsiF T φ)).prod}

end

end BorderD4


