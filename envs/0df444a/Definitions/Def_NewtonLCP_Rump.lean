-- Prove2me | Definitions.Def_NewtonLCP_Rump
-- name    : NewtonLCP_Rump
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:00.218207+00:00
-- url     : https://prove2.me/theorems/fbf21f7a-cb1d-4306-9a95-821cd4f24692
-- title:
--   Real spectral radius $\rho$, sign-real spectral radius $\rho^S_0$ and maximum geometric cycle mean $\zeta$
-- statement:
--   Let $A,M\in\mathbb R^{n\times n}$.
--
--   1. The **real spectral radius** $\rho(A)$ is the maximum of $|\lambda|$ over the real eigenvalues $\lambda$ of $A$, and $\rho(A)=0$ if $A$ has no real eigenvalue.
--   2. The **sign-real spectral radius** is $\rho^S_0(M)=\max_{S\in\mathcal S_n}\rho(SM)$, where $\mathcal S_n$ is the set of the $2^n$ signature matrices $\mathrm{diag}(\pm1)$.
--   3. A cycle is $C=(i_1,\dots,i_\ell,i_1)$ with $i_1,\dots,i_\ell$ distinct and $\ell\ge1$ (loops allowed). The **maximum absolute geometric cycle mean** is
--   $$\zeta(M)=\max_{C}\Big(\prod_{(i,j)\in C}|M_{ij}|\Big)^{1/|C|}.$$
--
--   Rump's theorem (Theorem 2.10) relates $\zeta$ and $\rho^S_0$; the mission uses it for $H=(I_n+A)^{-1}$ with $A\in\mathcal P_\star$.
--
--   **Formalization Note** The maxima are over finite sets and are written as suprema; the empty set (no real eigenvalue, or $n=0$) gives $0$, which is the paper's convention for $\rho$.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Definitions 2.7 and 2.9, p.7

import Mathlib

open Matrix

namespace NewtonLCP

/-!
# Real spectral radius, sign-real spectral radius and maximum geometric cycle mean

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab…40f8), Definitions 2.7 and 2.9, p.7.

* `ρ(A)` is the maximum absolute value of a real eigenvalue of `A`, and `0` if `A` has none.
* `ρ^S_0(M) = max_{S ∈ 𝒮ₙ} ρ(SM)`, `𝒮ₙ` the `2ⁿ` signature matrices `diag(±1)`.
* A cycle is `C = (i₁, …, i_ℓ, i₁)` with `i₁, …, i_ℓ` distinct and `ℓ ≥ 1` (a loop `(i, i)` is a
  cycle); `ζ(M) = max_C (∏_{(i,j) ∈ C} |Mᵢⱼ|)^{1/|C|}`.

**Formalization Note.** `realSpecRad A` is the real `sSup` of `{|λ| : Av = λv, v ≠ 0, λ ∈ ℝ}`, a
finite set; its `sSup` is the maximum, and `0` when the set is empty, which is the paper's
convention. A signature matrix is `diag(σ)` for `σ : ι → Bool` (`true ↦ 1`, `false ↦ −1`), and the
maximum over the finite type `ι → Bool` is an `iSup`. A cycle is a duplicate-free nonempty list
`[i₁, …, i_ℓ]`; its arcs are the pairs of the list with its rotation, `(i₁,i₂), …, (i_ℓ,i₁)`. The
set of such lists is finite, so `ζ` is a maximum (`0` when `ι` is empty).
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real spectral radius `ρ(A)` (Definition 2.7). -/
noncomputable def realSpecRad (A : Matrix ι ι ℝ) : ℝ :=
  sSup ((fun t : ℝ => |t|) '' {t : ℝ | ∃ v : ι → ℝ, v ≠ 0 ∧ A *ᵥ v = t • v})

/-- The sign-real spectral radius `ρ^S_0(M) = max_{S ∈ 𝒮ₙ} ρ(SM)` (Definition 2.7). -/
noncomputable def signRealSpecRad (M : Matrix ι ι ℝ) : ℝ :=
  ⨆ σ : ι → Bool, realSpecRad (diagonal (fun i => if σ i then (1 : ℝ) else -1) * M)

/-- `∏_{(i,j) ∈ C} |Mᵢⱼ|` for the cycle through the list `l` (arcs `(l_k, l_{k+1 mod ℓ})`). -/
noncomputable def cycleProd (M : Matrix ι ι ℝ) (l : List ι) : ℝ :=
  ((l.zip (l.rotate 1)).map (fun p => |M p.1 p.2|)).prod

/-- The maximum absolute geometric cycle mean `ζ(M)` (Definition 2.9). -/
noncomputable def cycleMean (M : Matrix ι ι ℝ) : ℝ :=
  sSup {r : ℝ | ∃ l : List ι, l.Nodup ∧ l ≠ [] ∧
    r = cycleProd M l ^ ((1 : ℝ) / (l.length : ℝ))}

end NewtonLCP


