-- Prove2me | Definitions.Def_LiftSAParity_mu
-- name    : LiftSAParity_mu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:09:59.1339+00:00
-- url     : https://prove2.me/theorems/022dc042-a3ec-4ed6-85f8-eb203b2d6e22
-- title:
--   The measure $\mu$ on affine spaces
-- statement:
--   Let $\mathcal D$ be a $d$-local distribution for $F$ and $\gamma$ a family of stifling inputs. For $I\subseteq[n]$ with $|I|\le d$ and $J\in[\ell]^n$, the law $\tilde D^J_I$ of $y\in\{0,1\}^{n\times\ell}$ samples $x_I\sim D_I$, sets $y_{i,k}$ to the $k$-th bit of $\gamma_{J_i,x_i}$ for $i\in I$ and $k\neq J_i$, and samples all remaining variables (the stifled variables of the blocks in $I$ and all variables outside those blocks) uniformly and independently. For a nonempty affine space $A$,
--   $$\mu_J(A)=\Pr_{y\sim\tilde D^J_{I(J,A)}}[y\in A],\qquad \mu(A)=\mathop{\mathbb E}_{J\sim[\ell]^n}\big[\mu_J(A)\big], \tag{24–25}$$
--   and $\mu(\emptyset)=\mu_J(\emptyset)=0$. Here $J$ is uniform on $[\ell]^n$, and $\Pr_J$, $\mathbb E_J$ denote the uniform probability and expectation over $J$.
--
--   This is the pseudo-measure of the lifting theorem: the paper shows it satisfies the four conditions of Lemma 3.4 with $r=\lfloor d/2\ell\rfloor$ and $\delta=e^{-d/8\ell^3}$.
--
--   **Formalization Note** $\Pr_{y\sim\tilde D^J_I}[y\in A]=\sum_\sigma D_I(\sigma)\,|\{y\in A: y\text{ compatible with }\sigma\}|/|\{y: y\text{ compatible with }\sigma\}|$, where compatible means $y_{i,k}=\gamma_{J_i,\sigma_i}(k)$ for $i\in I$, $k\neq J_i$; everything is a finite sum, with no measure theory.
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §4.1, p.14, eqs. (24)–(25)

import Mathlib
import Definitions.Def_LiftSAParity_IsAffineSpace
import Definitions.Def_LiftSAParity_blocks

namespace LiftSAParity

open Classical

/-- `y` agrees with the stifling inputs on the selected blocks: for every `i ∈ I` and `k ≠ J_i`,
`y_{i,k}` is the `k`th bit of `γ_{J_i, σ_i}`. -/
def Compat {n ℓ : ℕ} (γ : Fin ℓ → Bool → (Fin ℓ → Bool)) (J : Fin n → Fin ℓ) (I : Finset (Fin n))
    (σ : I → Bool) (y : Fin n × Fin ℓ → ZMod 2) : Prop :=
  ∀ (i : Fin n) (hi : i ∈ I) (k : Fin ℓ), k ≠ J i → y (i, k) = ofBool (γ (J i) (σ ⟨i, hi⟩) k)

/-- **`Pr_{y∼D̃^J_I}[y ∈ A]`** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to
Unary Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…), §4.1, p.14): "define D̃^J_I
by sampling x_I ∼ D_I and setting y_{i,k} to the kth bit of γ_{J_i,x_i} for i ∈ I and k ≠ J_i, and
sampling all remaining variables, including the stifled variables in blocks belonging to I and all
variables outside those blocks, uniformly and independently at random."

The probability is `∑_σ D_I(σ) · |{y ∈ A : y compatible with σ}| / |{y : y compatible with σ}|`:
given `x_I = σ` the free coordinates are uniform, so `y` is uniform on the compatible points.

**Formalization Note** `D I σ` is the probability of `σ : I → Bool` under `D_I`; `γ j b` is the
stifling input `γ_{j,b}`, whose value at `j` is never read. -/
noncomputable def tildeProb {n ℓ : ℕ} (D : (I : Finset (Fin n)) → (I → Bool) → ℝ)
    (γ : Fin ℓ → Bool → (Fin ℓ → Bool)) (J : Fin n → Fin ℓ) (I : Finset (Fin n))
    (A : Set (Fin n × Fin ℓ → ZMod 2)) : ℝ :=
  ∑ σ : I → Bool, D I σ *
    (((Finset.univ.filter (fun y => y ∈ A ∧ Compat γ J I σ y)).card : ℝ) /
      ((Finset.univ.filter (fun y => Compat γ J I σ y)).card : ℝ))

/-- **`µ_J(A)`** (§4.1, p.14, eq. (24)): "For a fixed J and for a non-empty affine subspace A, we
let µ_J(A) = Pr_{y∼D̃^J_{I(J,A)}}[y ∈ A] … For the empty space, we let µ(∅) = µ_J(∅) = 0." -/
noncomputable def muJ {n ℓ : ℕ} (d : ℕ) (D : (I : Finset (Fin n)) → (I → Bool) → ℝ)
    (γ : Fin ℓ → Bool → (Fin ℓ → Bool)) (J : Fin n → Fin ℓ) (A : Set (Fin n × Fin ℓ → ZMod 2)) :
    ℝ :=
  if A.Nonempty then tildeProb D γ J (blocks d J A) A else 0

/-- The expectation `E_{J∼[ℓ]^n}[X(J)]` over a uniform `J ∈ [ℓ]^n`. -/
noncomputable def expJ {n ℓ : ℕ} (X : (Fin n → Fin ℓ) → ℝ) : ℝ :=
  (∑ J, X J) / (ℓ : ℝ) ^ n

/-- The probability `Pr_{J∼[ℓ]^n}[P(J)]` over a uniform `J ∈ [ℓ]^n`. -/
noncomputable def probJ {n ℓ : ℕ} (P : (Fin n → Fin ℓ) → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (ℓ : ℝ) ^ n

/-- **The measure `µ`** (§4.1, p.14, eq. (25)): "µ(A) = E_{J∼[ℓ]^n}[µ_J(A)]", with `µ(∅) = 0`.

**Formalization Note** `µ` is defined on every subset of `𝔽₂^{n×ℓ}`; the theorems of the mission
evaluate it on affine spaces only. The cutoff `d`, the family `D` and the stifling inputs `γ` are
parameters. -/
noncomputable def mu {n ℓ : ℕ} (d : ℕ) (D : (I : Finset (Fin n)) → (I → Bool) → ℝ)
    (γ : Fin ℓ → Bool → (Fin ℓ → Bool)) (A : Set (Fin n × Fin ℓ → ZMod 2)) : ℝ :=
  expJ (fun J => muJ d D γ J A)

end LiftSAParity


