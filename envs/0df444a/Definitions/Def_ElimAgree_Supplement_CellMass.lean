-- Prove2me | Definitions.Def_ElimAgree_Supplement_CellMass
-- name    : ElimAgree_Supplement_CellMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:35:16.902124+00:00
-- url     : https://prove2.me/theorems/2c84820f-eb85-46c8-9923-1470023b71f8
-- title:
--   $\Omega=\binom{[N]}{\ell}$, the operators $D$, $I$ and $\int\min_\sigma(\bigotimes_i\sigma_i)1_B\,d\pi^{\otimes k}$
-- statement:
--   In §3.8, $N=4\ell-1$, $\pi$ is uniform on $\Omega=\binom{[N]}{\ell}$, and $D$, $I$ are the conditional-expectation operators of $\mu_D$ (uniform on pairs of disjoint $\ell$-sets) and $\mu_I$ (uniform on pairs of $\ell$-sets meeting in one element):
--
--   $$(Dg)(x)=\mathbb E_{\mu_D}[g(Y)\mid X=x],\qquad (Ig)(x)=\mathbb E_{\mu_I}[g(Y)\mid X=x].$$
--
--   For $\sigma\in\{D,I\}^k$, $\bigotimes_i\sigma_i$ acts on functions on $\Omega^k$ by the product kernel. For $B\subseteq\Omega^k$ the mass is $q=\pi^{\otimes k}(B)$, and the quantity of Theorem 3.20 is
--
--   $$\int\min_{\sigma\in\{D,I\}^k}\Big(\bigotimes_i\sigma_i\Big)1_B\,d\pi^{\otimes k},$$
--
--   the minimum taken pointwise.
--
--   **Formalization Note** $\mu_D$, $\mu_I$ are the base definitions on subsets of $[N]$; their kernels are normalized over $\Omega$. $\{D,I\}$ is `Bool` with `true` $=D$, as in the base `muSigma`. The integral is the uniform average over $\Omega^k$.
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), §3.8, p.15 (PDF p.17); Theorem 3.20, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_ElimAgree_muD
import Definitions.Def_ElimAgree_halfSetChannel

namespace ElimAgree

namespace Supplement

/-!
# `Ω = ([N] choose ℓ)`, the operators `D`, `I` and their tensor products (§3.8)

Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*,
manuscript (STOC 2027 submission), §3.8, p.15 and Theorem 3.20, p.16.

**Formalization Note.** `Ω` is the set of `ℓ`-subsets of `[N] = Fin (4ℓ − 1)` (base `LSet`, `Nset`),
`π` is uniform on `Ω`, and `D`, `I` are the conditional-expectation operators of the base laws
`µ_D` (`muD`) and `µ_I` (`muI`): `(Dg)(x) = Σ_y µ_D(x, y) g(y) / Σ_y µ_D(x, y)`. For `σ ∈ {D, I}^k`
the operator `⊗_i σ_i` acts on functions on `Ω^k` by the product kernel. `{D, I}` is `Bool` with
`true = D`, as in the base `muSigma`. The integral against `π^{⊗k}` is the uniform average over
`Ω^k`, and the minimum over `σ` is pointwise, taken over the finite nonempty set `{D, I}^k`.
-/

/-- `Ω = ([N] choose ℓ)` with `N = 4ℓ − 1` (§3.8, p.15). -/
abbrev Omega (ℓ : ℕ) : Type := LSet (Fin (4 * ℓ - 1)) ℓ

/-- The transition kernel of the conditional expectation under a law `µ` on pairs of subsets of
`[N]`, restricted to `Ω`: `P(x, y) = µ(x, y) / Σ_{y'} µ(x, y')`. -/
noncomputable def transK (ℓ : ℕ) (μ : Nset ℓ × Nset ℓ → ℝ) (x y : Omega ℓ) : ℝ :=
  μ (x.1, y.1) / ∑ y' : Omega ℓ, μ (x.1, y'.1)

/-- The kernel of `D` (`s = true`) or `I` (`s = false`). -/
noncomputable def sigmaKer (ℓ : ℕ) (s : Bool) : Omega ℓ → Omega ℓ → ℝ :=
  transK ℓ (if s then muD ℓ else muI ℓ)

/-- `(⊗_i σ_i) u` for `σ ∈ {D, I}^k` and `u` a function on `Ω^k`. -/
noncomputable def tensorOp (ℓ k : ℕ) (σ : Fin k → Bool) (u : (Fin k → Omega ℓ) → ℝ)
    (x : Fin k → Omega ℓ) : ℝ :=
  ∑ y : Fin k → Omega ℓ, (∏ i, sigmaKer ℓ (σ i) (x i) (y i)) * u y

/-- The mass `q = π^{⊗k}(B)` of `B ⊆ Ω^k`. -/
noncomputable def piMass (ℓ k : ℕ) (B : Finset (Fin k → Omega ℓ)) : ℝ :=
  (B.card : ℝ) / (Fintype.card (Omega ℓ) : ℝ) ^ k

/-- `∫ min_{σ ∈ {D, I}^k} (⊗_i σ_i) 1_B dπ^{⊗k}` (Theorem 3.20, p.16). -/
noncomputable def minCellIntegral (ℓ k : ℕ) (B : Finset (Fin k → Omega ℓ)) : ℝ :=
  ∑ x : Fin k → Omega ℓ, (1 / (Fintype.card (Omega ℓ) : ℝ) ^ k) *
    Finset.univ.inf' Finset.univ_nonempty
      (fun σ : Fin k → Bool => tensorOp ℓ k σ (fun y => if y ∈ B then 1 else 0) x)

end Supplement

end ElimAgree


