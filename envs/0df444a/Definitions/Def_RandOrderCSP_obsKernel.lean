-- Prove2me | Definitions.Def_RandOrderCSP_obsKernel
-- name    : RandOrderCSP_obsKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:11.148207+00:00
-- url     : https://prove2.me/theorems/4cb76312-171d-490c-aee6-4f5630d9c5b2
-- title:
--   The observation kernel $T_\Phi$, its pushforward and the posterior
-- statement:
--   For a $\Delta_1(\mathbb Z_q^k)$-colored hypergraph $\Phi=(H,\mathcal Y)$, the coboundary is $(\Pi_HX)_{j,\ell}=X_{M_H(j,\ell)}$ and the **observation kernel** is $T_\Phi(X)=\mathrm{Law}(\Pi_HX-\mathbf Y)$ with $\mathbf Y\sim\bigotimes\mathcal Y$. Its pushforward is $(T_\Phi)_*D(Z)=\sum_XD(X)T_\Phi(X,Z)$. A set $\mathcal B$ of label matrices is **nontrivial** if it has positive mass under the pushforward, and then
--
--   $$\mathrm{Post}(D,\Phi,\mathcal B)(X)=\frac{D(X)\sum_{Z\in\mathcal B}T_\Phi(X,Z)}{\mathbb P_{(T_\Phi)_*D}[\mathcal B]}.$$
--
--   This is the law of the hidden signal $\mathbf X\sim D$ given $\mathbf Z\in\mathcal B$.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), Definitions 4.2, 5.8, pp.16–17, 24

import Mathlib
import Definitions.Def_RandOrderCSP_Hypergraph

namespace RandOrderCSP

variable {k q : ℕ} {V E : Type}

/-- The coboundary operator `Π_H : ℤ_q^{𝒱_H} → ℤ_q^{ℰ_H×[k]}` (4.1), p.16:
`(Π_H X)_{j,ℓ} := X_{M_H(j,ℓ)}`. -/
def coboundary (H : Hypergraph k V E) (X : V → ZMod q) : E × Fin k → ZMod q :=
  fun p => X (H.M p.1 p.2)

/-- **The observation kernel `T_Φ`** (Definition 4.2, p.17).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), p.17: "For a Δ₁(Z_q^k)-colored hypergraph
Φ = (H, 𝒴), define the Markov kernel T_Φ : Z_q^{𝒱_H} → Δ(Z_q^{ℰ_H×[k]}) by
T_Φ(X) := Law(Π_H X − 𝐘), 𝐘 ∼ ⨂𝒴."

**Formalization Note.** `Z = Π_H X − 𝐘` exactly when `𝐘 = Π_H X − Z`, and the rows of `𝐘` are
independent with laws `𝒴(j)`, so the probability of `Z` is the product over `j` written here. -/
def obsKernel [Fintype E] (H : Hypergraph k V E) (Y : E → (Fin k → ZMod q) → ℝ)
    (X : V → ZMod q) (Z : E × Fin k → ZMod q) : ℝ :=
  ∏ j, Y j (fun ℓ => coboundary H X (j, ℓ) - Z (j, ℓ))

/-- The pushforward `(T_Φ)_* D` (3.4), p.12: `Z ↦ ∑_X D(X) T_Φ(X, Z)`. -/
def pushObs [Fintype V] [DecidableEq V] [NeZero q] [Fintype E] (H : Hypergraph k V E)
    (Y : E → (Fin k → ZMod q) → ℝ) (D : (V → ZMod q) → ℝ) (Z : E × Fin k → ZMod q) : ℝ :=
  ∑ X, D X * obsKernel H Y X Z

/-- `P_{(T_Φ)_* D}[ℬ]`, the mass of `ℬ` under the pushforward. -/
def pushObsMass [Fintype V] [DecidableEq V] [NeZero q] [Fintype E] (H : Hypergraph k V E)
    (Y : E → (Fin k → ZMod q) → ℝ) (D : (V → ZMod q) → ℝ) (B : Finset (E × Fin k → ZMod q)) : ℝ :=
  ∑ Z ∈ B, pushObs H Y D Z

/-- **The posterior `Post(D, Φ, ℬ)`** (Definition 5.8, p.24): `Law(𝐗 | 𝐙 ∈ ℬ)` for `𝐗 ∼ D`,
`𝐙 ∼ T_Φ(𝐗)`, written by Bayes' rule (5.9). `ℬ` is nontrivial when `0 < pushObsMass H Y D ℬ`; the
theorems use the posterior only for such `ℬ`. -/
noncomputable def posterior [Fintype V] [DecidableEq V] [NeZero q] [Fintype E] (H : Hypergraph k V E)
    (Y : E → (Fin k → ZMod q) → ℝ) (D : (V → ZMod q) → ℝ) (B : Finset (E × Fin k → ZMod q))
    (X : V → ZMod q) : ℝ :=
  D X * (∑ Z ∈ B, obsKernel H Y X Z) / pushObsMass H Y D B

end RandOrderCSP


