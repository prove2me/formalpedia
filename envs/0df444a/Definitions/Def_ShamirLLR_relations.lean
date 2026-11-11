-- Prove2me | Definitions.Def_ShamirLLR_relations
-- name    : ShamirLLR_relations
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:02.002586+00:00
-- url     : https://prove2.me/theorems/42035c14-df67-47a5-ad08-2c1ba6d4ac43
-- title:
--   Shortened moment forms, block spaces $E_i$ and the relation space $R$
-- statement:
--   In the setting of §7.4, let $(a_i)_{i\in I}$ be places, $r'\ge1$ and $\tilde L_i(x)=\sum_{h<r'}a_i^hx_h$, a polynomial in $x_0,\dots,x_{r'-1}$. For $\beta_{i,1},\beta_{i,2}\in\mathbb F_p^{d_i}$ let $E_i=\mathrm{span}\{\beta_{i,1},\beta_{i,2}\}$. A Fourier tuple $\gamma=(\gamma_i)_i$, $\gamma_i\in E_i^*$, defines
--   $$
--   Q_\gamma(x)=\sum_{i\in I}\Bigl(\gamma_i(\beta_{i,1})\tilde L_i(x)+\gamma_i(\beta_{i,2})\tilde L_i(x)^2\Bigr),
--   $$
--   and $\gamma$ is a **relation**, $\gamma\in R$, when $Q_\gamma$ is identically zero as a polynomial.
--
--   Only relations contribute to the leakage probabilities in the finite Fourier calculation.
--
--   **Formalization Note** Polynomials are `MvPolynomial (Fin r') (ZMod p)`.
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), §7.4, Eq. (53)–(60), pp.54–55 (PDF pp.55–56)

import Mathlib

set_option autoImplicit false

namespace ShamirLLR

/-- The shortened moment form `L̃_i(x) = ∑_{h=0}^{r'-1} a_i^h x_h` as a polynomial in the
variables `x₀, …, x_{r'-1}` (§7.4, Eq. (53), p.54).

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
§7.4, pp.54–56. -/
noncomputable def momentPoly {p : ℕ} {I : Type*} (a : I → ZMod p) (r' : ℕ) (i : I) :
    MvPolynomial (Fin r') (ZMod p) :=
  ∑ h : Fin r', MvPolynomial.C (a i ^ (h : ℕ)) * MvPolynomial.X h

/-- The block space `E_i = span_{𝔽_p}{β_{i,1}, β_{i,2}} ⊆ 𝔽_p^{d_i}` of §7.4, p.54. -/
def blockSpace {p d : ℕ} (β₁ β₂ : Fin d → ZMod p) : Submodule (ZMod p) (Fin d → ZMod p) :=
  Submodule.span (ZMod p) {β₁, β₂}

/-- The polynomial `Q_γ(x) = ∑_{i ∈ I} (γ_i(β_{i,1}) L̃_i(x) + γ_i(β_{i,2}) L̃_i(x)²)` of a Fourier
tuple `γ = (γ_i)_i`, `γ_i ∈ E_i^*` (§7.4, p.55). -/
noncomputable def relPoly {p : ℕ} {I : Type*} [Fintype I] (a : I → ZMod p) (r' : ℕ)
    {d : I → ℕ} (β₁ β₂ : (i : I) → Fin (d i) → ZMod p)
    (γ : (i : I) → Module.Dual (ZMod p) (blockSpace (β₁ i) (β₂ i))) :
    MvPolynomial (Fin r') (ZMod p) :=
  ∑ i, (MvPolynomial.C (γ i ⟨β₁ i, Submodule.subset_span (by simp)⟩) * momentPoly a r' i +
    MvPolynomial.C (γ i ⟨β₂ i, Submodule.subset_span (by simp)⟩) * momentPoly a r' i ^ 2)

/-- `γ` is a relation, `γ ∈ R`: `Q_γ` is identically zero as a polynomial (§7.4, p.55: "Let R be
the 𝔽_p-vector space of tuples for which Q_γ is identically zero as a polynomial"). -/
def IsRelation {p : ℕ} {I : Type*} [Fintype I] (a : I → ZMod p) (r' : ℕ) {d : I → ℕ}
    (β₁ β₂ : (i : I) → Fin (d i) → ZMod p)
    (γ : (i : I) → Module.Dual (ZMod p) (blockSpace (β₁ i) (β₂ i))) : Prop :=
  relPoly a r' β₁ β₂ γ = 0

end ShamirLLR


