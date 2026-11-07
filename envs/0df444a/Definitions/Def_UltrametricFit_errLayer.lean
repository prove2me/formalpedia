-- Prove2me | Definitions.Def_UltrametricFit_errLayer
-- name    : UltrametricFit_errLayer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:45:30.880204+00:00
-- url     : https://prove2.me/theorems/ca8352db-1821-4003-950c-ca7b96ac804f
-- title:
--   The biclique quantities $E^\ell_\pm$, $\mathrm{err}_\ell$, $\mathrm{cost}$, $\mathrm{lp}(A\times B,x)$ and the constants $\Gamma_0,\Gamma$
-- statement:
--   For a layer $\ell$ and sets $A,B$:
--   $$E^\ell_+(A,B)=\{(i,j)\in A\times B:X(i,j)\le D_\ell\},\qquad E^\ell_-(A,B)=\{(i,j)\in A\times B:X(i,j)>D_\ell\},$$
--   $$\mathrm{err}_\ell(A,B)=\sum_{ij\in E^\ell_+(A,B)}x_\ell(i,j)+\sum_{ij\in E^\ell_-(A,B)}\bigl(1-x_\ell(i,j)\bigr),$$
--   $$\mathrm{cost}(A,B,\ell^*)=\sum_{i\in A,\,j\in B}|D_{\ell^*}-X(i,j)|^p,\qquad \mathrm{lp}(A\times B,x)=\sum_{i\in A,\,j\in B}\mathrm{lp\text{-}cost}_p(x,i,j),$$
--   and the constants
--   $$\Gamma_0=1+\frac{1-\delta}{\delta(1-2\delta)^2},\qquad \Gamma=\frac{2}{((\Gamma_0+1)/\Gamma_0)^{1/p}-1}.$$
--   These are the objects of the analysis of the algorithm's cost, biclique by biclique.
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), §4.3–4.4, p.11; Lemma 13, p.11

import Mathlib
import Definitions.Def_UltrametricFit_IsFeasible

namespace UltrametricFit

/-- `E^ℓ_+(A, B) = {(i, j) ∈ A × B : X(i, j) ≤ D_ℓ}`, Charikar, Gao, STOC 2027 submission (manuscript
sha256 87af12a2…), §4.4, p.11. -/
noncomputable def Eplus {n : ℕ} (X : Fin n → Fin n → ℝ) (ℓ : ℕ) (A B : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  (A ×ˢ B).filter fun q => X q.1 q.2 ≤ layerValue X ℓ

/-- `E^ℓ_−(A, B) = {(i, j) ∈ A × B : X(i, j) > D_ℓ}`, Charikar, Gao, STOC 2027 submission (manuscript
sha256 87af12a2…), §4.4, p.11. -/
noncomputable def Eminus {n : ℕ} (X : Fin n → Fin n → ℝ) (ℓ : ℕ) (A B : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  (A ×ˢ B).filter fun q => layerValue X ℓ < X q.1 q.2

/-- **The unweighted LP cost on layer ℓ**, Charikar, Gao, STOC 2027 submission (manuscript sha256
87af12a2…), §4.4, p.11:
`err_ℓ(A, B) = Σ_{ij ∈ E^ℓ_+(A,B)} x_ℓ(i, j) + Σ_{ij ∈ E^ℓ_−(A,B)} (1 − x_ℓ(i, j))`. -/
noncomputable def errLayer {n : ℕ} (X : Fin n → Fin n → ℝ) (x : ℕ → Fin n → Fin n → ℝ) (ℓ : ℕ)
    (A B : Finset (Fin n)) : ℝ :=
  ∑ q ∈ Eplus X ℓ A B, x ℓ q.1 q.2 + ∑ q ∈ Eminus X ℓ A B, (1 - x ℓ q.1 q.2)

/-- **The algorithm's cost on a biclique**, Charikar, Gao, STOC 2027 submission (manuscript sha256
87af12a2…), §4.3, p.11: `cost(A, B, ℓ*) = Σ_{i∈A, j∈B} |D_{ℓ*} − X(i, j)|^p`. -/
noncomputable def mergeCost {n : ℕ} (X : Fin n → Fin n → ℝ) (p : ℝ) (ℓ : ℕ)
    (A B : Finset (Fin n)) : ℝ :=
  ∑ i ∈ A, ∑ j ∈ B, |layerValue X ℓ - X i j| ^ p

/-- **The LP cost on a biclique**, Charikar, Gao, STOC 2027 submission (manuscript sha256
87af12a2…), §4.3, p.11: `lp(A × B, x) = Σ_{i∈A, j∈B} lp-cost_p(x, i, j)`. -/
noncomputable def lpBiclique {n : ℕ} (X : Fin n → Fin n → ℝ) (p : ℝ)
    (x : ℕ → Fin n → Fin n → ℝ) (A B : Finset (Fin n)) : ℝ :=
  ∑ i ∈ A, ∑ j ∈ B, lpCostPair X p x i j

/-- `Γ₀ = 1 + (1 − δ)/(δ(1 − 2δ)²)`, Charikar, Gao, STOC 2027 submission (manuscript sha256
87af12a2…), Lemma 13, p.11. -/
noncomputable def Gamma0 (δ : ℝ) : ℝ := 1 + (1 - δ) / (δ * (1 - 2 * δ) ^ 2)

/-- `Γ = 2 / (((Γ₀ + 1)/Γ₀)^{1/p} − 1)`, Charikar, Gao, STOC 2027 submission (manuscript sha256
87af12a2…), Lemma 13, p.11. -/
noncomputable def Gamma (δ p : ℝ) : ℝ :=
  2 / (((Gamma0 δ + 1) / Gamma0 δ) ^ (1 / p) - 1)

end UltrametricFit


