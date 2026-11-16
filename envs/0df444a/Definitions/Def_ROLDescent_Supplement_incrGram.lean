-- Prove2me | Definitions.Def_ROLDescent_Supplement_incrGram
-- name    : ROLDescent_Supplement_incrGram
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:55:46.150511+00:00
-- url     : https://prove2.me/theorems/689ac7e4-9bdb-46ec-b9b4-73ce00780e6a
-- title:
--   Increment Gram matrix $C^{\mu_{S,s}}$ of the normalized centered spins
-- statement:
--   For $i\notin S$ let
--
--   $$u_i=\frac{X_i-\mathbb E_{\mu_{S,s}}X_i}{\sqrt{\operatorname{Var}_{\mu_{S,s}}(X_i)}}$$
--
--   be the normalized centered spin at site $i$ under the conditional law $\mu_{S,s}$. The **increment Gram matrix** $C^{\mu_{S,s}}$ is the Gram matrix of these functions in $L^2(\mu_{S,s})$:
--
--   $$C^{\mu_{S,s}}_{ij}=\langle u_i,u_j\rangle_{L^2(\mu_{S,s})}=\sum_x \mu_{S,s}(x)\,\overline{u_i(x)}\,u_j(x),\qquad i,j\in V\setminus S .$$
--
--   The $u_i$ represent the single-site increment directions at the fixed assignment $X_S=s$.
--
--   **Formalization Note** Observables are complex-valued, so the matrix is complex with the conjugate-linear first slot; the $u_i$ are real.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Theorem 6.4, p.50 (PDF 50)

import Mathlib
import Definitions.Def_ROLDescent_Supplement_condCov

namespace ROLDescent.Supplement

/-- **Increment Gram matrix** `C^{µ_{S,s}}` of the normalized centered spins.
Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Theorem 6.4, p.50 (PDF 50): "Let C^{µS,s} be the Gram matrix in L²(µS,s) of the normalized
centered functions u_i := (X_i − E_{µS,s}X_i) / √Var_{µS,s}(X_i) (i ∉ S)."

The entry `(i, j)` is `⟨u_i, u_j⟩_{L²(µS,s)} = Σ_x µS,s(x) conj(u_i(x)) u_j(x)`.

**Formalization Note** Observables are ℂ-valued (Section 6.2.1, p.47), so the Gram matrix is a
complex matrix with the conjugate-linear first slot; `u_i` is real-valued. Indexed by the remaining
sites `{i : V // i ∉ S}`. `Var_{µS,s}(X_i)` is `condCov μ S s i i`. -/
noncomputable def incrGram {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ) (S : Finset V)
    (s : S → Bool) : Matrix {i : V // i ∉ S} {i : V // i ∉ S} ℂ :=
  let u : {i : V // i ∉ S} → (V → Bool) → ℝ := fun i x =>
    ((if x i.1 then 1 else 0) - ∑ y, condLaw μ S s y * (if y i.1 then 1 else 0)) /
      Real.sqrt (condCov μ S s i i)
  fun i j => ∑ x, ((condLaw μ S s x : ℝ) : ℂ) * star ((u i x : ℝ) : ℂ) * ((u j x : ℝ) : ℂ)

end ROLDescent.Supplement


