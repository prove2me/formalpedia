-- Prove2me | Definitions.Def_NonadaptiveSFT_Subgroups
-- name    : NonadaptiveSFT_Subgroups
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:40.363903+00:00
-- url     : https://prove2.me/theorems/76e0adab-a0e8-4e53-9de4-57c005e4f0a8
-- title:
--   The subgroup chain $H_j$, its annihilators $K_j$, and the node statistics $h_{v,j,R}$, $F_{v,j,R}$, $W_{v,j,R}$
-- statement:
--   For an integer $0\le j=\ell a+c<ad$ with $0\le c<a$,
--
--   $$H_j=\{0\}^\ell\times(2^c\mathbb Z/2^a\mathbb Z)\times(\mathbb Z/2^a\mathbb Z)^{d-\ell-1},$$
--
--   and $H_{ad}=\{0\}^d$; in particular $H_0=G$. The nodes at depth $j$ of the frequency search tree are the cosets $v+H_j$. The annihilator of $H_j$ is
--
--   $$K_j=\{z\in G:\chi_h(z)=1\text{ for every }h\in H_j\}.$$
--
--   For a residual signal $R$ with spectrum $\widehat R$,
--
--   $$h_{v,j,R}(t)=\sum_{f\in v+H_j}\widehat R(f)\chi_f(t),\qquad F_{v,j,R}=\mathbb E_t|h_{v,j,R}(t)|,\qquad W_{v,j,R}=\sum_{f\in v+H_j}|\widehat R(f)|^2,$$
--
--   where $\mathbb E_t$ is the uniform average over $G$. $h_{v,j,R}$ is the Fourier projection of $R$ onto the node $v+H_j$, $F$ its average magnitude and $W$ its energy; the locator tests nodes through these statistics.
--
--   **Formalization Note** The paper's coordinate $i$ is the index $i-1$; $\ell=\lfloor j/a\rfloor$ and $c=j\bmod a$. $K_j$ is defined as the annihilator; its product form is a clause of Proposition 8.
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), §3, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_NonadaptiveSFT_Fourier

open scoped BigOperators

namespace NonadaptiveSFT

/-!
# The subgroup chain `H_j`, its annihilators `K_j`, and the node statistics `h`, `F`, `W`

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…), §3, p.21 (PDF p.23).

"for integer 0 ≤ j = ℓa + c < ad, where 0 ≤ c < a, define
H_j = {0}^ℓ × (2^cZ/2^aZ) × (Z/2^aZ)^{d−ℓ−1}, and let H_ad = {0}^d and H_0 = G."
"For a residual signal R with spectrum R̂, define
h_{v,j,R}(t) = Σ_{f∈v+H_j} R̂(f)χ_f(t), F_{v,j,R} = E_t |h_{v,j,R}(t)|, W_{v,j,R} = Σ_{f∈v+H_j} |R̂(f)|²."

**Formalization Note.**
* The paper's coordinates `1, …, ℓ` are the indices `i < ℓ`, its coordinate `ℓ + 1` is the index
  `ℓ`. For `j < ad`, `ℓ = j / a` and `c = j % a`. `2^cℤ/2^aℤ` is the set of multiples of `2^c` in
  `ZMod (2^a)`. For `j ≥ ad`, `H_j = {0}` (only `j = ad` is used). `H_0 = G` holds by the formula.
* `Kann j` is the annihilator `{z ∈ G : χ_h(z) = 1 for every h ∈ H_j}`, the paper's *definition* of
  `K_j`; its product form is a clause of Proposition 8.
* `coset v j = v + H_j = {f : f − v ∈ H_j}`.
* `E_t` is the uniform average `(1/N) Σ_t` over `G`, `N = 2^{ad}`; `R̂ = hat R`.
-/

/-- `H_j = {0}^ℓ × 2^cℤ/2^aℤ × (ℤ/2^aℤ)^{d−ℓ−1}` for `j = ℓa + c < ad`, and `{0}` for `j ≥ ad`. -/
noncomputable def Hsub (a d j : ℕ) : Finset (G a d) := by
  classical exact
    if j < a * d then
      Finset.univ.filter fun f => ∀ i : Fin d,
        ((i : ℕ) < j / a → f i = 0) ∧ ((i : ℕ) = j / a → ∃ m : ZMod (2 ^ a), f i = 2 ^ (j % a) * m)
    else {0}

/-- The annihilator `K_j = {z ∈ G : χ_h(z) = 1 for every h ∈ H_j}`. -/
noncomputable def Kann (a d j : ℕ) : Finset (G a d) := by
  classical exact Finset.univ.filter fun z => ∀ h ∈ Hsub a d j, chi h z = 1

/-- The node (coset) `v + H_j`. -/
noncomputable def coset {a d : ℕ} (v : G a d) (j : ℕ) : Finset (G a d) := by
  classical exact Finset.univ.filter fun f => f - v ∈ Hsub a d j

/-- The projection `h_{v,j,R}(t) = Σ_{f ∈ v+H_j} R̂(f) χ_f(t)`. -/
noncomputable def hproj {a d : ℕ} (v : G a d) (j : ℕ) (R : G a d → ℂ) (t : G a d) : ℂ :=
  ∑ f ∈ coset v j, hat R f * chi f t

/-- The average magnitude `F_{v,j,R} = E_t |h_{v,j,R}(t)|`. -/
noncomputable def Fstat {a d : ℕ} (v : G a d) (j : ℕ) (R : G a d → ℂ) : ℝ :=
  (1 / (2 : ℝ) ^ (a * d)) * ∑ t, ‖hproj v j R t‖

/-- The energy `W_{v,j,R} = Σ_{f ∈ v+H_j} |R̂(f)|²`. -/
noncomputable def Wstat {a d : ℕ} (v : G a d) (j : ℕ) (R : G a d → ℂ) : ℝ :=
  ∑ f ∈ coset v j, ‖hat R f‖ ^ 2

end NonadaptiveSFT


