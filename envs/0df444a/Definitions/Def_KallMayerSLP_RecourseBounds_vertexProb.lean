-- Prove2me | Definitions.Def_KallMayerSLP_RecourseBounds_vertexProb
-- name    : KallMayerSLP_RecourseBounds_vertexProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:11:54.231972+00:00
-- url     : https://prove2.me/theorems/b0a0fb94-3245-4149-aac8-575cae4ebc86
-- title:
--   Vertex distribution $\mathbb P_{\eta(\xi)}$ of a point of a box
-- statement:
--   Let $\Xi=\times_{i=1}^r[a_i,b_i]\subset\mathbb R^r$ be a box and $\xi\in\Xi$. Following Frauendorfer, give each coordinate the two-point law on $\{a_i,b_i\}$ with mean $\xi_i$,
--   $$
--   \mathbb P_{\eta_i(\xi_i)}(a_i)=\frac{b_i-\xi_i}{b_i-a_i},\qquad \mathbb P_{\eta_i(\xi_i)}(b_i)=\frac{\xi_i-a_i}{b_i-a_i},
--   $$
--   and take the product. A vertex $v^\nu$ of $\Xi$ then has probability
--   $$
--   \mathbb P_{\eta(\xi)}(v^\nu)=\prod_{i\in I_\nu}\frac{b_i-\xi_i}{b_i-a_i}\cdot\prod_{i\in J_\nu}\frac{\xi_i-a_i}{b_i-a_i},
--   $$
--   where $I_\nu=\{i\mid v^\nu_i=a_i\}$ and $J_\nu$ is its complement (an empty product is $1$).
--
--   This law on the $2^r$ vertices has mean $\xi$; averaging it over the distribution of $\xi$ gives the generalized Edmundson–Madansky distribution (2.30).
--
--   **Formalization Note** A vertex is a Boolean vector $v$ ($v_i=\mathrm{false}$ selects $a_i$, $\mathrm{true}$ selects $b_i$), the vertex itself is the platform's `NumStochOpt.Bounds.boxVertex`, and the two-point factor is `NumStochOpt.Bounds.emProb`. A degenerate coordinate $a_i=b_i$, where the formula divides by zero, gets the point mass at its single value (factor $1$ for false, $0$ for true); for $a_i<b_i$ the definition is the book's formula.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (2.26)–(2.28), pp.215–216 (PDF 224–225)

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_EdmundsonMadansky

namespace KallMayerSLP.RecourseBounds

/-- **The vertex distribution `IP_{η(ξ)}` of a point of a box.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, (2.26)–(2.28), printed pp.215–216
(PDF 224–225): for a point `ξ` of `Ξ = ×ᵢ [αᵢ, βᵢ]` the independent two-point laws
`IP_{ηᵢ(ξᵢ)}(αᵢ) = (βᵢ − ξᵢ)/(βᵢ − αᵢ)`, `IP_{ηᵢ(ξᵢ)}(βᵢ) = (ξᵢ − αᵢ)/(βᵢ − αᵢ)` give the vertex `v^ν`
the probability
`IP_{η(ξ)}(v^ν) = ∏_{i ∈ I_ν} (βᵢ − ξᵢ)/(βᵢ − αᵢ) · ∏_{i ∈ J_ν} (ξᵢ − αᵢ)/(βᵢ − αᵢ)`,
`I_ν = {i | v^ν_i = αᵢ}`, `J_ν` its complement.

**Formalization Note.** `ℝ^r` is `Fin r → ℝ` (index `0, …, r−1`). A vertex is a Boolean vector `v`
(`v i = false` selects `αᵢ`, i.e. `i ∈ I_ν`; `true` selects `βᵢ`), the vertex itself is
`NumStochOpt.Bounds.boxVertex a b v`, and the two-point factor is the platform's
`NumStochOpt.Bounds.emProb`. A degenerate coordinate `aᵢ = bᵢ` (where the book's formula divides by
zero) gets the point mass at its single value `aᵢ` (factor `1` for `false`, `0` for `true`); this
only extends the book's formula to degenerate boxes and is never used when `aᵢ < bᵢ`. -/
noncomputable def vertexProb {r : ℕ} (a b x : Fin r → ℝ) (v : Fin r → Bool) : ℝ :=
  ∏ i, if a i < b i then NumStochOpt.Bounds.emProb (a i) (b i) (x i) (v i)
    else if v i then 0 else 1

end KallMayerSLP.RecourseBounds


