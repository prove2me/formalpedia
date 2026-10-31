-- Prove2me | Definitions.Def_KempeCloning_relFreqA1
-- name    : KempeCloning_relFreqA1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:23:30.381405+00:00
-- url     : https://prove2.me/theorems/9defce93-5390-44f2-a670-1acf3a40d9e0
-- title:
--   Mean relative frequency of photons in the correct mode $a_1$
-- statement:
--   For a finite superposition $|\psi\rangle = \sum_n \psi(n)|n\rangle$ of number states,
--
--   $$\mathrm{relFreq}_{a_1}(\psi) = \sum_n |\psi(n)|^2\;\frac{n_{a_1}}{n_{a_1} + n_{a_2}} ,$$
--
--   the $|\text{amplitude}|^2$-weighted mean of the fraction of photons that are in the correct mode $a_1$. For a normalized state this is the paper's cloning fidelity: "the mean relative frequency of photons in the correct mode ($a_1$ in our case). In the state $|m+l-i, i\rangle_{photons}$ the relative frequency of correct photons is $(m+l-i)/(m+l)$."
--
--   **Formalization Note** The weights are not divided by $\langle\psi|\psi\rangle$; the mission applies the definition to normalized states. The denominator is each basis state's own photon number; on a basis state with no photons the term is $0$ (Lean's $x/0 = 0$), which does not occur for $|\mathcal F_l\rangle$ with $m+l\ge1$.
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II C, sentence before (20), p.5

import Definitions.Def_KempeCloning_FockVec

namespace KempeCloning

/-- **Mean relative frequency of photons in the good mode `a₁` (the cloning fidelity).**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II C, sentence before (20), p.5: "let us
calculate the fidelity of the cloning, given by the mean relative frequency of photons in the
correct mode (a1 in our case). In the state |m + l − i, i⟩photons the relative frequency of correct
photons is (m + l − i)/(m + l)."

For a Fock vector `ψ = Σ_n ψ(n)|n⟩`,
`relFreqA1 ψ = Σ_n |ψ(n)|² · n_{a1} / (n_{a1} + n_{a2})`,
the `|amplitude|²`-weighted mean of the fraction of photons in mode `a₁`.

**Formalization Note.** The weights are `|ψ(n)|²` without dividing by `⟨ψ|ψ⟩`, so this is the mean
relative frequency for a normalized `ψ` (the mission applies it to the normalized `|F_l⟩`). The
denominator is each basis state's own photon number `n_{a1} + n_{a2}`, not a fixed `m + l`; at a
basis state with no photons Lean's convention `x / 0 = 0` gives the term `0` (this case does not
occur in `|F_l⟩` with `m + l ≥ 1`). -/
noncomputable def relFreqA1 (ψ : FockVec) : ℝ :=
  ∑ n ∈ ψ.support, ‖ψ n‖ ^ 2 * ((n Mode.a1 : ℝ) / ((n Mode.a1 : ℝ) + (n Mode.a2 : ℝ)))

end KempeCloning


