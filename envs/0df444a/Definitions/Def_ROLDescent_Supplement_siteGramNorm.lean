-- Prove2me | Definitions.Def_ROLDescent_Supplement_siteGramNorm
-- name    : ROLDescent_Supplement_siteGramNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:56:48.043071+00:00
-- url     : https://prove2.me/theorems/61e87111-c29c-49a1-8c94-a4bf0f00492e
-- title:
--   Gram norm $\theta_S$ of the complete site hierarchy with weights $1/m$
-- statement:
--   For the observable hierarchy $(I_S)_{S\subseteq V}$ of a full-support law $\mu$ on $\{0,1\}^V$, with $E_{S,i}=\Pi_S-\Pi_{S\cup\{i\}}$ ($\Pi_S$ the orthogonal projection onto $I_S$) and $m=n-|S|$, $n=|V|$, the **Gram norm** of the complete uniform hierarchy at $S$ is
--
--   $$\theta_S=\Big\|\sum_{i\notin S}\frac1m\,E_{S,i}\big|_{I_S}\Big\| .$$
--
--   This is the Gram norm (75) of the general hierarchy, with the outgoing probabilities $\pi_S(i)=1/m$ of the complete complex (94).
--
--   **Formalization Note** The published `ROLDescent.gramNorm` is instantiated at the complete complex $2^V$ with facet size $n$ and weight $1$ on its single facet $V$; then the link of $S$ is $V\setminus S$ and $\pi_S(i)=1/m$. The subspaces are the observable hierarchy in the transported $L^2(\mu)$ metric.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), eq. (75), p.31; eqs. (94)–(95), p.41; Section 6.2.1, p.47 (PDF 31, 41, 47)

import Mathlib
import Definitions.Def_ROLDescent_gramNorm
import Definitions.Def_ROLDescent_Supplement_obsSubspace

namespace ROLDescent.Supplement

/-- **Gram norm `θ_S` of the complete site hierarchy** with uniform weights, eqs. (75), (94), (95).
Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), eq. (75), p.31 (PDF 31): "θ_τ := ‖Σ_{i∈N_τ} π_τ(i) E_{τ,i}|_{I_τ}‖"; eq. (94)–(95), p.41
(PDF 41): in the complete uniform hierarchy `π_S(i) = 1/m` and `‖C_S‖ = mθ_S`; Section 6.2.1,
p.47: the observable hierarchy (108) lives on "the complete site hierarchy [which] records only
S ⊆ V".

**Formalization Note** The published `ROLDescent.gramNorm` is instantiated at the complete complex
`2^V` (`Finset.univ.powerset`), facet size `d = n = |V|`, and facet weight `1` on the single
facet `V` (`0` on non-facets, never read). Then `N_S = V ∖ S` and `π_S(i) = 1/(n − |S|) = 1/m` for
`i ∉ S`. The subspaces are the observable hierarchy `obsSubspace μ` of (108) in the transported
`L²(µ)` metric. -/
noncomputable def siteGramNorm {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ)
    (S : Finset V) : ℝ :=
  ROLDescent.gramNorm (Finset.univ : Finset V).powerset (Fintype.card V)
    (fun F => if F = Finset.univ then 1 else 0) (obsSubspace μ) S

end ROLDescent.Supplement


