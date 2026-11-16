-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_Supplement_SpectralAdversary
-- name    : TarskiBootstrap_Dimensional_Supplement_SpectralAdversary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:02:05.634548+00:00
-- url     : https://prove2.me/theorems/d6aecc88-8e58-47ed-b77b-7cb3e76d1040
-- title:
--   Spectral adversary ratio and value $\mathrm{SA}(\Phi)$
-- statement:
--   Let $\Phi$ be a function on a set $S\subseteq\Sigma^I$ of query strings, with $I$ and $\Sigma$ finite; the oracle of an input $x\in S$ is the string $x$ itself, and $\Delta_i[x,y]=1$ exactly when $x_i\ne y_i$ (Definition 2.5). For a real matrix $\Gamma$ indexed by $S$, its **adversary ratio** is
--
--   $$
--   \frac{\|\Gamma\|}{\max_{i\in I}\|\Gamma\circ\Delta_i\|},
--   $$
--
--   where $\|\cdot\|$ is the spectral (Euclidean operator) norm and $\circ$ the entrywise product. The **spectral adversary value** is
--
--   $$
--   \mathrm{SA}(\Phi)=\sup\Bigl\{\frac{\|\Gamma\|}{\max_{i\in I}\|\Gamma\circ\Delta_i\|}\;:\;\Gamma\ne0\text{ a nonnegative adversary matrix for }\Phi|_S\Bigr\},
--   $$
--
--   with $\mathrm{SA}(\Phi)=0$ when no nonzero nonnegative adversary matrix exists, i.e. when $\Phi$ is constant on $S$.
--
--   This is equation (2.8). For a nonzero nonnegative adversary matrix the denominator is positive and the ratio is at most $|I|$, and the supremum is attained, so the supremum coincides with the maximum of (2.8).
--
--   **Formalization Note** The ratio is stated for an arbitrary oracle; a zero denominator yields the Lean value $0$ (it never occurs for nonzero adversary matrices of string inputs). The supremum is a real `sSup`, which is $0$ on the empty set, matching the convention for constant $\Phi$. Only the values of $\Phi$ on $S$ enter.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, equation (2.8) and Definitions 2.4–2.5, PDF/printed p. 7, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. Printed page = PDF page. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Adversary
import Definitions.Def_TarskiBootstrap_Dimensional_QueryMask

open scoped Matrix

namespace TarskiBootstrap.Dimensional.Supplement

/-- The adversary ratio `‖Γ‖ / max_i ‖Γ ∘ Δ_i‖` of (2.8), PDF/printed p. 7, with
real Euclidean (spectral) operator norms and the distinguisher matrices `Δ_i` of
Definition 2.5 for the given oracle. The maximum over the finite query set is a real
`⨆`; a zero denominator gives the Lean value `0`. -/
noncomputable def adversaryRatio {S Q O : Type*} [Fintype S]
    (oracle : S → Q → O) (Γ : Matrix S S ℝ) : ℝ := by
  classical
  exact ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖ /
    ⨆ x : Q, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Γ ⊙ queryMask oracle x)‖

/-- The spectral adversary value `SA(Φ)` of (2.8), PDF/printed p. 7, for a function
`Φ` on a set `S ⊆ Σ^I` of query strings (`I`, `Σ` finite): the supremum, over all
nonzero nonnegative adversary matrices `Γ` for `Φ|S` (Definition 2.4), of
`‖Γ‖ / max_{i ∈ I} ‖Γ ∘ Δ_i‖`. The oracle of an input is the string itself.
If no nonzero nonnegative adversary matrix exists (`Φ` constant on `S`), the set is
empty and the value is `sSup ∅ = 0`, the convention of p. 7. Only the values of `Φ`
on `S` matter. -/
noncomputable def spectralAdversary {I Sig Out : Type*} [Finite I] [Finite Sig]
    (S : Set (I → Sig)) (Φ : (I → Sig) → Out) : ℝ := by
  classical
  haveI : Fintype S := Fintype.ofFinite S
  exact sSup {r : ℝ | ∃ Γ : Matrix S S ℝ, Γ ≠ 0 ∧
    NonnegativeAdversary (fun x : S => Φ x.val) Γ ∧
    r = adversaryRatio (fun x : S => x.val) Γ}

end TarskiBootstrap.Dimensional.Supplement


