-- Prove2me | Definitions.Def_SubmodSparsify_Supplement_gibbsScore
-- name    : SubmodSparsify_Supplement_gibbsScore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:09:47.782512+00:00
-- url     : https://prove2.me/theorems/0a85d76e-637d-4f69-9aa8-4d514bf1600a
-- title:
--   Algorithm 6: Gibbs scores, discarding of zero components, and $\Lambda = 128\varepsilon^{-2}\log(64n/\delta)$
-- statement:
--   Let $V = [n]$ and $f_1,\dots,f_m : 2^V \to \mathbb R_{\ge0}$, and fix an integer inverse temperature $\beta \ge 1$. For every $u \in V$, on $E = V\setminus\{u\}$, let $s^{(u)}_i$ and $t^{(u)}_i$ be the Gibbs shares (68) of component $i$ in the families $D \mapsto f^{\to}_i(u, D)$ and $D \mapsto f^{\to}_i(D, u)$. Algorithm 6's score is
--
--   $$p_i = \sum_{u \in V} \bigl(s^{(u)}_i + t^{(u)}_i\bigr).$$
--
--   Algorithm 6 discards identically zero components (they receive weight $0$) and samples with
--
--   $$\Lambda = 128\, \varepsilon^{-2} \log(64n/\delta).$$
--
--   **Formalization Note** `discardZero f w` sets $w_i = 0$ when $f_i(S) = 0$ for every $S$ and keeps $w_i$ otherwise. A zero component has Gibbs score $0$, so discarding does not change the scores. Logarithms are natural.
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6793d37e5008919a4795e2e18da7fa5049f06ad4d1b929ac6d7fbc634), Algorithm 6, p.43

import Mathlib
import Definitions.Def_SubmodSparsify_weights
import Definitions.Def_SubmodSparsify_Supplement_gibbsShare

namespace SubmodSparsify.Supplement

/-!
# Algorithm 6: Gibbs scores, the discarding of zero components, and `Λ` (p.43)

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Algorithm 6, p.43.

"2: Discard identically zero components; if none remain, return zero weights […]
4: for all u ∈ V do 5: E ← V \ {u} 6: Hu(x) ← Σᵢ f̂→ᵢ(u, x) for x ∈ R^E≥0
7: Gu(x) ← Σᵢ f̂→ᵢ(x, u) for x ∈ R^E≥0 8: s⁽ᵘ⁾ᵢ ← E_{Xu∼µHu} f̂→ᵢ(u, Xu) for i ∈ [m]
9: t⁽ᵘ⁾ᵢ ← E_{Yu∼µGu} f̂→ᵢ(Yu, u) for i ∈ [m] 10: end for
11: pᵢ ← Σ_{u∈V}(s⁽ᵘ⁾ᵢ + t⁽ᵘ⁾ᵢ) for i ∈ [m] 12: Λ ← 128ε⁻² log(64n/δ) […]
14: Independently draw ξᵢ ∼ Bernoulli(min{1, Λpᵢ}) 15: wᵢ ← ξᵢ/min{1, Λpᵢ}"

**Formalization Note.**
* `V = [n]` is `Fin n`, components `f : Fin m → Finset (Fin n) → ℝ` (paper index = value + 1).
* `s⁽ᵘ⁾ᵢ` and `t⁽ᵘ⁾ᵢ` are the Gibbs shares (68) of the base terminal families
  `inFamily f u` (`D ↦ f→ᵢ(u, D)`) and `outFamily f u` (`D ↦ f→ᵢ(D, u)`) on `[n] \ {u}`; the
  Gibbs law of `H_u` (resp. `G_u`) is that of the family's sum.
* A discarded (identically zero) component gets weight `0`: `discardZero f w` sets `wᵢ = 0`
  whenever `fᵢ(S) = 0` for every `S`, and keeps `wᵢ` otherwise. If no component remains every
  weight is `0`, as in line 2. A zero component has Gibbs score `0` anyway, so the scores `pᵢ`
  are unaffected by the discarding.
* `Λ = 128 ε⁻² log(64n/δ)` with the natural logarithm.
-/

variable {n m : ℕ}

/-- Algorithm 6, line 11: `pᵢ = Σ_u (s⁽ᵘ⁾ᵢ + t⁽ᵘ⁾ᵢ)` at inverse temperature `β`. -/
noncomputable def gibbsScore (β : ℕ) (f : Fin m → Finset (Fin n) → ℝ) (i : Fin m) : ℝ :=
  ∑ u, (gibbsShare β (inFamily f u) (Finset.univ.erase u) i +
    gibbsShare β (outFamily f u) (Finset.univ.erase u) i)

/-- Algorithm 6, line 2: identically zero components get weight `0`. -/
noncomputable def discardZero (f : Fin m → Finset (Fin n) → ℝ) (w : Fin m → ℝ) (i : Fin m) :
    ℝ := by
  classical exact if ∀ S, f i S = 0 then 0 else w i

/-- Algorithm 6, line 12: `Λ = 128 ε⁻² log(64n/δ)` (natural logarithm). -/
noncomputable def gibbsScale (n : ℕ) (ε δ : ℝ) : ℝ :=
  128 * ε⁻¹ ^ 2 * Real.log (64 * (n : ℝ) / δ)

end SubmodSparsify.Supplement


