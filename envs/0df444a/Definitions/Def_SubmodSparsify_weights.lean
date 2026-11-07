-- Prove2me | Definitions.Def_SubmodSparsify_weights
-- name    : SubmodSparsify_weights
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:27.171777+00:00
-- url     : https://prove2.me/theorems/3210113a-a470-4f2a-aae5-7137de649d15
-- title:
--   Algorithm 1 — sampling weights $p_i$, terminal prices, influences $\inf_S$, residuals $\Delta_i$ and $\Lambda$
-- statement:
--   Let $f_1, \dots, f_m : 2^{[n]} \to \mathbb R$ be set functions. For a vertex $u \in [n]$, the **inside-terminal family** is $(f_i^{\to}(u, \cdot))_{i=1}^m$ and the **outside-terminal family** is $(f_i^{\to}(\cdot, u))_{i=1}^m$, both on the ground set $E = [n] \setminus \{u\}$. Let $s_i^{(u)}$ and $b^{(u,\mathrm{in})}$ be the shares and the price vector (15) of the decomposition of the inside-terminal family of $u$, and $t_i^{(v)}$ and $b^{(v,\mathrm{out})}$ those of the outside-terminal family of $v$. **Algorithm 1**'s sampling weights are
--
--   $$p_i := \sum_{u \in [n]} s_i^{(u)} + \sum_{v \in [n]} t_i^{(v)} \qquad (i \in [m]).$$
--
--   For a query $S \subseteq [n]$ with complement $\bar S$, the **influence** of a coordinate $w$ and the **residual** of component $i$ for a free set $U$ are
--
--   $$\inf_S(w) := \begin{cases} \max_{v \in \bar S} b^{(v,\mathrm{out})}(w), & w \in S,\\ \max_{u \in S} b^{(u,\mathrm{in})}(w), & w \in \bar S,\end{cases} \qquad \Delta_i(S, U) := f_i(S) - f_i^{\to}(S \setminus U, \bar S \setminus U),$$
--
--   with the maximum over the empty set equal to zero (displays (25) and (24)). Finally Algorithm 1 uses the sampling scale $\Lambda := 56\,\varepsilon^{-2} \log(32 n/\delta)$.
--
--   **Formalization Note** $[n]$ is `Fin n` and the components are `f : Fin m → Finset (Fin n) → ℝ` (paper indices = values + 1). The shares and prices are those of (15) (definition `SubmodSparsify.chain`), which Algorithm 2 computes exactly (Claim 4.3). $\log$ is the natural logarithm.
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), Algorithm 1, p.18 (PDF p.20); §4.2, (24)–(25), p.24 (PDF p.26)

import Mathlib
import Definitions.Def_SubmodSparsify_blockMinCut
import Definitions.Def_SubmodSparsify_chain

namespace SubmodSparsify

/-!
# Algorithm 1's sampling weights, the terminal prices, influences and residuals (§4, pp.18–24)

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Algorithm 1, p.18; §4.2, p.24.

"for each vertex u ∈ [n], it considers the inside-to-outside family (f→i(u, ·))_{i=1}^m and the
outside-to-inside family (f→i(·, u))_{i=1}^m on the ground set E = [n] \ {u}, and invokes the
subroutine Decomposition (Algorithm 2) to compute their ground-state component shares
(s(u)i)_{i=1}^m and (t(u)i)_{i=1}^m […]. Summing these 2n share vectors gives
pi = Σ_{u∈[n]} s(u)i + Σ_{v∈[n]} t(v)i" (p.18). Prices b(u,in), b(v,out) of the terminal
families (p.24); influences (25) and residuals (24) (p.24); Λ of Algorithm 1, line 8 (p.18).

**Formalization Note.**
* Ground set `[n]` is `Fin n` (paper index = value + 1); components are
  `f : Fin m → Finset (Fin n) → ℝ` (paper index = value + 1); `S̄` is `Sᶜ`.
* The shares and prices are those of (15) (module `SubmodSparsify.chain`), i.e. the values that
  Algorithm 2 computes (Claim 4.3); the weights are thus Algorithm 1's weights, as functions of
  `f`.
* `Λ` uses the natural logarithm (Step 3 of §4.3, p.27, needs `e^{−ℓ log(32n/δ)} = (δ/32n)^ℓ`).
-/

variable {n m : ℕ}

/-- The inside-terminal family `(f→ᵢ(u, ·))ᵢ` on `E = [n] \ {u}`. -/
noncomputable def inFamily (f : Fin m → Finset (Fin n) → ℝ) (u : Fin n) :
    Fin m → Finset (Fin n) → ℝ :=
  fun i C => blockMinCut (f i) {u} C

/-- The outside-terminal family `(f→ᵢ(·, v))ᵢ` on `E = [n] \ {v}`. -/
noncomputable def outFamily (f : Fin m → Finset (Fin n) → ℝ) (v : Fin n) :
    Fin m → Finset (Fin n) → ℝ :=
  fun i C => blockMinCut (f i) C {v}

/-- `s_i^{(u)}`: the share of component `i` in the decomposition of the inside-terminal family
of `u` on `[n] \ {u}`. -/
noncomputable def inShare (f : Fin m → Finset (Fin n) → ℝ) (u : Fin n) (i : Fin m) : ℝ :=
  share (inFamily f u) (Finset.univ.erase u) i

/-- `t_i^{(v)}`: the share of component `i` in the decomposition of the outside-terminal family
of `v` on `[n] \ {v}`. -/
noncomputable def outShare (f : Fin m → Finset (Fin n) → ℝ) (v : Fin n) (i : Fin m) : ℝ :=
  share (outFamily f v) (Finset.univ.erase v) i

/-- `b^{(u,in)}`: the coordinate price vector of the inside-terminal family of `u`. -/
noncomputable def inPrice (f : Fin m → Finset (Fin n) → ℝ) (u : Fin n) : Fin n → ℝ :=
  price (sumFn (inFamily f u)) (Finset.univ.erase u)

/-- `b^{(v,out)}`: the coordinate price vector of the outside-terminal family of `v`. -/
noncomputable def outPrice (f : Fin m → Finset (Fin n) → ℝ) (v : Fin n) : Fin n → ℝ :=
  price (sumFn (outFamily f v)) (Finset.univ.erase v)

/-- Algorithm 1, line 7: the sampling weights `p_i = Σ_u s_i^{(u)} + Σ_v t_i^{(v)}`. -/
noncomputable def weights (f : Fin m → Finset (Fin n) → ℝ) (i : Fin m) : ℝ :=
  ∑ u, inShare f u i + ∑ v, outShare f v i

/-- The influence (25): `inf_S(w) = max_{v ∈ S̄} b^{(v,out)}(w)` for `w ∈ S` and
`max_{u ∈ S} b^{(u,in)}(w)` for `w ∈ S̄`, the maximum over the empty set being zero. -/
noncomputable def influence (f : Fin m → Finset (Fin n) → ℝ) (S : Finset (Fin n)) (w : Fin n) :
    ℝ :=
  if w ∈ S then finMax Sᶜ (fun v => outPrice f v w) else finMax S (fun u => inPrice f u w)

/-- The residual (24): `Δᵢ(S, U) = fᵢ(S) − f→ᵢ(S \ U, S̄ \ U)`. -/
noncomputable def residual (f : Fin m → Finset (Fin n) → ℝ) (i : Fin m)
    (S U : Finset (Fin n)) : ℝ :=
  f i S - blockMinCut (f i) (S \ U) (Sᶜ \ U)

/-- Algorithm 1, line 8: `Λ = 56 ε⁻² log(32n/δ)` (natural logarithm). -/
noncomputable def samplingScale (n : ℕ) (ε δ : ℝ) : ℝ :=
  56 * ε⁻¹ ^ 2 * Real.log (32 * (n : ℝ) / δ)

end SubmodSparsify


