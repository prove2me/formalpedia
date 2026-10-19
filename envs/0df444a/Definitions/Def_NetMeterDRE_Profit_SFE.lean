-- Prove2me | Definitions.Def_NetMeterDRE_Profit_SFE
-- name    : NetMeterDRE_Profit_SFE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:01.826711+00:00
-- url     : https://prove2.me/theorems/c205842e-56e8-4d23-ac70-c02ff5d0ecb6
-- title:
--   §2, p. 8, Definition 1; Appendix B, p. ec3, (1), (EC.2), (EC.8) — wholesale market clearing, supply function equilibrium, the symmetric supply S(p) and α
-- statement:
--   The wholesale electricity market of Sunar and Swaminathan has $N$ power generators, indexed by $n = 1,\dots,N$. Each generator submits a **supply function** $S_n : \mathbb R \to \mathbb R$, and producing the quantity $q$ costs it $c q^2$ for a constant $c$.
--
--   1. **Profit (EC.2).** A generator that produces $q$ at the market price $p$ earns
--   $$\pi(q,p) = q\,p - c\,q^2 .$$
--   2. **Market clearing (1).** For a realized net wholesale demand $\epsilon \in \mathbb R$, a price $p$ clears the market under the profile $S = (S_1,\dots,S_N)$ when
--   $$\sum_{n=1}^N S_n(p) = \epsilon .$$
--   3. **Supply function equilibrium (Definition 1).** A profile $S$ is a supply function equilibrium if for every generator $n$ and every realization $\epsilon$: whenever $p$ clears the market under $S$, then for every alternative supply function $S'$ of generator $n$ and every price $p'$ that clears the market under the profile in which $S_n$ is replaced by $S'$ (the others unchanged),
--   $$\pi\big(S'(p'),p'\big) \le \pi\big(S_n(p),p\big).$$
--   The equilibrium is ex post: the inequality must hold for every realization $\epsilon$ of the demand.
--   4. **The symmetric supply function** exhibited in the proof of Proposition 1,
--   $$S(p) = \frac{(N-2)\,p}{(N-1)\,2c},$$
--   and the constant (EC.8)
--   $$\alpha = \frac{2c(N-1)}{(N-2)N}.$$
--
--   These objects describe the generators' side of the paper's model; the paper's later results use the market-clearing price of the symmetric equilibrium, whose slope in the demand is $\alpha$.
--
--   **Formalization Note** Generators are indexed by `Fin N`. A deviation $S'$ under which no price clears the market places no constraint in Definition 1 (the deviator cannot reach such an outcome); when several prices clear, the inequality is required at every one of them. At a clearing price the generator's output $S_n(p)$ equals its residual demand $\epsilon - \sum_{k\ne n} S_k(p)$, which is how (EC.2) is written in the paper.
-- source:
--   Sunar & Swaminathan, Net-metered distributed renewable energy: A peril for utilities?, SSRN 3257925 (version of September 2019), pp. 7–8 (PDF 7–8), §2, (1), Definition 1, (3); p. ec3 (PDF 35), (EC.2) and S(p); p. ec4 (PDF 36), (EC.8)

import Mathlib

namespace NetMeterDRE.Profit

/-! # The wholesale electricity market (Sunar & Swaminathan, SSRN 3257925, §2, pp. 7–8,
Definition 1; Appendix B, p. ec3)

`N` power generators, indexed by `Fin N`, each with production cost `c q²`, submit supply
functions `S n : ℝ → ℝ`. The market clears at a price `p` with `∑ n, S n p = ε`, where `ε` is
the realized net wholesale demand (1). -/

/-- (EC.2): the ex-post profit of a generator that produces `q` at the market price `p`,
with production cost `c q²`: revenue `q p` minus cost `c q²`. -/
def genProfit (c q p : ℝ) : ℝ := q * p - c * q ^ 2

/-- (1): the price `p` clears the market for the realized net demand `ε` under the supply
function profile `S`, i.e. `∑ₙ Sₙ(p) = ε`. -/
def IsClearing {N : ℕ} (S : Fin N → ℝ → ℝ) (ε p : ℝ) : Prop := ∑ n, S n p = ε

/-- Definition 1 (supply function equilibrium), for generators with cost `c q²`: for every
generator `n` and every realization `ε` of the net demand, if `p` clears the market under the
profile `S`, then no unilateral deviation `S'` of generator `n` gives it a larger profit at any
price `p'` that clears the market under the deviated profile. A deviation for which no price
clears is an outcome the deviator cannot reach and is not constrained. -/
def IsSFE (N : ℕ) (c : ℝ) (S : Fin N → ℝ → ℝ) : Prop :=
  ∀ (n : Fin N) (ε p : ℝ), IsClearing S ε p →
    ∀ (S' : ℝ → ℝ) (p' : ℝ), IsClearing (Function.update S n S') ε p' →
      genProfit c (S' p') p' ≤ genProfit c (S n p) p

/-- The symmetric supply function exhibited in the proof of Proposition 1 (p. ec3):
`S(p) = (N − 2) p / ((N − 1) 2c)`. -/
noncomputable def symSupply (N : ℕ) (c p : ℝ) : ℝ :=
  ((N : ℝ) - 2) * p / (((N : ℝ) - 1) * (2 * c))

/-- (EC.8): `α = 2c(N − 1) / ((N − 2) N)`. -/
noncomputable def alpha (N : ℕ) (c : ℝ) : ℝ :=
  2 * c * ((N : ℝ) - 1) / (((N : ℝ) - 2) * (N : ℝ))

end NetMeterDRE.Profit


