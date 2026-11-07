-- Prove2me | Definitions.Def_UnionVolEst_alponaFixed
-- name    : UnionVolEst_alponaFixed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:03:32.974601+00:00
-- url     : https://prove2.me/theorems/0ad76511-9e79-468d-b91c-2a704a923849
-- title:
--   Fixed-intensity process ("$p\leftarrow q$")
-- statement:
--   The **fixed-intensity process** at intensity $q$ with fixed volume answers $\tilde V_1,\dots,\tilde V_M$ runs lines 5–9 and 13–15 of Algorithm 1 with $p$ held at $q$ and no halving: for each body in order it removes the stored points lying in $K_i$, draws $N_i\sim\mathrm{Pois}(\tilde V_i q)$ and adds $N_i$ samples from GenerateSamples on $K_i$. It returns the final multiset $X$.
--
--   It is the process "$p_{\mathrm{final}}\leftarrow 2^{-t}$" to which the proofs of Claims 14, 17 and 20 apply Lemmas 12–19.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), proofs of Claims 14, 17, 20, pp.22–27 (PDF pp.24–29)

import Mathlib
import Definitions.Def_UnionVolEst_poissonQuantile

namespace UnionVolEst

open Classical in
/-- The fixed-intensity process "`p ← q`" referred to in the proofs of Claims 14, 17 and 20
("`P[Fail_good : p_final ← 2^{−t}]`", Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), printed pp.23–26, PDF pp.25–28) and in Lemmas 12, 13,
15, 16, 18, 19: lines 5–9 and 13–15 of Algorithm 1 with the intensity held at `q` and no halving
(no lines 10–12). For each body in order, remove the stored points lying in `K_i`, draw
`Nᵢ = poissonQuantile (Ṽᵢ · q) (U i)` (a `Pois(Ṽᵢ q)` draw) and add the samples
`Z i 0, …, Z i (Nᵢ − 1)`. Returns the final multiset `X`.

**Formalization Note** The volume answers are a fixed vector `V` (the page conditions on an
accurate outcome of all volume queries, printed p.21). Bodies in the order of `Fin M`. -/
noncomputable def alponaFixed {n M : ℕ} {Ω : Type*} (q : ℝ)
    (K : Fin M → Set (EuclideanSpace ℝ (Fin n))) (V : Fin M → ℝ) (U : Fin M → Ω → ℝ)
    (Z : Fin M → ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    List (EuclideanSpace ℝ (Fin n)) :=
  (List.finRange M).foldl
    (fun X i => X.filter (fun x => decide (x ∉ K i)) ++
      (List.range (poissonQuantile (V i * q).toNNReal (U i ω))).map (fun j => Z i j ω))
    []

end UnionVolEst


