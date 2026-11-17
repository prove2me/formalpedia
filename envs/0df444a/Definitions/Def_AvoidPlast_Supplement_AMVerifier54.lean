-- Prove2me | Definitions.Def_AvoidPlast_Supplement_AMVerifier54
-- name    : AvoidPlast_Supplement_AMVerifier54
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:01:18.168941+00:00
-- url     : https://prove2.me/theorems/e7abb9e2-de45-4611-9558-904c12e4256c
-- title:
--   The AM verifier of Theorem 5.4
-- statement:
--   For a family $C$, $m$, $\delta<\varepsilon$, a time bound $T$, ensembles $X,Y$, a bound $p$, a language $L$ and $e\ge1$: there is a verifier $V$ reading $x$, a sample $y\sim Y_{T(n)^{1/\varepsilon}}$, uniform coins $\rho$, the prover's message $z$ of $\lceil T(n)^{\delta/\varepsilon}\rceil$ bits, and the oracle $C_{xy}$, where $y$ and $\rho$ are its persistent randomness (read-only, two-way, not counted as space), such that, with $N=n+T(n)^{1/\varepsilon}$:
--
--   1. $V$ runs in time $T^{O(1/\varepsilon)}$ (and $\rho$ has that length) and space $O(T^{\delta/\varepsilon})$;
--   2. there is one round: the challenge $(y,\rho)$, then the message $z$;
--   3. with probability at least $1-p(N)$ over $x\sim X_n$ and $(y,\rho)$, if $x\in L$ then some $z$ makes $V$ accept;
--   4. for every $x\notin L$, the probability over $(y,\rho)$ that some $z$ makes $V$ accept is at most $2^{-(\lg N)^e}$.
--
--   **Formalization Note** The source's verifier draws $y$ from uniform coins with the sampler of $Y$; here $y$ is given as part of the randomness. The sampler runs within the stated time and space, so a verifier of this form is a verifier of the source's form.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.4, items 1–4, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_lg
import Definitions.Def_AvoidPlast_workSpace
import Definitions.Def_AvoidPlast_Supplement_Ensemble
import Definitions.Def_AvoidPlast_Supplement_pr
import Definitions.Def_AvgPHETH_uniformDist
import Definitions.Def_AvoidPlast_Supplement_oracleTable
import Definitions.Def_AvoidPlast_Supplement_padExp

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The conclusion of Theorem 5.4 for `L` and a polylog exponent `e` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 5.4,
items 1–4, p.23). `V` has read-only tapes for the input `x`, the sample `y ∼ Y_{T(n)^{1/ε}}`,
its uniform random string `ρ`, the prover's message `z` of `⌈T(n)^{δ/ε}⌉` bits, and the oracle
`C_{xy}`; `y` and `ρ` are its persistent randomness and do not count as space. Then:

1. `V` runs in time `T^{O(1/ε)}` (`⌈a(T(n)^{a/ε} + 1)⌉`, also the length of `ρ`) and space
   `O(T^{δ/ε})`, querying `C_{xy}`;
2. one round: the challenge `(y, ρ)`, then the prover's message `z`;
3. with probability at least `1 - p(N)`, `N = n + T(n)^{1/ε}`, over `x ∼ X_n` and `(y, ρ)`, if
   `x ∈ L` then some `z` makes `V` accept;
4. every `x ∉ L` is accepted (for some `z`) with probability at most `2^{-(lg N)^e}`.

**Formalization Note** The sample `y` is given to `V` as part of its randomness. The source's
verifier draws it with the sampler of `Y` from uniform coins; the sampler runs within the stated
time and space, so a verifier of this form is a verifier of the source's form. -/
def AMVerifier54 (C : List Bool → List Bool → List Bool) (m : ℕ → ℕ) (δ ε : ℝ) (T : ℕ → ℕ)
    (X Y : Ensemble) (p : ℕ → ℝ) (L : Set (List Bool)) (e : ℝ) : Prop :=
  ∃ (V : Machine 5) (a : ℕ) (K : ℝ),
    let τ : ℕ → ℕ := fun n => ⌈(a : ℝ) * ((T n : ℝ) ^ ((a : ℝ) / ε) + 1)⌉₊
    let μ : ℕ → ℕ := fun n => ⌈(T n : ℝ) ^ (δ / ε)⌉₊
    let tbl : List Bool → List Bool := oracleTable C (ceilPow δ) m
    (∀ x y ρ z : List Bool, y.length = padExp T ε x.length → ρ.length = τ x.length →
      z.length = μ x.length →
      HaltsWithin V ![x, y, ρ, z, tbl (x ++ y)] (τ x.length) ∧
      (workSpace V ![x, y, ρ, z, tbl (x ++ y)] : ℝ) ≤ K * ((T x.length : ℝ) ^ (δ / ε) + 1)) ∧
    (∀ n : ℕ, 1 - p (n + padExp T ε n) ≤
      pr ((X.dist n).bind fun x => (Y.dist (padExp T ε n)).bind fun y =>
          (AvgPHETH.uniformDist (τ n)).map fun ρ => (x, y, ρ))
        fun t => t.1 ∈ L → ∃ z : List Bool, z.length = μ n ∧
          Accepts V ![t.1, t.2.1, t.2.2, z, tbl (t.1 ++ t.2.1)]) ∧
    ∀ x : List Bool, x ∉ L →
      pr ((Y.dist (padExp T ε x.length)).bind fun y => (AvgPHETH.uniformDist (τ x.length)).map fun ρ => (y, ρ))
        (fun t => ∃ z : List Bool, z.length = μ x.length ∧ Accepts V ![x, t.1, t.2, z, tbl (x ++ t.1)])
        ≤ (2 : ℝ) ^ (-(lg (x.length + padExp T ε x.length)) ^ e)

end AvoidPlast.Supplement


