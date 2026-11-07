-- Prove2me | Definitions.Def_TargetedSamplers_rejOracleClass
-- name    : TargetedSamplers_rejOracleClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:04:09.719601+00:00
-- url     : https://prove2.me/theorems/64f926a0-171d-4077-863b-7a739c2e9d98
-- title:
--   The oracle class $\mathcal D$ of Proposition 4.26
-- statement:
--   $\mathcal D_Q$ is the class of Boolean oracles $D$ that reject (answer $0$) at most $Q(m)$ strings of each length $m$: $|D^{-1}(0)\cap\{0,1\}^m|\le Q(m)$ for every $m$.
--
--   **Formalization Note** Proposition 4.26 takes $D:\{0,1\}^m\to\{0,1\}$ with $|D^{-1}(0)|\le Q(m)$ for the block length $m$. An oracle here answers on all strings and the bound is imposed on every length. This class contains every such $D$, extended by $1$ on the other lengths.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Proposition 4.26, p.36 (pdf p.38)

import Mathlib

namespace TargetedSamplers

/-- The oracle class `D` of Proposition 4.26 (Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027
submission, manuscript sha256 599d0a59…, p.36): Boolean oracles `D` that reject (answer `0`) at most
`Q(m)` strings of each length `m`.

**Formalization Note** The page takes `D : {0,1}^m → {0,1}` with `|D^{−1}(0)| ≤ Q(m)` for the block
length `m`. An oracle here answers on all bit strings; the bound is imposed on every length, which
contains every such `D` (extended by `1` on the other lengths). -/
def rejOracleClass (Q : ℕ → ℕ) (O : List Bool → ℕ) : Prop :=
  (∀ z, O z ≤ 1) ∧
    ∀ L : ℕ, (Finset.univ.filter (fun z : Fin L → Bool => O (List.ofFn z) = 0)).card ≤ Q L

end TargetedSamplers


