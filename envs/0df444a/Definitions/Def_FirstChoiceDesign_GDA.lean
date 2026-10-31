-- Prove2me | Definitions.Def_FirstChoiceDesign_GDA
-- name    : FirstChoiceDesign_GDA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:13.838891+00:00
-- url     : https://prove2.me/theorems/b68b0540-7b12-474e-bef6-744ad8bcbef0
-- title:
--   Generalized deferred acceptance mechanisms: regime, $f^\varphi$, $g^\varphi$, modified priority
-- statement:
--   A **generalized deferred acceptance (gDA) mechanism** $\varphi$ (Definition 1) draws lottery numbers under its regime, computes for each student $i$ and school $s$ the **modified priority**
--
--   $$
--   \rho^\varphi_{is}=f^\varphi(\rho_{is})+g^\varphi(\mathrm{rank}_{is}),
--   $$
--
--   where $f^\varphi$ is strictly increasing and $g^\varphi$ is weakly increasing, and runs DA with the strict school orders given by $\rho^\varphi_{is}+r_{is}$. The regime is STB (a single tie breaker: one number per student, used by all schools) or MTB (a multiple tie breaker: an independent number per student and school). The mechanism is parametrized by the regime and $(f^\varphi,g^\varphi)$. The DA mechanism is $f^\varphi(m)=m$, $g^\varphi(n)=0$, and the Boston mechanism is $f^\varphi(m)=m$, $g^\varphi(n)=(K+1)n$.
--
--   **Formalization Note** `K n`, `f n`, `g n` are the values used in markets with `n` students, because the source lets $K$ change with $|I|$ and Boston's $g$ depends on $K$. A mechanism with one $K$, $f$, $g$ is the case of functions constant in the student count. $f$ and $g$ are monotone on the positive integers, and their codomain contains $0$, as the DA mechanism needs. `Regime` and `GDA.modified` are in this module.
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Definition 1, pp.7–8

import Definitions.Def_FirstChoiceDesign_Setting

namespace FirstChoiceDesign

/-- The two lottery regimes of pp.6–7: a single tie breaker (one number per student, used by all
schools) and a multiple tie breaker (an independent number per student and school). -/
inductive Regime
  | STB
  | MTB

/-- A generalized deferred acceptance mechanism, Definition 1, pp.7–8, by its parameters: "gDA
mechanisms are parametrized by the lottery regime (STB or MTB) and the priority modification
function `(f^φ, g^φ)`" (p.8), together with the number of priority statuses.

**Formalization Note** `K n`, `f n`, `g n` are the values for markets with `n` students. P.6 lets
`K` change with `|I|`, and Boston's `g(n) = (K + 1)n` depends on `K`, so the parameters have to be
allowed to change too. A mechanism with a single `K`, `f`, `g` is the case of functions constant in
the student count. `f n`, `g n` are monotone on the positive integers, where the page's `ℕ` lives;
their codomain contains `0`, because the DA mechanism is `g(n) = 0` (p.8). -/
structure GDA where
  regime : Regime
  /-- Priorities in a market with `n` students lie in `{1, …, K n}`. -/
  K : ℕ → ℕ
  f : ℕ → ℕ → ℕ
  g : ℕ → ℕ → ℕ
  f_strictMono : ∀ n, StrictMonoOn (f n) (Set.Ici 1)
  g_monotone : ∀ n, MonotoneOn (g n) (Set.Ici 1)

/-- The modified priority `ρ^φ_is = f^φ(ρ_is) + g^φ(rank_is)`, Definition 1(2), p.7, computed from
any (true or reported) priorities `ρ`. -/
def GDA.modified {n m : ℕ} (φ : GDA) (B : Setting n m) (ρ : Fin n → Fin m → ℕ) (i : Fin n)
    (s : Fin m) : ℕ :=
  φ.f n (ρ i s) + φ.g n (B.rank i s)

end FirstChoiceDesign


