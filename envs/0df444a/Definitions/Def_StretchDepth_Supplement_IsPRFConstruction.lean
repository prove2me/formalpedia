-- Prove2me | Definitions.Def_StretchDepth_Supplement_IsPRFConstruction
-- name    : StretchDepth_Supplement_IsPRFConstruction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:10:24.024432+00:00
-- url     : https://prove2.me/theorems/28eaf8ca-ea0e-4336-be27-dcb32f16ba6c
-- title:
--   PRG-to-PRF constructions with nonadaptive security (Definition 4)
-- statement:
--   Let $N>n$, $k,\ell,q,d\ge1$, $1\le t\le2^\ell$ and $0<\gamma,\epsilon\le1$. A **fully black-box PRG-to-PRF construction with nonadaptive security and parameters $(q,t,\gamma,\epsilon,d)$** is a pair $(F,R)$ where:
--   1. $F:\{0,1\}^k\times\{0,1\}^\ell\to\{0,1\}$, $F^G_x(u):=F^G(x,u)$, is a $(q,d)$-construction from $G:\{0,1\}^n\to\{0,1\}^N$: each evaluation $F^G_x(u)$ makes at most $q$ queries to $G$ in at most $d$ adaptive rounds;
--   2. for each tuple $\bar u=(u_1,\dots,u_t)$ of **distinct** inputs in $\{0,1\}^\ell$, $R_{\bar u}$ is a randomized query procedure making at most $q$ queries in total to $G$ and to $T:\{0,1\}^t\to\{0,1\}$;
--   3. for all $\bar u$, $G$, $T$: $\mathrm{Adv}^{\mathrm{prf}}_{F^G}(\bar u,T)\ge\gamma\Rightarrow\mathrm{Adv}_G(R^{G,T}_{\bar u})\ge\epsilon$, where
--   $$
--   \mathrm{Adv}^{\mathrm{prf}}_{F^G}(\bar u,T)=\Big|\Pr_{x\sim U_k}\big[T(F^G_x(u_1)\cdots F^G_x(u_t))=1\big]-\Pr[T(U_t)=1]\Big|
--   $$
--   and $\mathrm{Adv}_G(D)=|\Pr[D(G(U_n))=1]-\Pr[D(U_N)=1]|$.
--
--   The definition models a black-box construction of a one-bit PRF from a PRG, with security against deterministic nonadaptive $t$-query distinguishers.
--
--   **Formalization Note** $F$ is a family of one-output-bit round trees, one per $(x,u)$, with the base `IsConstruction` bounds for each fixed $u$; $\bar u$ is an embedding $\mathrm{Fin}\,t\hookrightarrow\{0,1\}^\ell$; $R$ reuses the base mission's `QProc`, `WithinQueries` and `SAdv`. The parameter conditions are hypotheses of the theorems that use the predicate.
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), Definition 4, p.14 (PDF p.14)

import Definitions.Def_StretchDepth_IsPRGReduction

set_option autoImplicit false

namespace StretchDepth.Supplement

/-- `F^G_x(u) ∈ {0,1}`: bit `0` of the one-bit output of the tree `F x u` run against `G`. -/
def prfEval {n N k ℓ : ℕ} (F : Bits k → Bits ℓ → RoundTree n N 1) (G : Bits n → Bits N)
    (x : Bits k) (u : Bits ℓ) : Bool :=
  run G (F x u) 0

/-- Definition 4, p.14: the advantage of the deterministic nonadaptive `t`-query distinguisher
`(ū, T)`, with `ū` a tuple of distinct inputs:
`Adv^prf_{F^G}(ū, T) = |Pr_{x∼U_k}[T(F^G_x(u₁)⋯F^G_x(u_t)) = 1] − Pr[T(U_t) = 1]|`. -/
noncomputable def advPRF {n N k ℓ t : ℕ} (F : Bits k → Bits ℓ → RoundTree n N 1)
    (G : Bits n → Bits N) (u : Fin t ↪ Bits ℓ) (T : Bits t → Bool) : ℝ :=
  |((Finset.univ.filter fun x : Bits k => T (fun i => prfEval F G x (u i)) = true).card : ℝ) /
      2 ^ k -
    ((Finset.univ.filter fun z : Bits t => T z = true).card : ℝ) / 2 ^ t|

/-- **PRG-to-PRF construction with nonadaptive security, parameters `(q, t, γ, ϵ, d)`.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), Definition 4, p.14: "A fully black-box PRG-to-PRF construction with nonadaptive
security and parameters (q, t, γ, ϵ, d) is defined by a pair (F, R). The function F is a (q, d)
construction of the form F(·) : {0,1}^k × {0,1}^ℓ → {0,1}, F^G_x(u) := F^G(x, u), taking an oracle
G : {0,1}^n → {0,1}^N, so q bounds the number of queries to G per evaluation F^G_x(u). … The
reduction R^{G,T}_ū is a randomized query procedure making at most q queries in total to oracles
G : {0,1}^n → {0,1}^N, T : {0,1}^t → {0,1}, on every input and for every choice of its randomness.
Overall the construction must satisfy the following for all ū, G, T:
Adv^prf_{F^G}(ū, T) ≥ γ ⟹ Adv_G(R^{G,T}_ū) ≥ ϵ."

**Formalization Note.** `F x u` is a round tree with one output bit; the `(q, d)` bounds hold per
evaluation `(x, u)` and per real `G` (the base `IsConstruction` for each fixed `u`, which the page
says "extends in the obvious way"). A distinguisher's inputs are an embedding `Fin t ↪ {0,1}^ℓ`
(distinct inputs). The reduction for `ū` is the base mission's randomized query procedure
(`QProc n N t`, `T`-queries on `{0,1}^t`), with the base `WithinQueries` and `SAdv`
(`Adv_G = |SAdv_G|`). The conditions `N > n`, `k, ℓ, q, d ≥ 1`, `1 ≤ t ≤ 2^ℓ`, `0 < γ, ϵ ≤ 1` are
hypotheses of the theorems using this predicate. -/
def IsPRFConstruction {n N k ℓ t : ℕ} (F : Bits k → Bits ℓ → RoundTree n N 1)
    (R : (Fin t ↪ Bits ℓ) → PMF (Bits N → QProc n N t)) (q : ℕ) (γ ε : ℝ) (d : ℕ) : Prop :=
  (∀ u : Bits ℓ, IsConstruction (fun x => F x u) q d) ∧
    (∀ u : Fin t ↪ Bits ℓ, WithinQueries (R u) q) ∧
    ∀ (u : Fin t ↪ Bits ℓ) (G : Bits n → Bits N) (T : Bits t → Bool),
      γ ≤ advPRF F G u T → ε ≤ |SAdv (R u) G T|

end StretchDepth.Supplement


