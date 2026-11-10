-- Prove2me | Definitions.Def_SetDefinedGraphs_Functional
-- name    : SetDefinedGraphs_Functional
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:24:49.788057+00:00
-- url     : https://prove2.me/theorems/0b9eed65-a2f8-415f-a5ab-38dd13a925ec
-- title:
--   $(L,\lambda)$-functional and $L$-functional sets of vectors
-- statement:
--   Let $L\subsetneq[d]$, $\overline L=[d]\setminus L$ and $\lambda\in\overline L$. A set $U\subseteq\mathbb N^d$ is **$(L,\lambda)$-functional** if the coordinate $v_\lambda$ is determined by $v|_L$: there is $\varphi:\mathbb N^{L}\to\mathbb N$ with
--   $$v_\lambda=\varphi(v|_L)\qquad\text{for every }v\in U.$$
--   $U$ is **$L$-functional** if it is $(L,\lambda)$-functional for some $\lambda\in\overline L$, and **$(L_1,\dots,L_k)$-functional** if it is $L_s$-functional for every $s\in[k]$ (each with its own $\lambda_s$). These sets are the independent sets produced in the analysis of discrete DNFs.
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), §3.6 p.18 (PDF p.20): (L, λ)-functional, L-functional, (L1, …, Lk)-functional sets

import Mathlib

set_option autoImplicit false

namespace SetDefinedGraphs

/-- For `L ⊊ [d]` and `λ ∈ L̄ = [d] ∖ L`, a set `U ⊆ ℕ^d` is **`(L, λ)`-functional** (arXiv:2607.23754, §3.6, p.18) if
for every `v ∈ U` the value `v_λ` is determined by `v|_L`: there is `φ : ℕ^L → ℕ` with `v_λ = φ(v|_L)` for all `v ∈ U`. -/
def IsFunctionalAt {d : ℕ} (L : Finset (Fin d)) (lam : Fin d) (U : Set (Fin d → ℕ)) : Prop :=
  lam ∉ L ∧ ∃ φ : (L → ℕ) → ℕ, ∀ v ∈ U, v lam = φ (fun i => v i.1)

/-- A set `U ⊆ ℕ^d` is **`L`-functional** (for `L ⊊ [d]`, §3.6, p.18) if it is `(L, λ)`-functional for some
`λ ∈ L̄`. -/
def IsLFunctional {d : ℕ} (L : Finset (Fin d)) (U : Set (Fin d → ℕ)) : Prop :=
  L ≠ Finset.univ ∧ ∃ lam : Fin d, IsFunctionalAt L lam U

end SetDefinedGraphs


