-- Prove2me | Definitions.Def_ConeL2G_projPi
-- name    : ConeL2G_projPi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:43:01.66124+00:00
-- url     : https://prove2.me/theorems/67f23c94-18b5-47dc-8383-60a4f314caac
-- title:
--   The rank-one projection $\Pi_{i,c}$
-- statement:
--   For $h\in L^2(\mu_H)$,
--   $$(\Pi_{i,c}h)(x)=\begin{cases}e_{i,c}(x)\,\mathbb E_\mu\big[h(X)e_{i,c}(X)\mid X_{-i}=x_{-i}\big], & c\in L_i^{-x_{N_H(i)}},\\ 0,&\text{otherwise,}\end{cases}$$
--   the orthogonal projection onto $e_{i,c}$ within the fiber of $x_{-i}$. The conditional expectation is the reused heat-bath operator `SpinGirth5.heatBath` of $\mu_H$ at $i$.
--
--   These operators give the rank-one decomposition of $D_i$ (Fact 2.2) on which the pairwise local inequalities of the paper are built.
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Section 2.1, p.8

import Mathlib
import Definitions.Def_SpinGirth5_heatBath
import Definitions.Def_ConeL2G_unifMass
import Definitions.Def_ConeL2G_eVec

namespace ConeL2G

/-- **The rank-one projection** `Π_{i,c}` onto `e_{i,c}`. Li–Oveis Gharan, arXiv:2610.37721,
Section 2.1, p.8: "we let `Π_{i,c}` be the orthogonal projection onto `e_{i,c}`, when
`c ∈ L_i^{−x_{N_H(i)}}` and 0 otherwise. In particular, for any `h ∈ L²(µ)`
`(Π_{i,c}h)(x) := e_{i,c}(x) E_µ[h(X)e_{i,c}(X) | X_{−i} = x_{−i}]` if `c ∈ L_i^{−x_{N_H(i)}}`,
`0` otherwise."

The conditional expectation given `X_{−i} = x_{−i}` under `µ = µ_H` is the reused heat-bath
operator `SpinGirth5.heatBath (unifMass H L) i`.

**Formalization Note.** Functions are on all of `V → Fin K`; the identities of the paper hold on
`Ω_H` (off `Ω_H` the conditional expectation is Lean's junk value `0/0 = 0`). -/
noncomputable def projPi {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {K : ℕ} (L : V → Finset (Fin K)) (i : V) (c : Fin K)
    (h : (V → Fin K) → ℝ) (x : V → Fin K) : ℝ :=
  if c ∈ avail H L i x then
    eVec H L i c x * SpinGirth5.heatBath (unifMass H L) i (fun y => h y * eVec H L i c y) x
  else 0

end ConeL2G


