-- Prove2me | Definitions.Def_ConeL2G_glauberLap
-- name    : ConeL2G_glauberLap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:41:50.358692+00:00
-- url     : https://prove2.me/theorems/a170da25-4b36-4615-9e3d-21c2c8b84045
-- title:
--   The Laplacian $\frac1nD$ of the Glauber dynamics
-- statement:
--   For a graph $G$ on $n$ vertices with lists and $\mu$ uniform on proper list colorings, the Glauber dynamics picks a uniformly random vertex and resamples its color given all other colors; its transition matrix is $\frac1nP$ with $P=\sum_iP_i$, and its Laplacian is
--   $$\tfrac1nD=I-\tfrac1nP,\qquad D=\sum_i D_i,\ D_i=I-P_i .$$
--
--   "The spectral gap of the Glauber dynamics is at least $\varepsilon$" is the Poincaré inequality $\varepsilon\langle f,f\rangle_\mu\le\langle f,\tfrac1nDf\rangle_\mu$ for every $f$ with $\mathbb E_\mu f=0$ (the reused `SpinGirth5.PoincareIneq`).
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Section 1, pp.1–2

import Mathlib
import Definitions.Def_SpinGirth5_heatBath
import Definitions.Def_ConeL2G_unifMass

namespace ConeL2G

open Finset

/-- **The Laplacian of the Glauber dynamics** `(1/n)D = I − (1/n)P`. Li–Oveis Gharan,
arXiv:2610.37721, Section 1, pp.1–2: "Let `(1/n)P` be the transition probability matrix of the
Glauber dynamics … the second smallest eigenvalue of the Laplacian matrix `(1/n)D = I − (1/n)P`",
with `P = Σᵢ Pᵢ`, `Dᵢ = I − Pᵢ`, `D = Σᵢ Dᵢ` (p.2).

Here `n = |V|`, `µ = unifMass H L`, and `D = SpinGirth5.lapSum µ univ`. "The spectral gap of the
Glauber dynamics is at least `ε`" is `SpinGirth5.PoincareIneq (unifMass H L) (glauberLap H L) ε`
(the Poincaré form `ε⟨f, f⟩_µ ≤ ⟨f, (1/n)Df⟩_µ` for every `f ⊥ 1`). -/
noncomputable def glauberLap {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {K : ℕ} (L : V → Finset (Fin K)) (f : (V → Fin K) → ℝ)
    (x : V → Fin K) : ℝ :=
  (1 / (Fintype.card V : ℝ)) * SpinGirth5.lapSum (unifMass H L) univ f x

end ConeL2G


