-- Prove2me | Definitions.Def_DSDensity1246_Main_maximumDensity
-- name    : DSDensity1246_Main_maximumDensity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:11:53.945995+00:00
-- url     : https://prove2.me/theorems/912c24ba-2e47-4935-a9d9-7b7f6f4eec53
-- title:
--   Maximum list density over all samples and finite subfamilies
-- statement:
--   Let $X,Y$ be arbitrary sets, $H\subseteq Y^X$, $\ell\ge1$, and $n\in\mathbb N$. Collect all densities of finite nonempty families $W$ in every length-$n$ restriction of $H$, and define
--
--   $$\mu_H^\ell(n)=\sup\{\operatorname{Dens}^\ell(W):S\in X^n,\ \varnothing\ne W\subseteq H|_S,\ |W|<\infty\}.$$
--
--   The inner family is not required to be the entire restriction. This quantity is meaningful for infinite classes and infinite label spaces because each density is at most $n$.
--
--   **Formalization Note** The supremum is taken in the nonnegative reals and its empty value is zero. No boundedness hypothesis is added: the unconditional bound by $n$ is proved in the separate local verification module. Thus converting this supremum to a real number for the ceiling preserves its actual finite value. If there is no eligible sample or nonempty family, the maximum density is zero.
-- source:
--   Chirag Pabbaraju, STOC 2027 submission #1246 (October 2026), p. 14, Definition 6 and the observation immediately before it

import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_DSDensity1246_Main_listDensity

open scoped NNReal

namespace DSDensity1246.Main

/-- Definition 6, p. 14: every sample and every finite nonempty subfamily
of its restriction. This set is bounded above by n, independently of DS dimension. -/
def densityValues {X Y : Type*} (ℓ : ℕ) (H : Set (X → Y)) (n : ℕ) : Set ℝ≥0 :=
  {r | ∃ (S : Fin n → X) (W : Finset (Fin n → Y)),
    W.Nonempty ∧ (↑W : Set (Fin n → Y)) ⊆ MulticlassDS.Compress.proj H S ∧
      r = listDensity ℓ W}

/-- The nonnegative-real supremum; the empty supremum is zero.
Its unconditional bound by n is checked in the local verification module. -/
noncomputable def maximumDensity {X Y : Type*}
    (ℓ : ℕ) (H : Set (X → Y)) (n : ℕ) : ℝ≥0 :=
  sSup (densityValues ℓ H n)

end DSDensity1246.Main


