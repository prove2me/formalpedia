-- Prove2me | Definitions.Def_SamplingAC0_hybrid
-- name    : SamplingAC0_hybrid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:46:30.5021+00:00
-- url     : https://prove2.me/theorems/153ef15c-eb54-4d52-a0c2-19f609b5afb5
-- title:
--   The hybrid input $U$ of $X$ and $Y$
-- statement:
--   Let $f$ be a forest with the output positions of $R$, $i\in[q]$, and $X,Y\in\{0,1\}^s$. Let $S$ be the set of bits queried on input $X$ by the $2k$ trees of $f$ that compute the point $g_i$. The **hybrid** $U$ of $X$ and $Y$ is
--
--   $$U_j=\begin{cases}X_j & j\in S,\\ Y_j & j\notin S.\end{cases}$$
--
--   For independent uniform $X,Y$ the hybrid is uniform and $g_i(U)=g_i(X)$; it is the coupling at the heart of the proof of Theorem 10.
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), §3.1, p.10

import Mathlib
import Definitions.Def_SamplingAC0_Forest
import Definitions.Def_SamplingAC0_lineDNF
set_option autoImplicit false

namespace SamplingAC0

/-- The input bits queried on input `X` by the `2k` trees of `f` that compute the point `g_i`. -/
def pointQueries {s k : ℕ} (f : Forest s (ROut k)) (i : Fin (2 ^ k)) (X : Fin s → Bool) :
    Finset (Fin s) :=
  (Finset.univ : Finset (Bool × Fin k)).biUnion
    (fun cj => queriedSet (f (Sum.inr (i, cj.1, cj.2))) X)

/-- **The hybrid input.** Riazanov–Viola, *Sampling Tools and the Power of AC0*, STOC 2027
submission (manuscript sha256 99c33d30…), §3.1, p.10: "Let us first take two independent inputs
X, Y ∼ {0, 1}^s and then represent U as a hybrid of these two inputs: for each j ∈ [s] if any of
the 2k trees computing g_i(X) queries j let U_j = X_j, otherwise let U_j = Y_j." -/
def hybrid {s k : ℕ} (f : Forest s (ROut k)) (i : Fin (2 ^ k)) (X Y : Fin s → Bool) :
    Fin s → Bool :=
  fun j => if j ∈ pointQueries f i X then X j else Y j

end SamplingAC0


